#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
"""Find duplicate non-private Lean declaration names.

The source lexer is shared with ``check_axioms.py`` so one-line namespace
openings and masked comments/strings are handled consistently.  This checker
does not elaborate Lean: it is a cheap source-level guard against a duplicate
qualified name that can be hidden by a stale olean in a per-file build.

Two theorems with the same statement are reported unless one of them is a
direct restatement of the other: its whole proof is ``by exact`` (or the bare
term) naming the other declaration, possibly applied to plain arguments.  The
main theorem statements are restated this way from the modules that prove
them.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import re
import subprocess
import sys


SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import check_axioms  # noqa: E402


@dataclass(frozen=True)
class DeclarationLocation:
    name: str
    path: str
    line: int


@dataclass(frozen=True)
class Duplicate:
    name: str
    first: DeclarationLocation
    second: DeclarationLocation


@dataclass(frozen=True)
class StatementDuplicate:
    statement: str
    first: DeclarationLocation
    second: DeclarationLocation


def tracked_lean_files(root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--", "*.lean"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        values = result.stdout.splitlines()
    else:
        # git archive checkouts intentionally have no .git directory.  Every
        # Lean file in such a tree is part of the archived source universe.
        values = [
            path.relative_to(root).as_posix()
            for path in root.rglob("*.lean")
            if path.is_file() and ".git" not in path.parts and ".lake" not in path.parts
        ]
    # The comparator Challenge and Solution are separate environments that are never imported
    # together; they repeat each other's definitions by design (leanprover/comparator model).
    values = [value for value in values if not value.startswith("comparators/")]
    return [
        (root / value).resolve()
        for value in values
        if value.endswith(".lean") and (root / value).is_file()
    ]


def relative_path(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return str(path.resolve())


def top_level_declarations(root: Path, path: Path) -> list[DeclarationLocation]:
    """Return declarations whose command starts at the Lean top level.

    A tactic-local ``def`` or a local binder must never become a purported
    module declaration.  Lean's project files put namespace-level declarations
    at column zero, including declarations inside an already-open namespace,
    so require that shape here while using check_axioms' comment/string mask
    and namespace lexer.
    """
    masked = check_axioms.code_mask(path.read_text(encoding="utf-8"))
    namespaces: list[str] = []
    blocks: list[tuple[str, int]] = []
    result: list[DeclarationLocation] = []
    for line_number, line in enumerate(masked.splitlines(), start=1):
        events: list[tuple[int, str, object]] = []
        events.extend((match.start(), "namespace", match) for match in check_axioms.NAMESPACE.finditer(line))
        events.extend((match.start(), "section", match) for match in check_axioms.SECTION.finditer(line))
        if line == line.lstrip():
            end = check_axioms.END.match(line)
            if end is not None:
                events.append((end.start(), "end", end))
            declaration = check_axioms.DECL.match(line)
            if declaration is not None:
                events.append((declaration.start(), "declaration", declaration))
        for _position, kind, match in sorted(events, key=lambda item: item[0]):
            if kind == "namespace":
                parts = match.group(1).split(".")
                namespaces.extend(parts)
                blocks.append(("namespace", len(parts)))
            elif kind == "section":
                blocks.append(("section", 0))
            elif kind == "end":
                if blocks:
                    block, count = blocks.pop()
                    if block == "namespace" and count:
                        del namespaces[-count:]
            else:
                modifier, _declaration_kind, name = match.groups()
                if modifier not in {"private", "local"} and name is not None:
                    qualified = (name.removeprefix("_root_.") if name.startswith("_root_.")
                                 else ".".join([*namespaces, *name.split(".")]))
                    result.append(
                        DeclarationLocation(
                            qualified,
                            relative_path(root, path),
                            line_number,
                        )
                    )
    return result


def selected_files(root: Path, given: list[Path] | None = None) -> list[Path]:
    values = tracked_lean_files(root) if given is None else [*tracked_lean_files(root), *given]
    result: list[Path] = []
    seen: set[Path] = set()
    for value in values:
        path = value.resolve()
        if path.suffix != ".lean" or not path.is_file() or path in seen:
            continue
        seen.add(path)
        result.append(path)
    return sorted(result, key=lambda path: relative_path(root, path))


def find_duplicates(root: Path, given: list[Path] | None = None) -> list[Duplicate]:
    locations: dict[str, list[DeclarationLocation]] = {}
    for path in selected_files(root, given):
        for location in top_level_declarations(root, path):
            locations.setdefault(location.name, []).append(location)
    duplicates: list[Duplicate] = []
    for name, values in locations.items():
        for first, second in combinations(values, 2):
            duplicates.append(Duplicate(name, first, second))
    return sorted(
        duplicates,
        key=lambda duplicate: (
            duplicate.name,
            duplicate.first.path,
            duplicate.first.line,
            duplicate.second.path,
            duplicate.second.line,
        ),
    )


def theorem_statements(root: Path, path: Path) -> list[tuple[str, DeclarationLocation]]:
    """Read top-level theorem/lemma types, with declaration names removed."""
    masked = check_axioms.code_mask(path.read_text(encoding="utf-8"))
    result: list[tuple[str, DeclarationLocation]] = []
    offset = 0
    for line_number, line in enumerate(masked.splitlines(keepends=True), start=1):
        match = check_axioms.DECL.match(line) if not line[:1].isspace() else None
        if not match or match.group(2) not in {"theorem", "lemma"} or not match.group(3):
            offset += len(line)
            continue
        cursor = offset + match.end()
        depth = 0
        pending_binders = 0
        stop = len(masked)
        for index in range(cursor, len(masked) - 1):
            char = masked[index]
            if char in "({[⦃":
                depth += 1
            elif char in ")}]⦄":
                depth = max(0, depth - 1)
            elif (depth == 0 and masked.startswith(("let ", "have "), index)
                  and (index == 0 or not (masked[index - 1].isalnum() or masked[index - 1] in "_.'"))):
                # A `let`/`have` inside the statement binds with its own `:=`.
                pending_binders += 1
            elif char == ":" and masked[index + 1] == "=" and depth == 0:
                if pending_binders:
                    pending_binders -= 1
                    continue
                stop = index
                break
        statement = " ".join(masked[cursor:stop].split())
        if statement:
            result.append((statement, DeclarationLocation(
                match.group(3), relative_path(root, path), line_number
            )))
        offset += len(line)
    return result


COMMAND_START = re.compile(
    r"^(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|end|"
    r"module|public|meta|namespace|section|open|variable|set_option|noncomputable|private|protected|"
    r"attribute|example|universe|alias|export)(?![\w'])|^(?:@\[|#)"
)
# `by exact NAME`, or the bare term NAME, optionally applied to plain arguments.
DIRECT_PROOF = re.compile(r"^(?:by\s+exact\s+)?@?([\w'.]+)(?:\s+[^\s()]+)*$")


def theorem_proof(path: Path, line_number: int) -> str:
    """Return the masked proof text of the theorem declared at ``line_number``.

    The proof runs from the ``:=`` that ends the statement to the next
    top-level command.  Comments are masked, so comments between the
    statement and the proof do not matter.
    """
    masked = check_axioms.code_mask(path.read_text(encoding="utf-8"))
    lines = masked.splitlines(keepends=True)
    start = sum(len(line) for line in lines[: line_number - 1])
    depth = 0
    pending_binders = 0
    stop = None
    for index in range(start + 1, len(masked) - 1):
        char = masked[index]
        if char in "({[⦃":
            depth += 1
        elif char in ")}]⦄":
            depth = max(0, depth - 1)
        elif (depth == 0 and masked.startswith(("let ", "have "), index)
              and not (masked[index - 1].isalnum() or masked[index - 1] in "_.'")):
            pending_binders += 1
        elif char == ":" and masked[index + 1] == "=" and depth == 0:
            if pending_binders:
                pending_binders -= 1
                continue
            stop = index + 2
            break
    if stop is None:
        return ""
    rest = masked[stop:]
    first_break = rest.find("\n")
    body = [rest if first_break == -1 else rest[: first_break + 1]]
    if first_break != -1:
        for line in rest[first_break + 1 :].splitlines(keepends=True):
            if COMMAND_START.match(line):
                break
            body.append(line)
    return " ".join("".join(body).split())


def is_direct_restatement(root: Path, proof_of: DeclarationLocation, target: str) -> bool:
    """Whether ``proof_of``'s proof is exactly the qualified declaration ``target``."""
    proof = theorem_proof(root / proof_of.path, proof_of.line)
    match = DIRECT_PROOF.match(proof)
    return match is not None and match.group(1).lstrip("@") == target


def qualified_name(root: Path, location: DeclarationLocation) -> str | None:
    for declaration in top_level_declarations(root, root / location.path):
        if declaration.line == location.line:
            return declaration.name
    return None


def is_restatement_pair(root: Path, first: DeclarationLocation, second: DeclarationLocation) -> bool:
    first_name = qualified_name(root, first)
    second_name = qualified_name(root, second)
    if first_name is None or second_name is None:
        return False
    return (is_direct_restatement(root, first, second_name)
            or is_direct_restatement(root, second, first_name))


def find_duplicate_statements(root: Path, given: list[Path] | None = None) -> list[StatementDuplicate]:
    locations: dict[str, list[DeclarationLocation]] = {}
    for path in selected_files(root, given):
        if relative_path(root, path).startswith("comparators/"):
            continue
        for statement, location in theorem_statements(root, path):
            locations.setdefault(statement, []).append(location)
    duplicates: list[StatementDuplicate] = []
    for statement, values in locations.items():
        for first, second in combinations(values, 2):
            if is_restatement_pair(root, first, second):
                continue
            duplicates.append(StatementDuplicate(statement, first, second))
    return sorted(
        duplicates,
        key=lambda item: (item.first.path, item.first.line, item.second.path, item.second.line),
    )


def format_duplicate(duplicate: Duplicate) -> str:
    return (
        f"{duplicate.name}: {duplicate.first.path}:{duplicate.first.line} "
        f"<-> {duplicate.second.path}:{duplicate.second.line}"
    )


def format_statement_duplicate(duplicate: StatementDuplicate) -> str:
    excerpt = duplicate.statement[:160]
    if len(duplicate.statement) > 160:
        excerpt += "…"
    return (
        f"{duplicate.first.path}:{duplicate.first.line} <-> "
        f"{duplicate.second.path}:{duplicate.second.line}: {excerpt}"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path, metavar="LEAN_FILE")
    parser.add_argument("--root", type=Path, default=SCRIPTS.parent)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    given: list[Path] | None = None
    if args.files:
        given = []
        for value in args.files:
            path = value if value.is_absolute() else root / value
            if path.suffix != ".lean" or not path.is_file():
                print(f"dup_decls: missing Lean file {value}", file=sys.stderr)
                return 2
            # Comparator files repeat each other by design, as in tracked_lean_files.
            if path.resolve().relative_to(root).as_posix().startswith("comparators/"):
                continue
            given.append(path)
    duplicates = find_duplicates(root, given)
    duplicate_statements = find_duplicate_statements(root, given)
    count = len(selected_files(root, given))
    if duplicates or duplicate_statements:
        print(
            f"DUP-DECLS FAIL: {len(duplicates)} duplicate name pair(s), "
            f"{len(duplicate_statements)} duplicate statement pair(s) in {count} file(s)"
        )
        for duplicate in duplicates:
            print(f"- duplicate declaration: {format_duplicate(duplicate)}")
        for duplicate in duplicate_statements:
            print(f"- duplicate theorem statement: {format_statement_duplicate(duplicate)}")
        return 1
    print(f"DUP-DECLS PASS: checked {count} Lean file(s), no duplicate names or theorem statements")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
