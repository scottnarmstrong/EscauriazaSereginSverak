#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
"""Inventory project ``def ... : Prop`` interfaces and their witnesses."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys


SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import check_axioms  # noqa: E402


PROP_TYPE = re.compile(r"^\s*\(?\s*Prop\b")
TRIVIAL_MARKER = re.compile(r"\b(?:trivial|zero)\b|=>\s*\(?\s*0\b|\b0\b")


@dataclass(frozen=True)
class Declaration:
    name: str
    local_name: str
    kind: str
    path: str
    line: int
    namespace: str
    private: bool
    header: str
    body: str
    binders: str
    result_type: str


@dataclass(frozen=True)
class PropInterface:
    declaration: Declaration
    nullary: bool


@dataclass(frozen=True)
class PropAnalysis:
    interface: PropInterface
    status: str
    instantiator: Declaration | None
    hypothesis_users: tuple[Declaration, ...]


@dataclass(frozen=True)
class PolicyIssue:
    interface: PropInterface
    reason: str


def _line_events(
    text: str, root: Path, relative: str
) -> list[tuple[int, str, str, bool, str]]:
    masked = check_axioms.code_mask(text)
    namespaces: list[str] = []
    blocks: list[tuple[str, int]] = []
    starts: list[tuple[int, str, str, bool, str]] = []
    offset = 0
    for line_number, line in enumerate(masked.splitlines(keepends=True), start=1):
        content = line.rstrip("\n")
        events: list[tuple[int, str, re.Match[str]]] = []
        events.extend((m.start(), "namespace", m) for m in check_axioms.NAMESPACE.finditer(content))
        events.extend((m.start(), "section", m) for m in check_axioms.SECTION.finditer(content))
        if content == content.lstrip():
            ending = check_axioms.END.match(content)
            if ending is not None:
                events.append((ending.start(), "end", ending))
            declaration = check_axioms.DECL.match(content)
            if declaration is not None:
                events.append((declaration.start(), "declaration", declaration))
        for position, kind, match in sorted(events, key=lambda event: event[0]):
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
                modifier, declaration_kind, local_name = match.groups()
                if local_name is None and declaration_kind != "instance":
                    continue
                qualified = (
                    ".".join([*namespaces, *local_name.split(".")])
                    if local_name is not None
                    else f"{'.'.join(namespaces)}.<instance@{line_number}>"
                )
                starts.append(
                    (
                        offset + position,
                        qualified,
                        declaration_kind,
                        modifier in {"private", "local"},
                        ".".join(namespaces),
                    )
                )
        offset += len(line)
    return starts


def _signature_parts(header: str) -> tuple[str, str] | None:
    masked = _registry_code_mask(header)
    declaration = check_axioms.DECL.match(masked)
    if declaration is None or declaration.group(3) is None:
        # Anonymous instances have no declaration name, but their target can
        # still be inspected separately by their source header.
        if declaration is None or declaration.group(2) != "instance":
            return None
        start = declaration.end()
    else:
        start = declaration.end(3)
    paren = brace = bracket = angle = 0
    for index in range(start, len(masked)):
        char = masked[index]
        if char == "(":
            paren += 1
        elif char == ")":
            paren = max(0, paren - 1)
        elif char == "{":
            brace += 1
        elif char == "}":
            brace = max(0, brace - 1)
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket = max(0, bracket - 1)
        elif char == "⦃":
            angle += 1
        elif char == "⦄":
            angle = max(0, angle - 1)
        elif char == ":" and paren == brace == bracket == angle == 0:
            return masked[start:index].strip(), masked[index + 1 :].strip()
    return None


def _registry_code_mask(text: str) -> str:
    """Mask comments and literals without hiding big-operator notation.

    Lean's big-operator notation uses a postfix apostrophe in `∑'` and `∏'`.
    The shared source mask treats an apostrophe after a non-ASCII operator as
    the start of a character literal, so a declaration containing a tsum can
    lose its proof delimiter and everything after it.  Replace only those
    notation markers with an equal-length space before applying the shared
    comment/literal mask.
    """
    normalized = re.sub(r"([∑∏])'", r"\1 ", text)
    return check_axioms.code_mask(normalized)


def _top_level_assignment(text: str, start: int, limit: int) -> int:
    """Find the declaration body separator outside delimiter groups."""
    paren = brace = bracket = angle = 0
    index = start
    while index < limit:
        char = text[index]
        if char == "(":
            paren += 1
        elif char == ")":
            paren = max(0, paren - 1)
        elif char == "{":
            brace += 1
        elif char == "}":
            brace = max(0, brace - 1)
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket = max(0, bracket - 1)
        elif char == "⦃":
            angle += 1
        elif char == "⦄":
            angle = max(0, angle - 1)
        if paren == brace == bracket == angle == 0 and text.startswith(":=", index):
            return index
        index += 1
    return -1


def declarations_from_text(root: Path, relative: str, text: str) -> list[Declaration]:
    masked = _registry_code_mask(text)
    starts = _line_events(masked, root, relative)
    declarations: list[Declaration] = []
    for index, (start, name, kind, private, namespace) in enumerate(starts):
        limit = starts[index + 1][0] if index + 1 < len(starts) else len(masked)
        body_sep = _top_level_assignment(masked, start, limit)
        header_end = body_sep if body_sep >= 0 else limit
        header = masked[start:header_end]
        body = masked[body_sep + 2 : limit] if body_sep >= 0 else ""
        parts = _signature_parts(header)
        if parts is None:
            binders, result_type = "", ""
        else:
            binders, result_type = parts
        line = masked.count("\n", 0, start) + 1
        declarations.append(
            Declaration(
                name=name,
                local_name=name.rsplit(".", 1)[-1],
                kind=kind,
                path=relative,
                line=line,
                namespace=namespace,
                private=private,
                header=header,
                body=body,
                binders=binders,
                result_type=result_type,
            )
        )
    return declarations


def project_lean_files(root: Path) -> list[str]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        paths = {
            value
            for value in result.stdout.decode().split("\0")
            if value.endswith(".lean") and value
        }
    else:
        paths = {
            path.relative_to(root).as_posix()
            for path in root.rglob("*.lean")
            if path.is_file() and ".git" not in path.parts and ".lake" not in path.parts
        }
    if (root / "ESS.lean").is_file():
        paths.add("ESS.lean")
    return sorted(paths)


def scan_paths(root: Path, paths: list[str]) -> list[Declaration]:
    declarations: list[Declaration] = []
    for relative in paths:
        path = root / relative
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        declarations.extend(declarations_from_text(root, relative, text))
    return declarations


def prop_interfaces(declarations: list[Declaration]) -> list[PropInterface]:
    result: list[PropInterface] = []
    for declaration in declarations:
        if declaration.kind != "def" or not declaration.result_type:
            continue
        if PROP_TYPE.match(declaration.result_type):
            result.append(
                PropInterface(
                    declaration=declaration,
                    nullary=not declaration.binders,
                )
            )
    return sorted(result, key=lambda item: (item.declaration.name, item.declaration.path))


def _strip_outer_parens(expression: str) -> str:
    value = expression.strip()
    while value.startswith("("):
        depth = 0
        closes_at = None
        for index, char in enumerate(value):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closes_at = index
                    break
        if closes_at != len(value) - 1:
            break
        value = value[1:-1].strip()
    return value


def _top_level_splits(expression: str, tokens: tuple[str, ...]) -> list[tuple[int, int]]:
    splits: list[tuple[int, int]] = []
    paren = brace = bracket = angle = 0
    index = 0
    while index < len(expression):
        char = expression[index]
        if char == "(":
            paren += 1
        elif char == ")":
            paren = max(0, paren - 1)
        elif char == "{":
            brace += 1
        elif char == "}":
            brace = max(0, brace - 1)
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket = max(0, bracket - 1)
        elif char == "⦃":
            angle += 1
        elif char == "⦄":
            angle = max(0, angle - 1)
        if paren == brace == bracket == angle == 0:
            token = next((token for token in tokens if expression.startswith(token, index)), None)
            if token is not None:
                splits.append((index, index + len(token)))
                index += len(token)
                continue
        index += 1
    return splits


def conclusion_and_hypotheses(result_type: str) -> tuple[str, str]:
    expression = _strip_outer_parens(result_type)
    hypotheses: list[str] = []
    while expression.startswith("∀"):
        commas = _top_level_splits(expression, (",",))
        if not commas:
            break
        _start, end = commas[0]
        hypotheses.append(expression[: _start + 1])
        expression = _strip_outer_parens(expression[end:])
    arrows = _top_level_splits(expression, ("→", "->"))
    if arrows:
        previous_end = 0
        segments: list[str] = []
        for start, end in arrows:
            segments.append(expression[previous_end:start])
            previous_end = end
        segments.append(expression[previous_end:])
        hypotheses.extend(segments[:-1])
        expression = segments[-1]
    return _strip_outer_parens(expression), " ".join(hypotheses)


def _prop_pattern(
    interface: PropInterface,
    declaration: Declaration,
    *,
    allow_unqualified: bool = False,
) -> re.Pattern[str]:
    qualified = re.escape(interface.declaration.name)
    alternatives = [qualified]
    if allow_unqualified or declaration.namespace == interface.declaration.namespace:
        alternatives.append(re.escape(interface.declaration.local_name))
    return re.compile(r"(?<![\w'.])(?:" + "|".join(alternatives) + r")(?![\w'])")


def analyze_interfaces(
    declarations: list[Declaration], interfaces: list[PropInterface] | None = None
) -> list[PropAnalysis]:
    interfaces = interfaces if interfaces is not None else prop_interfaces(declarations)
    local_counts = Counter(interface.declaration.local_name for interface in interfaces)
    analyses: list[PropAnalysis] = []
    for interface in interfaces:
        instantiator: Declaration | None = None
        hypothesis_users: list[Declaration] = []
        for candidate in declarations:
            if candidate.name == interface.declaration.name:
                continue
            pattern = _prop_pattern(
                interface,
                candidate,
                allow_unqualified=local_counts[interface.declaration.local_name] == 1,
            )
            inhabitation_commands = {
                "theorem",
                "lemma",
                "def",
                "abbrev",
                "opaque",
                "instance",
            }
            if not pattern.search(candidate.header):
                continue
            if candidate.kind not in inhabitation_commands:
                hypothesis_users.append(candidate)
                continue
            conclusion, hypotheses = conclusion_and_hypotheses(candidate.result_type)
            hypotheses = candidate.binders + " " + hypotheses
            if pattern.search(conclusion) and not pattern.search(hypotheses):
                instantiator = candidate
                break
            hypothesis_users.append(candidate)
        if instantiator is not None:
            status = "instantiated"
        elif hypothesis_users:
            status = "hypothesis-only"
        else:
            status = "unreferenced"
        analyses.append(
            PropAnalysis(interface, status, instantiator, tuple(hypothesis_users))
        )
    return analyses


def allowlist_names(path: Path) -> set[str]:
    names: set[str] = set()
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return names
    for line in lines:
        value = line.strip()
        if value and not value.startswith("#"):
            names.add(value.split("|", 1)[0].strip())
    return names


def has_git_worktree(root: Path) -> bool:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--is-inside-work-tree"],
        capture_output=True,
        text=True,
        check=False,
    )
    return result.returncode == 0 and result.stdout.strip() == "true"


def introduced_interfaces(
    root: Path,
    paths: list[str],
    current: list[PropInterface],
    *,
    baseline_by_path: dict[str, list[PropInterface]] | None = None,
) -> list[PropInterface]:
    """Select new/changed Prop definitions relative to HEAD.

    If there is no Git worktree (for example, in a source archive), every
    declaration is already part of the committed baseline and there is no
    working-copy change to check.
    """
    if baseline_by_path is None:
        if not has_git_worktree(root):
            return []
        baseline_by_path = {}
        for relative in paths:
            result = subprocess.run(
                ["git", "-C", str(root), "show", f"HEAD:{relative}"],
                capture_output=True,
                text=True,
                check=False,
            )
            if result.returncode == 0:
                baseline_by_path[relative] = prop_interfaces(
                    declarations_from_text(root, relative, result.stdout)
                )
            else:
                baseline_by_path[relative] = []
    baseline = {
        (interface.declaration.path, interface.declaration.name, _normalize(interface.declaration.header))
        for interfaces_in_file in baseline_by_path.values()
        for interface in interfaces_in_file
    }
    return [
        interface
        for interface in current
        if (interface.declaration.path, interface.declaration.name, _normalize(interface.declaration.header))
        not in baseline
    ]


def changed_source_paths(root: Path, paths: list[str]) -> list[str]:
    if not paths or not has_git_worktree(root):
        return []
    changed = subprocess.run(
        ["git", "-C", str(root), "diff", "--name-only", "HEAD", "--", *paths],
        capture_output=True,
        text=True,
        check=False,
    )
    untracked = subprocess.run(
        [
            "git",
            "-C",
            str(root),
            "ls-files",
            "--others",
            "--exclude-standard",
            "--",
            *paths,
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    selected = set(paths)
    candidates = set(changed.stdout.splitlines()) | set(untracked.stdout.splitlines())
    return sorted(selected & candidates)


def _normalize(text: str) -> str:
    return " ".join(text.split())


def policy_issues(
    introduced: list[PropInterface],
    analyses: list[PropAnalysis],
    allowed: set[str],
) -> list[PolicyIssue]:
    by_name = {analysis.interface.declaration.name: analysis for analysis in analyses}
    issues: list[PolicyIssue] = []
    for interface in introduced:
        declaration = interface.declaration
        if declaration.name in allowed:
            continue
        analysis = by_name.get(declaration.name)
        if interface.nullary:
            issues.append(PolicyIssue(interface, "new nullary Prop definition"))
        elif analysis is None or analysis.instantiator is None:
            status = analysis.status if analysis is not None else "uninstantiated"
            issues.append(PolicyIssue(interface, f"parameterized Prop is {status}"))
    return issues


def policy_issues_for_paths(
    root: Path,
    checked_paths: list[Path],
    allowlist_path: Path,
) -> list[PolicyIssue]:
    project_paths = project_lean_files(root)
    checked_relative: list[str] = []
    for path in checked_paths:
        try:
            relative = path.resolve().relative_to(root.resolve()).as_posix()
        except ValueError:
            continue
        if relative not in checked_relative:
            checked_relative.append(relative)
    all_paths = sorted(set(project_paths) | set(checked_relative))
    all_declarations = scan_paths(root, all_paths)
    all_interfaces = prop_interfaces(all_declarations)
    candidate_paths = changed_source_paths(root, checked_relative)
    checked_set = set(candidate_paths)
    checked_interfaces = [
        interface
        for interface in all_interfaces
        if interface.declaration.path in checked_set
    ]
    introduced = introduced_interfaces(root, candidate_paths, checked_interfaces)
    analyses = analyze_interfaces(all_declarations, all_interfaces)
    return policy_issues(introduced, analyses, allowlist_names(allowlist_path))


def satisfiability_witness(
    interface: PropInterface, given_declarations: list[Declaration]
) -> Declaration | None:
    expected = interface.declaration.name + "_satisfiable"
    for declaration in given_declarations:
        pattern = _prop_pattern(interface, declaration)
        conclusion, hypotheses = conclusion_and_hypotheses(declaration.result_type)
        proves_prop = bool(pattern.search(conclusion)) and not pattern.search(hypotheses)
        if declaration.name == expected and declaration.kind in {"theorem", "lemma"} and proves_prop:
            return declaration
        if declaration.kind == "instance" and proves_prop:
            body_match = TRIVIAL_MARKER.search(declaration.body)
            if body_match:
                return declaration
    return None


def given_witness_issues(root: Path, given: list[Path]) -> list[tuple[PropInterface, str]]:
    relative_paths: list[str] = []
    for path in given:
        try:
            relative_paths.append(path.resolve().relative_to(root.resolve()).as_posix())
        except ValueError:
            continue
    given_declarations = scan_paths(root, relative_paths)
    interfaces = prop_interfaces(given_declarations)
    if has_git_worktree(root):
        interfaces = introduced_interfaces(root, relative_paths, interfaces)
    issues: list[tuple[PropInterface, str]] = []
    for interface in interfaces:
        if satisfiability_witness(interface, given_declarations) is None:
            expected = interface.declaration.name + "_satisfiable"
            issues.append((interface, expected))
    return issues


def format_location(declaration: Declaration) -> str:
    return f"{declaration.path}:{declaration.line}"


def census_markdown(root: Path, revision: str | None = None) -> str:
    declarations = declarations_at_revision(root, revision) if revision else scan_paths(
        root, project_lean_files(root)
    )
    interfaces = prop_interfaces(declarations)
    analyses = analyze_interfaces(declarations, interfaces)
    snapshot = revision or "working tree"
    lines = [
        "# Prop-interface census",
        "",
        f"Tracked project `def ... : Prop` declarations at HEAD `{snapshot}`.",
        "“Instantiated” means the scanner found a tracked declaration that concludes the "
        "interface without assuming it, or a proof supplied to that interface as a field. "
        "Hypothesis-only and unreferenced rows are reported here and intentionally omitted "
        "from `scripts/prop_interface_allowlist.txt`.",
        "",
        "The census is generated by `python3 scripts/prop_interfaces.py --revision HEAD "
        "--output <census-path>`. "
        "The scan is syntactic and conservative; review the cited producer declaration when "
        "approving a new allowlist entry.",
        "",
        "| Declaration | Definition | Arity | Status | Instantiating declaration |",
        "|---|---|---|---|---|",
    ]
    for analysis in analyses:
        interface = analysis.interface
        declaration = interface.declaration
        arity = "nullary" if interface.nullary else "parameterized"
        producer = analysis.instantiator
        producer_text = (
            f"`{producer.name}` (`{producer.path}:{producer.line}`)" if producer else "—"
        )
        lines.append(
            f"| `{declaration.name}` | `{declaration.path}:{declaration.line}` | "
            f"{arity} | {analysis.status} | {producer_text} |"
        )
    lines.extend(
        [
            "",
            f"Total: {len(analyses)} tracked Prop definitions; "
            f"{sum(item.status == 'instantiated' for item in analyses)} instantiated, "
            f"{sum(item.status == 'hypothesis-only' for item in analyses)} hypothesis-only, "
            f"{sum(item.status == 'unreferenced' for item in analyses)} unreferenced. "
            f"The uninstantiated {sum(item.status != 'instantiated' for item in analyses)} "
            "entries are reports, not allowlist entries.",
            "",
        ]
    )
    return "\n".join(lines)


def declarations_at_revision(root: Path, revision: str) -> list[Declaration]:
    names = subprocess.run(
        ["git", "-C", str(root), "ls-tree", "-r", "--name-only", revision, "--", "ESS"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    paths = sorted(path for path in names if path.endswith(".lean"))
    root_module = subprocess.run(
        ["git", "-C", str(root), "cat-file", "-e", f"{revision}:ESS.lean"],
        capture_output=True,
        check=False,
    )
    if root_module.returncode == 0:
        paths.append("ESS.lean")
    declarations: list[Declaration] = []
    for relative in paths:
        result = subprocess.run(
            ["git", "-C", str(root), "show", f"{revision}:{relative}"],
            capture_output=True,
            text=True,
            check=True,
        )
        declarations.extend(declarations_from_text(root, relative, result.stdout))
    return declarations


def allowlist_markdown_rows(analyses: list[PropAnalysis]) -> list[str]:
    return [
        f"{analysis.interface.declaration.name} | "
        f"{format_location(analysis.interface.declaration)} | "
        f"{analysis.instantiator.name} ({format_location(analysis.instantiator)})"
        for analysis in analyses
        if analysis.status == "instantiated" and analysis.instantiator is not None
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=SCRIPTS.parent)
    parser.add_argument("--revision", help="inventory committed sources at this Git revision")
    parser.add_argument(
        "--allowlist-rows",
        action="store_true",
        help="print instantiated interfaces as name | definition | producer rows",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="write the census report to this path instead of stdout",
    )
    args = parser.parse_args(argv)
    try:
        if args.allowlist_rows:
            if args.revision:
                declarations = declarations_at_revision(args.root.resolve(), args.revision)
            else:
                paths = project_lean_files(args.root.resolve())
                declarations = scan_paths(args.root.resolve(), paths)
            analyses = analyze_interfaces(declarations)
            print("# Only entries with a source-level instantiating declaration belong here.")
            for row in allowlist_markdown_rows(analyses):
                print(row)
            return 0
        report = census_markdown(args.root.resolve(), args.revision)
        if args.output:
            args.output.write_text(report, encoding="utf-8")
            print(f"wrote {args.output}")
        else:
            print(report)
        return 0
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        print(f"prop_interfaces: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
