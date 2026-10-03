#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
"""Check every comparator Challenge/Solution pair under comparators/<Topic>/.

Rule: a Challenge imports only Mathlib and defines every notion it uses from
Mathlib definitions.  The Solution repeats the Challenge command by command
(definitions, docstrings and theorem statements byte-identical up to
whitespace), adds ESS imports, transport lemmas and definitions, and replaces
each `by sorry` by a proof.  Each Challenge must compile with exactly one
`sorry` warning per selected theorem, each Solution must elaborate with
warnings as errors, and every selected Solution theorem must depend on exactly
the standard axioms.  For upstream Comparator and independent NanoDa replay,
also run scripts/verify_comparator.sh; this local check does not replace it.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_axioms import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
HARD_LINE_LIMIT = 1000
BYTE_LIMIT = 100 * 1024
# Vocabulary hygiene is enforced in the development repository before release.
FORBIDDEN_WORDS: tuple[str, ...] = ()
CONFIG_FIELDS = {
    "challenge_module", "solution_module", "theorem_names", "definition_names",
    "permitted_axioms", "enable_nanoda",
}
# Commands the Solution may add between the Challenge's commands: transport
# lemmas and the definitions they need.  Nothing that can change how a
# Challenge statement elaborates (instances, notation, options, opens, ...).
EXTRA_KEYWORDS = ("theorem", "lemma", "def", "abbrev")
DECL_HEAD = re.compile(
    r"^(?:@\[simp\]\s+)?(?:(?:noncomputable|protected)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|"
    r"inductive|opaque|axiom|example)\b(?:\s+([^\s(\[{:]+))?"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: Path) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def norm(text: str) -> str:
    """Whitespace-normalized text, keeping comments and docstrings."""
    return " ".join(text.split())


# `import`, `public import`, `meta import`, `public meta import`, each optionally `all`.
IMPORT_LINE = re.compile(
    r"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)[ \t]*$", re.M)


def imports(text: str) -> list[str]:
    return re.findall(IMPORT_LINE, text)


def without_imports(text: str) -> str:
    return re.sub(r"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t].+\n", "", text, flags=re.M)


def chunks(text: str) -> list[tuple[str, str, str]]:
    """Split a module (without imports) into commands.

    Each chunk is `(full_text, code_text, head)`: the original text of the
    command with the comments and docstring that precede it, the same text with
    comments blanked, and the first code line.  Commands start at a line whose
    first character is not whitespace after comments are blanked.
    """
    blank = strip_comments(text)
    lines = text.splitlines(keepends=True)
    blines = blank.splitlines(keepends=True)
    starts = [i for i, line in enumerate(blines) if line[:1] not in ("", " ", "\t", "\n")]
    out: list[tuple[str, str, str]] = []
    previous_end = 0
    for k, start in enumerate(starts):
        nxt = starts[k + 1] if k + 1 < len(starts) else len(lines)
        end = start + 1
        for j in range(start, nxt):
            if blines[j].strip():
                end = j + 1
        out.append(("".join(lines[previous_end:end]), "".join(blines[start:end]),
                    blines[start].strip()))
        previous_end = end
    require("".join(lines[previous_end:]).strip() == "",
            "text after the last command is not a command")
    return out


def split_statement(chunk: tuple[str, str, str], name: str) -> tuple[str, str]:
    """Statement (through the terminating `:=`) and proof of a theorem chunk."""
    full, code, _ = chunk
    flines = full.splitlines(keepends=True)
    clines = code.splitlines(keepends=True)
    # `code` covers only the command lines, `full` also has the leading comments.
    offset = len(flines) - len(clines)
    for i, line in enumerate(clines):
        if line.rstrip().endswith(":="):
            stated = "".join(flines[:offset + i + 1])
            proof = "".join(flines[offset + i + 1:])
            return stated.rstrip()[:-2], proof
    raise ValueError(f"statement of {name} is not terminated by `:=`")


def strip_proof(proof: str) -> str:
    return norm(strip_comments(proof))


def declared_name(head: str) -> tuple[str, str] | None:
    match = DECL_HEAD.match(head)
    if match is None:
        return None
    return match.group(1), (match.group(2) or "")


def check_pair(topic: str, config: dict[str, object]) -> int:
    """Source checks of one Challenge/Solution pair; returns the theorem count."""
    require(isinstance(config, dict) and set(config) == CONFIG_FIELDS,
            f"{topic}: comparator.json has missing or unauthorized fields")
    challenge_path = Path(f"comparators/{topic}/Challenge.lean")
    solution_path = Path(f"comparators/{topic}/Solution.lean")
    # The Comparators library has srcDir `comparators`, so the modules are
    # `<Topic>.Challenge` and `<Topic>.Solution`: their first name component is
    # the topic, which no dependency defines at the root of its sources.
    require(config["challenge_module"] == f"{topic}.Challenge"
            and config["solution_module"] == f"{topic}.Solution",
            f"{topic}: comparator.json must select {topic}.Challenge and {topic}.Solution")
    names = config["theorem_names"]
    require(isinstance(names, list) and names and all(isinstance(n, str) for n in names),
            f"{topic}: theorem_names must be a nonempty string array")
    require(config["definition_names"] == [],
            f"{topic}: comparator definitions must not be selected as exports")
    require(config["permitted_axioms"] == AXIOMS and config["enable_nanoda"] is True,
            f"{topic}: comparator.json must use the standard axiom set and enable NanoDa")
    require(all(n.startswith("ESSChallenge.") and n.count(".") == 1 for n in names),
            f"{topic}: theorem names must be ESSChallenge.<name>")
    local = [n.split(".", 1)[1] for n in names]
    require(len(set(local)) == len(local), f"{topic}: duplicate comparator theorem name")

    challenge, solution = read(challenge_path), read(solution_path)
    require(len(challenge.splitlines()) <= HARD_LINE_LIMIT and len(challenge.encode()) <= BYTE_LIMIT,
            f"{topic}: Challenge exceeds the 1000-line or 100-KiB limit")
    require(len(re.findall(r"\bsorry\b", strip_comments(challenge))) == len(local),
            f"{topic}: Challenge must contain exactly {len(local)} intentional proof placeholders")
    require(not re.search(r"\b(?:sorry|admit|axiom|constant|sorryAx)\b", strip_comments(solution)),
            f"{topic}: Solution contains a placeholder or axiom declaration")
    for text, label in ((challenge, "Challenge"), (solution, "Solution")):
        require(re.findall(r"^namespace (\S+)", text, re.M) == ["ESSChallenge"],
                f"{topic}: {label} must use the single namespace ESSChallenge")
        require(not re.search(r"^\s*private\b", strip_comments(text), re.M),
                f"{topic}: {label} has private declarations")
        require(all(option.strip() == "autoImplicit false" for option in
                    re.findall(r"^\s*set_option (.+)$", text, re.M)),
                f"{topic}: {label} sets an unexpected Lean option")
        hits = sorted(word for word in FORBIDDEN_WORDS
                      if re.search(rf"\b{re.escape(word)}", text, flags=re.I))
        require(not hits, f"{topic}: {label} contains internal vocabulary: {hits}")

    # The Rule: a Challenge imports only Mathlib; the Solution adds ESS imports.
    challenge_imports = imports(challenge)
    require(challenge_imports and all(m == "Mathlib" or m.startswith("Mathlib.")
                                      for m in challenge_imports),
            f"{topic}: Challenge may import only Mathlib")
    solution_imports = imports(solution)
    extra_imports = [m for m in solution_imports if m not in challenge_imports]
    require(all(m in solution_imports for m in challenge_imports) and extra_imports
            and all(m.startswith(("ESS.", "CKN.")) for m in extra_imports)
            and len(set(solution_imports)) == len(solution_imports),
            f"{topic}: Solution must import the Challenge's Mathlib modules and ESS/CKN modules only")

    # The Solution repeats the Challenge command by command; it may only replace
    # each `by sorry` by a proof and add transport theorems, lemmas and
    # definitions (none of which may reuse a name of the Challenge).
    # Module scaffolding (the `module` header and the public section that follows the
    # module docstring) is structure, not a statement: set it aside before matching.
    def scaffold(chunk: tuple[str, str, str]) -> bool:
        return chunk[2] in ("module", "@[expose] public section", "public section")
    # A Solution may open the CKN namespace (the dependency's notions) for its transport lemmas.
    def solution_scaffold(chunk: tuple[str, str, str]) -> bool:
        return scaffold(chunk) or chunk[1].strip() == "open CKN"
    cc_all = chunks(without_imports(challenge))
    sc_all = chunks(without_imports(solution))
    for label, text_chunks in (("Challenge", cc_all), ("Solution", sc_all)):
        require(any(c[2] == "module" for c in text_chunks), f"{topic}: {label} lacks the `module` header")
    cc = [c for c in cc_all if not scaffold(c)]
    sc = [c for c in sc_all if not solution_scaffold(c)]
    pointer = 0
    seen: list[str] = []
    extras: list[tuple[str, str]] = []
    for chunk in sc:
        target = cc[pointer] if pointer < len(cc) else None
        if target is not None:
            challenge_decl = declared_name(target[2])
            is_selected = (challenge_decl is not None and challenge_decl[0] == "theorem"
                           and challenge_decl[1] in local)
            if is_selected:
                name = challenge_decl[1]
                cstate, cproof = split_statement(target, name)
                head = declared_name(chunk[2])
                if head == ("theorem", name):
                    sstate, sproof = split_statement(chunk, name)
                    require(strip_proof(cproof) == "by sorry",
                            f"{topic}: Challenge proof of {name} is not exactly `by sorry`")
                    require(norm(sstate) == norm(cstate),
                            f"{topic}: Solution statement of {name} differs from the Challenge")
                    require(strip_proof(sproof) not in ("", "by sorry"),
                            f"{topic}: Solution has no proof of {name}")
                    seen.append(name)
                    pointer += 1
                    continue
            elif norm(chunk[0]) == norm(target[0]):
                pointer += 1
                continue
        head = declared_name(chunk[2])
        require(head is not None and head[0] in EXTRA_KEYWORDS and head[1]
                and not chunk[2].startswith("private"),
                f"{topic}: Solution adds a command that is not a theorem, lemma or definition: "
                f"{chunk[2]!r}")
        extras.append((head[0], head[1]))
    require(pointer == len(cc), f"{topic}: the Solution does not repeat every Challenge command")
    require(sorted(seen) == sorted(local),
            f"{topic}: Solution or Challenge lacks a selected theorem: "
            f"{sorted(set(local) ^ set(seen))}")
    tokens = set(re.findall(r"[\w][\w'.]*", strip_comments(challenge)))
    for _, name in extras:
        bare = name.split(".")[-1]
        require(name not in tokens and bare not in tokens,
                f"{topic}: transport declaration {name} reuses a name of the Challenge")
    return len(local)


def check_sources(topics: list[str]) -> dict[str, dict[str, object]]:
    configs: dict[str, dict[str, object]] = {}
    for topic in topics:
        config = json.loads(read(Path(f"comparators/{topic}/comparator.json")))
        count = check_pair(topic, config)
        configs[topic] = config
        print(f"Comparator sources PASS ({topic}): {count} statements, Mathlib-only Challenge, "
              "Solution repeats it verbatim")
    return configs


def lean(path: Path, *args: str, extra_path: Path | None = None) -> tuple[int, str]:
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "6")
    if extra_path is not None:
        env["ESS_EXTRA_LEAN_PATH"] = str(extra_path)
    process = subprocess.run(
        [str(ROOT / "scripts/lean_direct.sh"), str(path), "-DautoImplicit=false", *args],
        cwd=ROOT, env=env, capture_output=True, text=True,
    )
    return process.returncode, (process.stdout + process.stderr).strip()


def check_proofs(topic: str, config: dict[str, object]) -> None:
    names = [str(n).split(".", 1)[1] for n in config["theorem_names"]]
    challenge = Path(f"comparators/{topic}/Challenge.lean")
    solution = Path(f"comparators/{topic}/Solution.lean")
    with tempfile.TemporaryDirectory(prefix="ess-comparator-") as directory:
        staging = Path(directory)
        (staging / topic).mkdir(parents=True)
        result, output = lean(challenge)
        diagnostics = [line for line in output.splitlines() if line.strip()]
        require(result == 0 and len(diagnostics) == len(names) and all(
            line.startswith(f"{challenge}:") and line.endswith("warning: declaration uses `sorry`")
            for line in diagnostics
        ), f"{topic}: unexpected Challenge diagnostics (exit {result}): {diagnostics}")
        result, output = lean(solution, "-DwarningAsError=true",
                             "-o", str(staging / topic / "Solution.olean"))
        require(result == 0 and not output,
                f"{topic}: Solution did not elaborate silently (exit {result}): {output}")

        probe = staging / "Axioms.lean"
        probe.write_text(
            f"import {topic}.Solution\n"
            + "".join(f"#print axioms ESSChallenge.{name}\n" for name in names),
            encoding="utf-8",
        )
        result, output = lean(probe, "-DwarningAsError=true", extra_path=staging)
        expected = [
            f"'ESSChallenge.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in names
        ]
        require(result == 0 and output.splitlines() == expected,
                f"{topic}: unexpected Solution axioms: {output}")
    print(f"Comparator proofs PASS ({topic}): {len(names)} standard axiom sets")


def main(argv: list[str] | None = None) -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--no-build", action="store_true", help="source checks only")
    parser.add_argument("--topic", action="append", default=[],
                        help="check only this comparators/<Topic> pair (repeatable)")
    parser.add_argument("--lake", action="store_true", help="build Comparators through the guarded wrapper")
    args = parser.parse_args(argv)
    ROOT = args.root.resolve()
    try:
        topics = sorted(p.parent.name for p in (ROOT / "comparators").glob("*/comparator.json"))
        if args.topic:
            require(all(t in topics for t in args.topic), f"unknown comparator topic in {args.topic}")
            topics = [t for t in topics if t in args.topic]
        if not topics:
            print("No comparator challenge registered yet; source checks deferred.")
            return 0
        configs = check_sources(topics)
        if args.lake:
            subprocess.run([sys.executable, str(ROOT / "scripts/build.py"), "Comparators"],
                           cwd=ROOT, check=True)
        if not args.no_build:
            for topic in topics:
                check_proofs(topic, configs[topic])
    except (ValueError, OSError, subprocess.CalledProcessError, KeyError, TypeError) as error:
        print(f"Comparator check failed: {error}")
        return 1
    print("All local comparator checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
