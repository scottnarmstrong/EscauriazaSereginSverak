#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
"""Check the published file set, local documentation links and library imports.

In a Git checkout the tracked files are checked; in a source tree without Git
metadata every file outside ``.lake`` is checked.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
ROOT_FILES = {
    ".gitignore", "CITATION.cff", "CONTRIBUTING.md", "ESS.lean", "LICENSE",
    "README.md", "formalization.yaml", "lake-manifest.json",
    "lakefile.toml", "lean-toolchain",
}
REQUIRED_FILES = ROOT_FILES | {
    "comparators/README.md",
    *(f"comparators/{topic}/{name}" for topic in ("Linear", "Regularity")
      for name in ("Challenge.lean", "Solution.lean", "comparator.json")),
    "paper/ess.tex",
}
DIRECTORIES = {"ESS", "comparators", "docs", "paper", "scripts", ".github"}
TEXT_SUFFIXES = {
    ".lean", ".md", ".tex", ".bib", ".py", ".sh", ".toml", ".yaml",
    ".yml", ".json", ".cff", ".txt",
}
SCRIPT_SUFFIXES = {".py", ".sh"}
SCRIPT_HEADER = [
    "# Copyright (c) 2026 Scott Armstrong.",
    "# Released under Apache 2.0 license.",
]


def release_files(root: Path) -> list[str]:
    if (root / ".git").exists():
        result = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=False
        )
        if result.returncode == 0 and result.stdout:
            return sorted(set(result.stdout.decode().split("\0")) - {""})
    return sorted(
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file()
        and not {".git", ".lake", "__pycache__"} & set(path.relative_to(root).parts)
    )


def root_import_closure(root: Path) -> set[str]:
    """Modules reachable from ``ESS.lean`` through ``import ESS...`` lines."""
    seen: set[str] = set()
    stack = ["ESS"]
    while stack:
        module = stack.pop()
        path = root / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            continue
        for imported in re.findall(r"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(ESS(?:\.[\w]+)+)[ \t]*$", path.read_text(encoding="utf-8"), re.M):
            if imported not in seen:
                seen.add(imported)
                stack.append(imported)
    return seen


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    files = release_files(root)
    errors: list[str] = []
    missing = REQUIRED_FILES - set(files)
    if missing:
        errors.append(f"missing required files: {sorted(missing)}")

    for name in files:
        path = Path(name)
        if name not in ROOT_FILES and (len(path.parts) == 1 or path.parts[0] not in DIRECTORIES):
            errors.append(f"unexpected release path: {name}")
        allowed = (
            path.parts[0] == "ESS" and path.suffix == ".lean"
            or path.parts[0] == "comparators" and path.suffix in {".lean", ".md", ".json"}
            or path.parts[0] == "docs" and path.suffix == ".md"
            or path.parts[0] == "paper" and path.suffix in {".tex", ".bib", ".pdf"}
            or path.parts[0] == "scripts" and path.suffix in SCRIPT_SUFFIXES | {".txt"}
            or path.parts[:2] == (".github", "workflows") and path.suffix == ".yml"
            or name in ROOT_FILES
        )
        if not allowed:
            errors.append(f"unexpected release file type: {name}")
        if path.suffix == ".pdf" and name != "paper/ess.pdf":
            errors.append(f"unexpected PDF: {name}")
        source = root / path
        if source.is_symlink() or not source.is_file():
            errors.append(f"missing or symlinked source: {name}")
            continue
        if path.suffix not in TEXT_SUFFIXES:
            continue
        text = source.read_text(encoding="utf-8")
        if path.suffix == ".md":
            for match in re.finditer(r"\]\(([^\s)]+)\)", text):
                target = match.group(1).split("#")[0]
                if not target or re.match(r"[a-z]+:", target):
                    continue
                destination = (source.parent / target).resolve()
                if not destination.is_relative_to(root) or not destination.exists():
                    errors.append(f"{name}: missing local link {target}")
        if path.suffix == ".lean":
            for module in re.findall(r"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(ESS(?:\.[\w]+)*)[ \t]*$", text, re.M):
                if module.replace(".", "/") + ".lean" not in files:
                    errors.append(f"{name}: missing import {module}")
        if path.suffix in SCRIPT_SUFFIXES:
            lines = text.splitlines()
            offset = 1 if lines and lines[0].startswith("#!") else 0
            if lines[offset : offset + 2] != SCRIPT_HEADER:
                errors.append(f"{name}: missing required copyright header")

    library = {
        name[:-5].replace("/", ".") for name in files
        if name.startswith("ESS/") and name.endswith(".lean")
    }
    unreachable = sorted(library - root_import_closure(root))
    if unreachable:
        errors.append(
            f"{len(unreachable)} ESS module(s) not imported by ESS.lean, e.g. {unreachable[:5]}"
        )

    for error in errors:
        print(f"check_public: {error}", file=sys.stderr)
    print(f"check_public: {'FAIL' if errors else 'PASS'} ({len(files)} files)")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
