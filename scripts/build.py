#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
"""Build local ESS modules with a fail-closed upstream package guard.

The upstream packages are Mathlib and the published CKN formalization
(``.lake/packages/CKN``). By default the guard requires both package trees to
be unchanged. The first build compiles CKN; with ``ESS_IGNORE_PACKAGE_BUILD=1``
the guard still requires Mathlib's package tree and CKN's source tree to be
unchanged, and permits CKN's generated build artifacts.

``--fresh TARGET`` is available only in a disposable non-main checkout. It
does not weaken the upstream package-tree integrity guard.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = ROOT / ".lake/packages/mathlib"
CKN_PACKAGE = ROOT / ".lake/packages/CKN"
# Upstream package trees that a guarded build must leave untouched.
UPSTREAM_PACKAGES = {"Mathlib": MATHLIB, "CKN": CKN_PACKAGE}
MATHLIB_OLEAN_CACHE_COUNT = 8555
MATHLIB_OLEAN_THRESHOLD = (MATHLIB_OLEAN_CACHE_COUNT * 90 + 99) // 100
EXPECTED_LEAN_VERSION = "Lean version 4.35.0-rc2"
PACKAGE = "ESS"
ALLOWED_TARGETS = {PACKAGE, "Comparators"}
# ``--fresh`` is deliberately restricted to disposable checkouts.  Keep the
# main checkout explicit so that the ordinary package-preservation guard can
# never be weakened by an environment variable or an invocation typo.
MAIN_CHECKOUT = Path(os.environ.get("ESS_MAIN_CHECKOUT", str(ROOT))).resolve()


def count_oleans(root: Path) -> int:
    return sum(1 for _ in root.rglob("*.olean")) if root.exists() else 0


def run_checked(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, check=True, text=True, **kwargs)


def git_output(repository: Path, *arguments: str) -> str:
    try:
        return run_checked(
            ["git", "-C", str(repository), *arguments], capture_output=True
        ).stdout.strip()
    except subprocess.CalledProcessError as exc:
        raise SystemExit(f"refusing build: Git check failed for {repository}: {exc}") from exc


def artifact_snapshot(
    root: Path, *, ignore_generated_build: bool = False
) -> dict[str, tuple[int, int, int, int, int]]:
    """Record package-tree entries without reading their contents.

    A disposable checkout may reuse generated package build artifacts.  Those
    entries, including the containing ``.lake`` directory, are intentionally
    outside that check's source-package mutation guard.
    """
    snapshot: dict[str, tuple[int, int, int, int, int]] = {}
    if not root.exists():
        return snapshot
    for path in (root, *root.rglob("*")):
        relative = path.relative_to(root)
        # Git's own metadata (index refreshes, lock files) is not package source; source
        # integrity is enforced separately by the pinned-revision Git check.
        if relative.parts[:1] == (".git",):
            continue
        # Lake trace-hash files (e.g. `*.ir.sig.hash`) are bookkeeping written next to
        # cached artifacts, not compiled artifacts; a Mathlib recompile is caught
        # separately by the forbidden-output check.
        if relative.suffix == ".hash" and ".lake" in relative.parts:
            continue
        if ignore_generated_build and (
            relative == Path(".")
            or relative == Path(".git")
            or relative.parts[:1] == (".git",)
            or relative == Path(".lake")
            or any(
                relative.parts[index : index + 2] == (".lake", "build")
                for index in range(len(relative.parts) - 1)
            )
        ):
            continue
        metadata = path.lstat()
        snapshot[str(relative) or "."] = (
            metadata.st_mode,
            metadata.st_size,
            metadata.st_mtime_ns,
            metadata.st_ctime_ns,
            metadata.st_ino,
        )
    return snapshot


def stop_process(process: subprocess.Popen[str]) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


run_checked([sys.executable, str(ROOT / "scripts/check_rules.py")], cwd=ROOT)

build_arguments = list(sys.argv[1:])
fresh_mode = False
if "--fresh" in build_arguments:
    if build_arguments.count("--fresh") != 1:
        raise SystemExit("refusing build arguments: --fresh may be given at most once")
    build_arguments.remove("--fresh")
    fresh_mode = True
if build_arguments and (
    len(build_arguments) != 1 or build_arguments[0] not in ALLOWED_TARGETS
):
    raise SystemExit(
        f"refusing build arguments: expected no arguments or exactly one of "
        f"{sorted(ALLOWED_TARGETS)}, with optional --fresh"
    )
if fresh_mode and ROOT.resolve() == MAIN_CHECKOUT:
    raise SystemExit(
        "refusing --fresh in the main checkout; package-tree changes must fail closed"
    )

environment = os.environ.copy()
for variable in ("LEAN_PATH", "LAKE_PACKAGES_DIR", "ELAN_TOOLCHAIN"):
    environment.pop(variable, None)
environment.setdefault("LEAN_NUM_THREADS", "6")
try:
    lean_threads = int(environment["LEAN_NUM_THREADS"])
except ValueError as exc:
    raise SystemExit("refusing build: LEAN_NUM_THREADS must be a positive integer") from exc
if lean_threads < 1:
    raise SystemExit("refusing build: LEAN_NUM_THREADS must be a positive integer")

try:
    lake_version = run_checked(
        ["lake", "--version"], cwd=ROOT, env=environment, capture_output=True
    ).stdout.strip()
except (FileNotFoundError, subprocess.CalledProcessError) as exc:
    raise SystemExit(f"refusing build: cannot resolve the pinned Lake executable: {exc}") from exc
if EXPECTED_LEAN_VERSION not in lake_version:
    raise SystemExit(f"refusing build: unexpected Lake/Lean version: {lake_version}")
print(lake_version, flush=True)

if not MATHLIB.is_dir():
    raise SystemExit(f"refusing build: Mathlib package is missing: {MATHLIB}")
if not CKN_PACKAGE.is_dir():
    raise SystemExit(f"refusing build: CKN package is missing: {CKN_PACKAGE}")
mathlib_oleans = count_oleans(MATHLIB / ".lake/build/lib")
print(
    f"mathlib oleans: {mathlib_oleans} (minimum {MATHLIB_OLEAN_THRESHOLD})",
    flush=True,
)
if mathlib_oleans < MATHLIB_OLEAN_THRESHOLD:
    raise SystemExit(
        f"refusing build: Mathlib olean threshold {MATHLIB_OLEAN_THRESHOLD} failed"
    )

try:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
except (json.JSONDecodeError, OSError) as exc:
    raise SystemExit(f"refusing build: cannot read lake-manifest.json: {exc}") from exc
mathlib_entry = next(
    (entry for entry in manifest.get("packages", []) if entry.get("name") == "mathlib"),
    None,
)
if not isinstance(mathlib_entry, dict) or not isinstance(mathlib_entry.get("rev"), str):
    raise SystemExit("refusing build: lake-manifest.json has no pinned Mathlib revision")
actual_revision = git_output(MATHLIB, "rev-parse", "HEAD")
if actual_revision != mathlib_entry["rev"]:
    raise SystemExit(
        f"refusing build: mathlib is at {actual_revision}, expected {mathlib_entry['rev']}"
    )
package_status = git_output(MATHLIB, "status", "--short")
if package_status:
    print(package_status, file=sys.stderr)
    raise SystemExit("refusing build: Mathlib package is not clean")

ckn_entry = next(
    (entry for entry in manifest.get("packages", []) if entry.get("name") == "CKN"),
    None,
)
if not isinstance(ckn_entry, dict) or not isinstance(ckn_entry.get("rev"), str):
    raise SystemExit("refusing build: lake-manifest.json has no pinned CKN revision")
actual_ckn_revision = git_output(CKN_PACKAGE, "rev-parse", "HEAD")
if actual_ckn_revision != ckn_entry["rev"]:
    raise SystemExit(
        f"refusing build: CKN is at {actual_ckn_revision}, expected {ckn_entry['rev']}"
    )
# The upstream CKN checkout does not ignore its own .lake/ build tree, which
# Lake populates when CKN is compiled from source; exclude it from the
# cleanliness check so that only source mutations count.
ckn_status = git_output(CKN_PACKAGE, "status", "--short", "--", ".", ":(exclude).lake")
if ckn_status:
    print(ckn_status, file=sys.stderr)
    raise SystemExit("refusing build: CKN package is not clean")

# Local-artifact invalidation is opt-in (ESS_INVALIDATE=1).  By default Lake's own
# traces decide what to rebuild, so oleans emitted by scripts/lean_direct.sh --emit
# for temporary probes are kept until Lake replaces them.
removed: list[Path] = []
for base in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
    if os.environ.get("ESS_INVALIDATE") != "1" or not base.exists():
        continue
    resolved_base = base.resolve()
    if not resolved_base.is_relative_to(ROOT.resolve()):
        raise SystemExit(f"refusing unsafe artifact root: {resolved_base}")
    for target in base.glob(f"{PACKAGE}*"):
        resolved_target = target.resolve()
        if not resolved_target.is_relative_to(resolved_base):
            raise SystemExit(f"refusing unsafe artifact target: {resolved_target}")
        if target.is_dir():
            shutil.rmtree(target)
        else:
            target.unlink()
        removed.append(target)

print(
    f"removed {len(removed)} generated local artifacts; Lake will regenerate them",
    flush=True,
)

command = ["lake", "--old", "--no-ansi", "build", *(build_arguments or [PACKAGE])]
forbidden_output = re.compile(
    r"(?:^|\s)(?:Building|Built|Compiling)\s+Mathlib(?:[./:]|\b)|"
    r"\.lake/packages/mathlib(?:/|\b)"
)
diagnostic_output = re.compile(r"^\s*(?:warning|error|info|note|trace):")
ignore_generated_package_build = os.environ.get("ESS_IGNORE_PACKAGE_BUILD") == "1"
snapshots_before = {
    name: artifact_snapshot(
        path,
        # CKN compiles from source; CI may ignore only its generated Lake build
        # directory. Mathlib remains fully guarded in every mode.
        ignore_generated_build=ignore_generated_package_build and name == "CKN",
    )
    for name, path in UPSTREAM_PACKAGES.items()
}

print(f"LEAN_NUM_THREADS={lean_threads}", flush=True)

process: subprocess.Popen[str] | None = None
failure: str | None = None
caught: BaseException | None = None
try:
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        start_new_session=True,
    )
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="", flush=True)
        if forbidden_output.search(line) and not diagnostic_output.match(line):
            failure = f"terminated forbidden Mathlib activity after line: {line.strip()}"
            stop_process(process)
            break
    if failure is None:
        return_code = process.wait()
        if return_code != 0:
            failure = f"Lake build failed with exit code {return_code}"
except BaseException as exc:
    caught = exc
finally:
    if process is not None:
        stop_process(process)
    for name, package_root in UPSTREAM_PACKAGES.items():
        snapshot_before = snapshots_before[name]
        snapshot_after = artifact_snapshot(
            package_root,
            ignore_generated_build=ignore_generated_package_build and name == "CKN",
        )
        if snapshot_after == snapshot_before:
            continue
        detail = f"{name} package tree changed during guarded build"
        changed = sorted(
            set(snapshot_before) ^ set(snapshot_after)
            | {
                path
                for path in set(snapshot_before) & set(snapshot_after)
                if snapshot_before[path] != snapshot_after[path]
            }
        )
        if fresh_mode:
            print(f"fresh checkout: {detail}", file=sys.stderr)
        for path in changed:
            print(f"  {path}", file=sys.stderr)
        failure = f"{failure}; {detail}" if failure else detail

if caught is not None:
    if failure:
        raise SystemExit(failure) from caught
    raise caught
if failure:
    raise SystemExit(failure)

if fresh_mode:
    print("guarded fresh-checkout build: PASS (upstream source trees unchanged)", flush=True)
else:
    print("guarded local build: PASS (Mathlib package tree and CKN "
          + ("source tree" if os.environ.get("ESS_IGNORE_PACKAGE_BUILD") == "1" else "package tree")
          + " unchanged)", flush=True)
