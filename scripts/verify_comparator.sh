#!/usr/bin/env bash
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
# Adapted from PalomarRegistry/PalomarTemplate's Apache-2.0 verification script.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${ESS_COMPARATOR_CACHE:-"${XDG_CACHE_HOME:-$HOME/.cache}/ess-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

comparator_commit=32bd61da1d68fbaa310234964e9b820b03a0f82f
lean4export_commit=6cea97789dc088ea47fcea15692db85685aedac5
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

mapfile -t comparator_configs < <(cd "$repository_root" && ls comparators/*/comparator.json)
if [ "${#comparator_configs[@]}" -eq 0 ]; then
  echo "error: no comparators/*/comparator.json found" >&2
  exit 1
fi

python3 - "${comparator_configs[@]/#/$repository_root/}" <<'PY'
import json
import pathlib
import sys

for argument in sys.argv[1:]:
    config_path = pathlib.Path(argument)
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
        raise SystemExit(1)

    if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
        print(
            f"error: {config_path}: enable_nanoda must be exactly true; "
            "the NanoDa replay is required",
            file=sys.stderr,
        )
        raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  echo "update lean4export_commit when changing lean-toolchain, then review" >&2
  echo "Comparator and NanoDa compatibility with the export format" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOMAXPROCS="${GOMAXPROCS:-2}" GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}" lake build comparator)
(cd "$lean4export_dir" && LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}" lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked -j "${CARGO_BUILD_JOBS:-2}")

cd "$repository_root"
for config in "${comparator_configs[@]}"; do
  echo "== Comparator: $config"
  COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  COMPARATOR_LANDRUN="$bin_dir/landrun" \
    lake env "$comparator_dir/.lake/build/bin/comparator" "$config"
done
