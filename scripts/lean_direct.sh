#!/usr/bin/env bash
# Copyright (c) 2026 Scott Armstrong.
# Released under Apache 2.0 license.
# Elaborate one ESS Lean file with the pinned toolchain binary against the
# already-built local and dependency oleans, without invoking Lake.
# Usage: scripts/lean_direct.sh <file.lean> [extra lean flags...]
# The file's own imports must already have oleans (run scripts/build.py first
# for local modules). Use this for temporary probes, #print axioms checks, and
# warm own-file profiles (add --profile). Never use it to compile a dependency.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean"
if [ ! -x "$LEAN" ]; then echo "pinned toolchain lean not found: $LEAN" >&2; exit 2; fi
LEAN_PATH="${ESS_EXTRA_LEAN_PATH:+$ESS_EXTRA_LEAN_PATH:}$ROOT/.lake/build/lib/lean"
for pkg in "$ROOT"/.lake/packages/*/; do
  lib="$pkg.lake/build/lib/lean"
  [ -d "$lib" ] && LEAN_PATH="$LEAN_PATH:$lib"
done
export LEAN_PATH
# When ESS_LEAN_SLOTS is set, take one of that many slots before
# elaborating, so that many concurrent processes share the machine fairly.
if [ -n "${ESS_LEAN_SLOTS:-}" ]; then
  slotdir="${ESS_LEAN_SLOT_DIR:-${TMPDIR:-/var/tmp}/lean-slots}"; mkdir -p "$slotdir"
  while :; do
    for i in $(seq 1 "$ESS_LEAN_SLOTS"); do
      exec {fd}>"$slotdir/slot$i"
      if flock -n "$fd"; then break 2; fi
      exec {fd}>&-
    done
    sleep 2
  done
fi
emit=0
if [ "${1:-}" = "--emit" ]; then emit=1; shift; fi
file="$1"; shift
if [ "$emit" = 1 ]; then
  # Emit the olean/ilean of a local module into the local build tree so that
  # other temporary files can import it before the next guarded build. Only
  # files under ESS/ (or the root module) may be emitted; scripts/build.py
  # regenerates these artifacts anyway.
  rel="$(realpath --relative-to="$ROOT" "$file")"
  case "$rel" in
    ESS/*.lean|ESS.lean) ;;
    *) echo "refusing to emit oleans for a non-local module: $rel" >&2; exit 2 ;;
  esac
  out="$ROOT/.lake/build/lib/lean/${rel%.lean}"
  mkdir -p "$(dirname "$out")"
  exec "$LEAN" "$@" -o "$out.olean" -i "$out.ilean" "$file"
fi
exec "$LEAN" "$@" "$file"
