# Verification

Run these commands from the repository root. The toolchain and dependencies
are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`:
Lean and Mathlib at `v4.35.0-rc2`, and the Caffarelli–Kohn–Nirenberg (CKN)
formalization at an exact commit (`381d658ead0f03a18361965cc0427ce3fa5844ab`). Both libraries use Lean's
module system.

## Install and build

With `elan` and Python 3 installed:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
ESS_IGNORE_PACKAGE_BUILD=1 python3 scripts/build.py ESS
```

The build follows the imports of `ESS.lean`, which imports every module of
the library, including the main theorem statements, their proofs and the
examples. Library warnings are treated as errors. The Mathlib cache does not
contain the CKN dependency, so the first build also compiles CKN from source. The CKN dependency
contains the Leray background (definitions of Leray–Hopf solutions, Leray's
existence theorem, the associated pressure and the forced versions), which is
verified in the CKN repository.

The build wrapper first runs the source checks described below. It then
checks the toolchain, the Mathlib and CKN revisions against the manifest, the
Mathlib cache, and that neither dependency's source tree changes during the
build. Keep the committed manifest and avoid `lake update` or `lake clean`
during verification.

A normal successful build ends with:

```text
guarded local build: PASS (Mathlib package tree and CKN source tree unchanged)
```

`ESS_IGNORE_PACKAGE_BUILD=1` is needed because the first build compiles CKN
and so creates CKN's compiled files; the guard still checks that the sources
of CKN and Mathlib are unchanged, and that Mathlib's compiled files are
untouched.

In a disposable checkout, CI sets `ESS_MAIN_CHECKOUT` to a different path,
sets `ESS_IGNORE_PACKAGE_BUILD=1` so that CKN's generated build directory may
change, and uses `python3 scripts/build.py --fresh ESS`. Mathlib remains fully
guarded in that mode.

## Independent theorem statements

```sh
ESS_IGNORE_PACKAGE_BUILD=1 python3 scripts/build.py Comparators
python3 scripts/check_comparators.py
```

Two independent Challenge/Solution pairs, `comparators/Linear` and
`comparators/Regularity`, restate all ten main theorems of this library. (The
comparator pair for the Leray theorems is in the CKN repository.) Each
Challenge imports only Mathlib and defines every notion it uses from Mathlib
definitions (`EuclideanSpace ℝ (Fin 3)`, `fderiv`, Mathlib measures), with one intentional proof placeholder per theorem. The separate
Solution proves the same named statements from this library, using transport
lemmas between the Mathlib-native notions and the library's. The local checker
rejects any non-Mathlib import in a Challenge, compares the Challenge and
Solution sources, checks that each statement agrees with the library
statement it cites, and verifies the solutions' exact standard axiom sets.
`--topic <Name>` (`Linear` or `Regularity`) checks one pair;
`--no-build` performs the source checks only; `--lake` also builds the target.

Run the upstream verification, including the independent NanoDa kernel:

```sh
scripts/verify_comparator.sh
```

This builds pinned verification tools in a user cache and runs the upstream Comparator and NanoDa on every pair, using
`comparators/<Topic>/comparator.json` for each pair. It requires Linux with Landlock
support, Go 1.24 or later, Rust/Cargo, Python 3, Git and Lean. See the
[comparator guide](../comparators/README.md) for the verification boundaries.

## Source checks and axioms

```sh
python3 scripts/check_rules.py
python3 scripts/dup_decls.py
python3 scripts/check_public.py
python3 scripts/check_axioms.py
```

The source checks enforce the repository conventions: the copyright header,
no `sorry`, `admit` or `axiom`, no heartbeat overrides, no bare `linarith`
or `nlinarith`, at most 1,500 lines per library file, no duplicate declaration names
or duplicate theorem statements, and no unreviewed uninstantiated `Prop`
interface. The main theorem statements are restated from the modules that
prove them by a one-line `by exact`; the duplicate-statement check accepts
exactly those direct restatements. The public-file check verifies the
allowed file types, local documentation links, library imports, and that
`ESS.lean` imports every library module.

The axiom checker imports every tracked ESS module and checks every named
public declaration found by its source lexer. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted; there are no exceptions.
In particular, `sorryAx` and custom axioms are rejected. A failed Lean probe
or a nonzero checker exit status is a verification failure. File and
declaration counts are reported at run time.

## Inspect the main theorems directly

After building the library:

```sh
probe_dir=$(mktemp -d)
cat > "$probe_dir/MainAxioms.lean" <<'LEAN'
import ESS

#print axioms ESS.essLocal
#print axioms ESS.essGlobal
#print axioms ESS.essL5Unique
#print axioms ESS.uniqueContinuation
#print axioms ESS.backwardUniqueness
#print axioms ESS.carlemanGaussian
#print axioms ESS.carlemanHalfSpace
#print axioms ESS.ladyzhenskayaProdiSerrin
#print axioms ESS.essSmooth
#print axioms ESS.serrinCriterion
LEAN
scripts/lean_direct.sh "$probe_dir/MainAxioms.lean" \
  -DautoImplicit=false -DwarningAsError=true
rm -rf -- "$probe_dir"
```

Each of the ten results should list exactly `[propext, Classical.choice, Quot.sound]`.
These are the standard logical axioms used by this formalization.

## Verify a fresh clone

`scripts/verify_fresh_clone.sh` creates a temporary clone, obtains the
dependency cache and runs the builds, local comparator checks, source checks,
axiom checks and the main-theorem probe above. Run the upstream Comparator
separately as described above. It uses `ESS_REPO_URL` when set, or the
configured `origin` remote. Use `--expected-sha SHA` to require a particular
commit, `--plan` to print the commands, or `--keep-on-failure` to retain a
failed checkout for inspection.

Compilation establishes that the proofs are accepted by Lean. Mathematical
review remains necessary to check that the formal statements and definitions
express the intended results.
