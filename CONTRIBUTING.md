# Contributing

This repository formalizes the Escauriaza–Seregin–Šverák theorem and the
Ladyzhenskaya–Prodi–Serrin theorem in Lean 4 (using Lean's module system)
and Mathlib, on top of the published Caffarelli–Kohn–Nirenberg (CKN)
formalization, which contains Leray's global existence theorem and the
Leray–Hopf definitions. The main theorem statements are in [ESS/Statements](ESS/Statements)
and their proofs are assembled in [ESS/Main](ESS/Main).

## Development environment

Install the pinned toolchain and obtain the Mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
```

Keep the committed `lake-manifest.json`. Avoid `lake update` and `lake clean`
when verifying this version: they can change dependencies or remove the cache.
The build scripts check the toolchain, the Mathlib and CKN revisions and the
dependency package files.

CKN is consumed only as a Lake dependency. Do not copy CKN files into this
repository or edit `.lake/packages/`; a missing CKN lemma is proved here
under the `ESS` namespace, and changes to the moved Leray background belong in
the CKN repository.

## Lean source conventions

Every Lean file begins with:

```lean
-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.
```

Use `set_option autoImplicit false`. Library code must contain no `sorry`,
`admit`, `sorryAx`, or custom axiom declarations. The only exceptions are the
deliberately unproved comparator Challenge statements
(`comparators/<Topic>/Challenge.lean`), whose separate Solution files provide
the proofs.

Space is `Vec3 = Fin 3 → ℝ` and space-time is `ParabolicPoint = Vec3 × ℝ`,
as in CKN; reuse CKN's primitives rather than redefining them, and do not
state library results over `EuclideanSpace`. The comparator Challenges are the
exception: they import only Mathlib and use its native notions, with the
transport to `Vec3` proved in the Solutions. Do not add heartbeat overrides or use
bare `linarith` or `nlinarith`; use explicit `only` arguments. Library Lean files
must remain at most 1,500 lines. Comparator Challenges must remain at most 1,000 lines and 100 KiB; comparator Solutions must remain at most 10,000 lines. The library builds with warnings treated as
errors. Docstrings cite the manuscript by its LaTeX labels, such as
`thm:ess-local`, never by line numbers or file paths.

## Building and checking changes

From the repository root:

```sh
python3 scripts/build.py ESS
python3 scripts/build.py Comparators
python3 scripts/check_comparators.py
python3 scripts/check_public.py
python3 scripts/check_axioms.py
```

The build runs the source-rule and duplicate-declaration checks first. Add
new modules to `ESS.lean` and to Git before building; `check_public.py`
rejects a module that `ESS.lean` does not import. The
[verification guide](docs/VERIFICATION.md) explains each check.

For a focused check after building the file's imports:

```sh
scripts/lean_direct.sh ESS/Statements/EssGlobal.lean \
  -DautoImplicit=false -DwarningAsError=true
```

Changes to the main statements or their definitions need mathematical review
against the manuscript. Update the [comparator pairs](comparators/README.md)
(`comparators/{Linear,Regularity}`) together with any changed statements
and rerun both the local checks (`python3 scripts/check_comparators.py`, or
`--topic <Name>` for one pair) and the upstream Comparator
(`scripts/verify_comparator.sh`). A Challenge may import only Mathlib.

## Submitting a change

Describe the mathematical or implementation change and include the relevant
build and checker results. For a new public theorem, include its
`#print axioms` output. Keep generated build files and temporary probes out
of the commit.
