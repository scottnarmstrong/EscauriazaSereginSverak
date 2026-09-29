# Independent statements and proof comparison

The ten main theorems of this library are restated in two independent pairs
of files, one pair per topic. (The Leray theorems are in the CKN library,
which carries its own comparator pair.)

| Directory | Topic | Theorems |
|---|---|---|
| [`Linear`](Linear) | unique continuation, backward uniqueness, Carleman inequalities | 4 |
| [`Regularity`](Regularity) | local and global regularity, $L^5$ and uniqueness, Ladyzhenskaya–Prodi–Serrin, smoothness, combined criterion | 6 |

Each directory contains `Challenge.lean`, `Solution.lean` and
`comparator.json`.

## The Challenge

`<Topic>/Challenge.lean` imports **only Mathlib** and defines every notion it
uses from Mathlib definitions: three-dimensional space is
`EuclideanSpace ℝ (Fin 3)`, derivatives are `fderiv` and weak derivatives
defined against smooth compactly supported test functions, space-time
integrals use Mathlib's Lebesgue measure, and
Hölder regularity is measured in the ordinary metric. It then states the
theorems in the namespace `ESSChallenge`, each with one intentional `sorry`.
A reader can compare a Challenge with the manuscript without reading the
proof library. Each Challenge is below the 1,000-line and 100-KiB limits.

## The Solution

`<Topic>/Solution.lean` contains the same definitions and the same statements
and proves them from the library's main theorems in `ESS/Statements`. The
library uses its own representation (`Vec3 = Fin 3 → ℝ`, explicit weak
gradients, parabolic geometry); the Solution proves transport lemmas between
that representation and the Mathlib-native one, and then applies the
theorem. It does not import the Challenge. Challenge and Solution are
separate Lean environments: importing both into one file would create
duplicate declarations.

## Correspondence

| Challenge declaration (`ESSChallenge.`) | Library theorem | Statement file |
|---|---|---|
| `Linear`: `uniqueContinuation` | `ESS.uniqueContinuation` | [`UniqueContinuation.lean`](../ESS/Statements/UniqueContinuation.lean) |
| `Linear`: `backwardUniqueness` | `ESS.backwardUniqueness` | [`BackwardUniqueness.lean`](../ESS/Statements/BackwardUniqueness.lean) |
| `Linear`: `carlemanGaussian` | `ESS.carlemanGaussian` | [`CarlemanGaussian.lean`](../ESS/Statements/CarlemanGaussian.lean) |
| `Linear`: `carlemanHalfSpace` | `ESS.carlemanHalfSpace` | [`CarlemanHalfSpace.lean`](../ESS/Statements/CarlemanHalfSpace.lean) |
| `Regularity`: `essLocal` | `ESS.essLocal` | [`EssLocal.lean`](../ESS/Statements/EssLocal.lean) |
| `Regularity`: `essGlobal` | `ESS.essGlobal` | [`EssGlobal.lean`](../ESS/Statements/EssGlobal.lean) |
| `Regularity`: `essL5Unique` | `ESS.essL5Unique` | [`EssL5Unique.lean`](../ESS/Statements/EssL5Unique.lean) |
| `Regularity`: `ladyzhenskayaProdiSerrin` | `ESS.ladyzhenskayaProdiSerrin` | [`LadyzhenskayaProdiSerrin.lean`](../ESS/Statements/LadyzhenskayaProdiSerrin.lean) |
| `Regularity`: `essSmooth` | `ESS.essSmooth` | [`EssSmooth.lean`](../ESS/Statements/EssSmooth.lean) |
| `Regularity`: `serrinCriterion` | `ESS.serrinCriterion` | [`SerrinCriterion.lean`](../ESS/Statements/SerrinCriterion.lean) |

These are all ten main theorems of this library.

## Local checks

After building the library and the comparator targets, run from the
repository root:

```sh
python3 scripts/build.py Comparators
python3 scripts/check_comparators.py
```

This checks both pairs. `--topic <Name>` (`Linear` or `Regularity`) checks one pair; `--no-build` performs the source checks only;
`--lake` additionally builds the target. The checker rejects any non-Mathlib
import in a Challenge, compares the definitions and theorem statements shared
by Challenge and Solution, checks that each Challenge has exactly one
intentional `sorry` per theorem, requires a clean Solution elaboration with
warnings treated as errors, and requires exactly
`[propext, Classical.choice, Quot.sound]` as the axiom set of each solution.

## Upstream Comparator and NanoDa

```sh
scripts/verify_comparator.sh
```

The script builds pinned revisions of
[Comparator](https://github.com/leanprover/comparator),
[lean4export](https://github.com/leanprover/lean4export),
[NanoDa](https://github.com/robsimmons/nanoda_lib) and
[Landrun](https://github.com/zouuup/landrun) in a user cache, then runs
Comparator on every `comparators/*/comparator.json`. It requires Linux with
Landlock support, Go 1.24 or later, Rust/Cargo, Git, Python 3 and the
project's Lean toolchain. Comparator checks the exported statement dependency
closures, the permitted axioms and the proofs; NanoDa independently replays
each exported Solution in a second kernel.

Neither check establishes that the definitions express the intended
mathematics; that requires review of the Challenge against the manuscript.
The departures of the Challenge notions from the manuscript's are recorded in
[DEVIATIONS](../docs/DEVIATIONS.md).
