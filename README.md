# The Escauriaza–Seregin–Šverák theorem, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/EscauriazaSereginSverak/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/EscauriazaSereginSverak/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/EscauriazaSereginSverak/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/EscauriazaSereginSverak/actions/workflows/comparators.yml)

A complete, machine-checked proof of the Escauriaza–Seregin–Šverák theorem
for the three-dimensional incompressible Navier–Stokes equations on
$\mathbb{R}^3$, together with the Ladyzhenskaya–Prodi–Serrin theorem:

- **The Escauriaza–Seregin–Šverák theorem.** A Leray–Hopf solution whose
  velocity is bounded in $L^\infty(0,T;L^3(\mathbb{R}^3))$ has no singular
  points, belongs to $L^5(\mathbb{R}^3\times(0,T))$, is the only
  Leray–Hopf solution with its initial datum, and is smooth on
  $\mathbb{R}^3\times(0,T]$. This is Theorem 1.3 of the paper in full.
- **The Ladyzhenskaya–Prodi–Serrin theorem.** A Leray–Hopf solution on
  $[0,T]$ that lies in $L^\ell(0,T;L^s(\mathbb{R}^3))$ with
  $3/s+2/\ell=1$ and $3<s\le\infty$ is the only Leray–Hopf solution with its
  initial datum and agrees almost everywhere with a function that is
  $C^\infty$ on $\mathbb{R}^3\times(0,T]$ (one-sided at $T$).
- **The regularity criterion for $3\le s\le\infty$.** The two theorems
  combined: a Leray–Hopf solution in $L^\infty(0,T;L^3)$, in
  $L^\ell(0,T;L^s)$ with $3<s<\infty$ and $\ell=2s/(s-3)$, or in
  $L^2(0,T;L^\infty)$ is unique and has a $C^\infty$ representative on
  $\mathbb{R}^3\times(0,T]$.

The formalization is written in Lean 4 on top of Mathlib and of the
[Caffarelli–Kohn–Nirenberg formalization](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)
(CKN below). CKN supplies the setting: suitable weak solutions and regular
points, Leray–Hopf solutions, Leray's global existence theorem in suitable
form, the associated pressure, and the Caffarelli–Kohn–Nirenberg theorems.
This project proves the rest of the argument: the local regularity theorem
and its blow-up proof, the Carleman inequalities, unique continuation and
backward uniqueness, the $L^5$ and uniqueness theorem, and the
Ladyzhenskaya–Prodi–Serrin uniqueness and smoothing theorem. The library uses
no axioms beyond Lean's standard three and contains no unfinished proofs.

The proof is written out in full in the accompanying
[manuscript](paper/ess.pdf) ([source](paper/ess.tex)). The manuscript and the
Lean development were produced together: the main theorems are stated in Lean
with the manuscript's hypotheses and conclusions, and the manuscript was
corrected as the formalization progressed.

## Results formalized

- **L. Escauriaza, G. A. Seregin and V. Šverák, "$L_{3,\infty}$-solutions of
  Navier–Stokes equations and backward uniqueness", *Russian Math. Surveys*
  58:2 (2003), 211–250.** Formalized, with the paper's numbering:
  - Theorem 1.4 (local regularity: a solution in $L^\infty L^3$ on the unit
    cylinder is Hölder continuous on the closure of the half cylinder);
  - Theorem 1.3 (a Leray–Hopf solution in $L^\infty(0,T;L^3)$ belongs to
    $L^5$, is unique among Leray–Hopf solutions with its datum, and is
    smooth on $\mathbb{R}^3\times(0,T]$), in full;
  - Theorem 1.2 (the Ladyzhenskaya–Prodi–Serrin theorem, see the next
    item), in the whole-space form used for Theorem 1.3;
  - Theorem 4.1 (unique continuation across spatial boundaries);
  - Theorem 5.1 (backward uniqueness for the heat operator with lower-order
    terms on a half-space), in dimension three;
  - Propositions 6.1 and 6.2 (the Carleman inequalities (6.1) and (6.12)).

  The paper's Theorem 1.1 (existence of suitable Leray–Hopf solutions) and
  the associated pressure used in its §3 are taken from CKN, where the
  pressure is constructed by Riesz transforms.
- **The Ladyzhenskaya–Prodi–Serrin theorem.** G. Prodi, "Un teorema di
  unicità per le equazioni di Navier–Stokes", *Ann. Mat. Pura Appl.* (4) 48
  (1959), 173–182; J. Serrin, "The initial value problem for the
  Navier–Stokes equations", in *Nonlinear Problems* (R. E. Langer, ed.),
  Univ. of Wisconsin Press, Madison, 1963, 69–98 (and, for interior
  regularity, *Arch. Rational Mech. Anal.* 9 (1962), 187–195); O. A.
  Ladyzhenskaya, "On uniqueness and smoothness of generalized solutions to the
  Navier–Stokes equations", *Zap. Nauchn. Sem. LOMI* 5 (1967), 169–185.
  Formalized in the whole-space form of Theorem 1.2 of Escauriaza, Seregin and
  Šverák, following J. C. Robinson, J. L. Rodrigo and W. Sadowski, *The
  Three-Dimensional Navier–Stokes Equations* (CUP, 2016), Theorems 8.17 and
  8.19, for the whole range $3<s\le\infty$ (with $\ell=2s/(s-3)$, and
  $L^2(0,T;L^\infty)$ at $s=\infty$). Together with the
  Escauriaza–Seregin–Šverák theorem, which is the case $s=3$, it gives the
  regularity criterion for $3\le s\le\infty$.
- **L. Escauriaza, G. A. Seregin and V. Šverák, "Backward uniqueness for
  the heat operator in half-space", *Algebra i Analiz* 15:1 (2003), 201–214;
  English translation in *St. Petersburg Math. J.* 15 (2004), 139–148.** This
  paper concerns the same half-space backward-uniqueness problem, whose
  theorem appears with its proof as Theorem 5.1 of the paper above. The
  formalization follows the *Russian Math. Surveys* paper; it has not been
  compared line by line with this one.

Not formalized:

- the exterior-domain backward uniqueness theorem of L. Escauriaza,
  G. A. Seregin and V. Šverák, "Backward uniqueness for parabolic equations",
  *Arch. Ration. Mech. Anal.* 169 (2003), 147–157, which the half-space
  theorem extends;
- the general Carleman and unique-continuation theory of L. Escauriaza
  (*Duke Math. J.*, 2000) and L. Escauriaza and F. J. Fernández (*Ark. Mat.*,
  2003) beyond the statements listed above.

## Sources

- L. Escauriaza, G. A. Seregin and V. Šverák, "$L_{3,\infty}$-solutions of
  Navier–Stokes equations and backward uniqueness", *Russian Math. Surveys*
  58:2 (2003), 211–250.
- J. C. Robinson, J. L. Rodrigo and W. Sadowski, *The Three-Dimensional
  Navier–Stokes Equations: Classical Theory*, Cambridge Studies in Advanced
  Mathematics 157, CUP (2016).
- G. Prodi, "Un teorema di unicità per le equazioni di Navier–Stokes", *Ann.
  Mat. Pura Appl.* (4) 48 (1959), 173–182.
- J. Serrin, "On the interior regularity of weak solutions of the
  Navier–Stokes equations", *Arch. Rational Mech. Anal.* 9 (1962), 187–195,
  and "The initial value problem for the Navier–Stokes equations", in
  *Nonlinear Problems* (R. E. Langer, ed.), Univ. of Wisconsin Press (1963),
  69–98.
- O. A. Ladyzhenskaya, "On uniqueness and smoothness of generalized solutions
  to the Navier–Stokes equations", *Zap. Nauchn. Sem. LOMI* 5 (1967),
  169–185.
- J. Leray, "Sur le mouvement d'un liquide visqueux emplissant l'espace",
  *Acta Math.* 63 (1934), 193–248.
- L. Caffarelli, R. Kohn and L. Nirenberg, "Partial regularity of suitable
  weak solutions of the Navier–Stokes equations", *Comm. Pure Appl. Math.* 35
  (1982), 771–831.
- P. G. Lemarié-Rieusset, *The Navier–Stokes Problem in the 21st Century*,
  CRC Press (2016).
- S. Armstrong and V. Vicol, *The Caffarelli–Kohn–Nirenberg theorem,
  formalized in Lean 4* (2026),
  [github.com/scottnarmstrong/CaffarelliKohnNirenberg](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg).

The [sources](docs/SOURCES.md) page gives the full bibliography with DOIs and
says what each work is used for.

## What is proved

Space is $\mathbb{R}^3$ and time is $\mathbb{R}$. The space $J$ of initial
data is the $L^2$ closure of smooth, compactly supported, divergence-free
vector fields. A Leray–Hopf solution on $[0,T]$ with datum $a\in J$
(Definition 3.3 of the manuscript) is a velocity $u$ with an explicit weak
spatial gradient $Du$ that has finite energy and dissipation, is weakly
divergence free, is weakly continuous in time on the closed interval,
satisfies the weak Navier–Stokes equation against divergence-free tests,
satisfies the energy inequality at every time, and converges to $a$ in $L^2$
as $t\downarrow 0$. These definitions, like suitable weak solutions, regular
points and singular points, are those of CKN, which also proves that every
$a\in J$ has a global Leray–Hopf solution that is suitable
(`CKN.leray_existence`).

**Local regularity** (Theorem 3.12 of the manuscript; Theorem 1.4 of
Escauriaza, Seregin and Šverák). If $u$, $Du$ and $p$ on $B_1\times(-1,0)$
have finite energy, $p\in L^{3/2}$, $u\in L^\infty(-1,0;L^3(B_1))$, and
satisfy the divergence-free condition and the momentum equation weakly (no
energy inequality is assumed), then $u$ agrees almost everywhere on
$B_{1/2}\times(-1/4,0)$ with a parabolically Hölder continuous function on
the closure of that cylinder.

**Global regularity, $L^5$ and uniqueness** (Theorems 3.13 and 16.3; Theorem
1.3 of Escauriaza, Seregin and Šverák). If $(u,Du)$ is a Leray–Hopf solution
on $[0,T]$ and $\operatorname{ess\,sup}_{t\in(0,T)}\|u(\cdot,t)\|_{L^3}<\infty$,
then $u$ has no singular point in $\mathbb{R}^3\times(0,T)$,
$u\in L^5(\mathbb{R}^3\times(0,T))$, and every Leray–Hopf solution on
$[0,T]$ with the same datum equals $u$ almost everywhere.

**Ladyzhenskaya–Prodi–Serrin** (Theorem 17.1 and Corollary 17.2; Theorems 1.2
and 1.3 of Escauriaza, Seregin and Šverák). If $(u,Du)$ is a Leray–Hopf
solution on $[0,T]$ with datum $a$ and either
$u\in L^{\ell}(0,T;L^s(\mathbb{R}^3))$ with $3<s<\infty$ and
$\ell=2s/(s-3)$, or $u\in L^2(0,T;L^\infty(\mathbb{R}^3))$, then every
Leray–Hopf solution on $[0,T]$ with datum $a$ equals $u$ almost everywhere,
and $u$ agrees almost everywhere with a function that is $C^\infty$ on
$\mathbb{R}^3\times(0,T]$, with derivatives at $T$ taken within that set.
Consequently a Leray–Hopf solution with
$\operatorname{ess\,sup}_t\|u(t)\|_{L^3}<\infty$ lies in $L^5$, is unique
and is smooth in this sense; this is Theorem 1.3 of Escauriaza, Seregin and
Šverák in full. Equality of solutions is almost everywhere, since the
prescribed time slices of a Leray–Hopf solution need not agree at every
point.

**Regularity criterion** (Corollary 17.3). If $(u,Du)$ is a Leray–Hopf
solution on $[0,T]$ with datum $a$ and $u$ lies in $L^\infty(0,T;L^3)$, or
in $L^\ell(0,T;L^s)$ with $3<s<\infty$ and $\ell=2s/(s-3)$, or in
$L^2(0,T;L^\infty)$, then $u$ is the only Leray–Hopf solution on $[0,T]$
with datum $a$ (almost everywhere) and agrees almost everywhere with a
function that is $C^\infty$ on $\mathbb{R}^3\times(0,T]$, one-sided at $T$.

**Linear continuation** (Propositions 4.1 and 4.2, Theorems 5.2 and 6.7;
Propositions 6.1 and 6.2 and Theorems 4.1 and 5.1 of Escauriaza, Seregin and
Šverák). Unique continuation across a spatial boundary and backward
uniqueness on a half-space for vector fields satisfying the differential
inequality $|\partial_t w+\Delta w|\le c_1(|\nabla w|+|w|)$, and the two
Carleman inequalities behind them. They are stated for fields with explicit
space-time weak derivatives in the class $W^{2,1}_2$, which is the regularity
available when they are applied to the vorticity of a suitable weak
solution.

## The Lean statements

The main statements are in [ESS/Statements](ESS/Statements), one declaration
per file; their proofs are assembled in [ESS/Main](ESS/Main). As in CKN,
`Vec3` is `Fin 3 → ℝ`, a `ParabolicPoint` is a pair of a point and a time,
and the weak spatial gradient `Du` is explicit data with `Du z i j` the
derivative $\partial_j u_i$. The definitions `IsLerayHopfSolution`,
`SingularSet` and `parabolicHausdorffMeasure` are those of
[CKN](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/tree/main/CKN/Statements).
The [design notes](docs/DESIGN_NOTES.md) explain the choices behind them.

Global regularity, [`ESS.essGlobal`](ESS/Statements/EssGlobal.lean):

```lean
theorem essGlobal :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      SingularSet (Set.univ : Set Vec3) (Ioo 0 T) u = ∅
```

$L^5$ and uniqueness, [`ESS.essL5Unique`](ESS/Statements/EssL5Unique.lean):

```lean
theorem essL5Unique :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      MemLp u (ENNReal.ofReal (5 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u
```

Ladyzhenskaya–Prodi–Serrin,
[`ESS.ladyzhenskayaProdiSerrin`](ESS/Statements/LadyzhenskayaProdiSerrin.lean)
(the hypothesis is the Serrin condition, a disjunction of the finite-$s$ mixed
norm with $\ell=2s/(s-3)$ and the $L^2_tL^\infty_x$ endpoint; the smooth
representative is a function $\text{uSmooth}$ with
`ContDiffOn ℝ (⊤ : ℕ∞)` on `univ ×ˢ Ioc 0 T`):

```lean
theorem ladyzhenskayaProdiSerrin :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ((∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
                ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup
            (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
            (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) →
      (∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u) ∧
      (∃ uSmooth : ParabolicPoint → Vec3,
        uSmooth =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T))
```

The corollary [`ESS.essSmooth`](ESS/Statements/EssSmooth.lean) has the
hypothesis of `essL5Unique` and concludes with the $L^5$ membership, the
uniqueness clause and the smooth representative of the previous statement:

```lean
theorem essSmooth :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      MemLp u (ENNReal.ofReal (5 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u) ∧
      (∃ uSmooth : ParabolicPoint → Vec3,
        uSmooth =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T))
```

The combined criterion for $3\le s\le\infty$,
[`ESS.serrinCriterion`](ESS/Statements/SerrinCriterion.lean):

```lean
theorem serrinCriterion :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ((essSup
          (fun t : ℝ => ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤) ∨
        (∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
                ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup
            (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
            (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) →
      (∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u) ∧
      (∃ uSmooth : ParabolicPoint → Vec3,
        uSmooth =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T))
```

The remaining main theorems are stated in the same directory:

| Manuscript | Lean declaration |
|---|---|
| Theorem 3.12 (local regularity) | [`ESS.essLocal`](ESS/Statements/EssLocal.lean) |
| Theorem 5.2 (unique continuation) | [`ESS.uniqueContinuation`](ESS/Statements/UniqueContinuation.lean) |
| Theorem 6.7 (backward uniqueness) | [`ESS.backwardUniqueness`](ESS/Statements/BackwardUniqueness.lean) |
| Proposition 4.1 (Gaussian Carleman inequality) | [`ESS.carlemanGaussian`](ESS/Statements/CarlemanGaussian.lean) |
| Proposition 4.2 (half-space Carleman inequality) | [`ESS.carlemanHalfSpace`](ESS/Statements/CarlemanHalfSpace.lean) |

Together with `essGlobal`, `essL5Unique`, `ladyzhenskayaProdiSerrin`,
`essSmooth` and `serrinCriterion` above, these are the ten main theorems.

Because a formal statement is only as good as the definitions inside it,
the repository also contains two independent Challenge/Solution pairs in
[comparators](comparators/README.md): `Linear` (unique continuation, backward
uniqueness and the two Carleman inequalities) and `Regularity` (`essLocal`,
`essGlobal`, `essL5Unique`, `ladyzhenskayaProdiSerrin`, `essSmooth` and
`serrinCriterion`). Each Challenge imports only Mathlib and defines every
notion it uses from Mathlib (`EuclideanSpace ℝ (Fin 3)`, `fderiv`, Mathlib
measures), so it can be read without reading this library or CKN; it states
its theorems in the namespace `ESSChallenge` with one intentional proof
placeholder each. The corresponding Solution proves the identical statements
from the library, with transport lemmas between the Mathlib-native notions
and the library's. [Comparator](comparators/README.md) checks their
statement dependency closures and proofs, including an independent NanoDa
kernel replay. Reading the Challenges is the quickest way to inspect the
precise mathematical claims.

## How the formalization relates to the manuscript and to CKN

The manuscript is the paper being formalized, not a description written
after the fact. Where it departs from the published sources it says so in a
remark next to the result concerned; the [deviations](docs/DEVIATIONS.md)
document collects these departures. Examples are the finite vorticity
bootstrap that replaces all-orders Stokes estimates in the blow-up argument,
the manuscript's own proof of the short-time $L^5$ bound, and, for the
Ladyzhenskaya–Prodi–Serrin theorem, an energy equality proved almost
everywhere in time from the Serrin condition and a smoothing argument by a
regularity ladder.

The solution classes are CKN's. A Leray–Hopf solution is one specified
function whose every time slice is constrained, and the same function is the
suitable weak solution to which the Caffarelli–Kohn–Nirenberg theorems
apply; the local regularity proof uses CKN's Theorem A, as the
[design notes](docs/DESIGN_NOTES.md) explain. The repository also contains
explicit examples showing that the definitions used in the statements are
inhabited; the [witnesses](docs/WITNESSES.md) page lists them.

## Building and checking it yourself

The project pins Lean 4 and Mathlib at v4.35.0-rc2 and CKN at the exact
commit `381d658ead0f03a18361965cc0427ce3fa5844ab`. With `elan` and Python 3 installed:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
ESS_IGNORE_PACKAGE_BUILD=1 python3 scripts/build.py ESS
```

The library contains about 205,000 lines of Lean (1,008 files). The Mathlib
cache does not include CKN, so the first build compiles it from source as well
(about 410,000 further lines); `ESS_IGNORE_PACKAGE_BUILD=1` lets the build
create CKN's compiled files, while the build script still checks that the
sources of CKN and Mathlib are unchanged. Build time depends on the machine. Keep the
committed dependency manifest; avoid `lake update` or `lake clean` when
verifying this version.

To confirm the axioms used by the main theorems, or to run the source and
comparator checks, follow the [verification guide](docs/VERIFICATION.md).
Each of the ten main theorems depends exactly on `propext`,
`Classical.choice` and `Quot.sound`.

## Repository layout

- [ESS/Statements](ESS/Statements): the ten main theorem statements, one declaration per file.
- [ESS/Main](ESS/Main): the assembly of each main theorem from its proof.
- [ESS/Linear](ESS/Linear): the Carleman inequalities, unique continuation and backward uniqueness (Part I of the manuscript).
- [ESS/Endpoint](ESS/Endpoint): the local energy equality, the smallness criterion, the blow-up argument, the vorticity bootstrap and the proofs of the local and global regularity theorems (Part IV).
- [ESS/PartV](ESS/PartV): the short-time $L^5$ solution, the heat and Stokes estimates, and weak–strong uniqueness (Part V).
- [ESS/LPS](ESS/LPS): Serrin mixed norms, the energy equality under the Serrin condition, the local strong solution, the $H^1$ estimate and continuation, general-exponent uniqueness and smoothing up to the final time (Part VI).
- [ESS/Witnesses](ESS/Witnesses): explicit examples showing the definitions are inhabited.
- [comparators](comparators): the two Mathlib-only Challenge/Solution pairs described above.
- [paper](paper): the manuscript source and PDF.
- [docs](docs): design notes, deviations, witnesses, verification guide, and the [bibliography](docs/SOURCES.md).
- [scripts](scripts): the guarded build, checking, comparison, and release-verification tools.

## How this was made

The Lean development was written between 2026-09-26 and 2026-09-29 using AI
coding agents under the author's supervision. Claude Opus 5.5 coordinated
agents using GPT-6 Luna, GPT-6 Sol and Claude Sonnet 5.5. The author reviewed
the theorem statements before proof development and decided the mathematics
and the corrections to the manuscript. Separate reviews checked the statements
and the use of intermediate results in the main proofs. Lean checks the
proofs; the comparator files make their mathematical statements available for
independent inspection.

## Contributing, author and license

See [Contributing](CONTRIBUTING.md) for the source rules and checks, and
[CITATION.cff](CITATION.cff) for how to cite this work.

The Lean development is by:

- **Scott Armstrong**, CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute School of Mathematics, Computing, and Data
  Science, New York University. Supported by the European Research Council
  under the European Union's Horizon Europe programme, grant agreement
  No. 101200828.

The Lean library, software, documentation and included manuscript are
copyright © 2026 Scott Armstrong and distributed under the
[Apache License 2.0](LICENSE). Cited third-party works and dependencies retain
their own licenses.
