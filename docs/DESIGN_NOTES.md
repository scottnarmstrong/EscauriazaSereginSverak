# Design notes

These notes explain the representation choices behind the Lean statements.
They build on the conventions of the published Caffarelli–Kohn–Nirenberg
formalization (its `docs/DESIGN_NOTES.md`), which is a pinned Lake dependency and now includes the Leray background transferred from this development. The notes on that background below explain the setting of the ESS results; the CKN repository documents it
in full. Manuscript labels refer to `paper/ess.tex`.

## Carriers and primitives

Space is `Vec3 = Fin 3 → ℝ` and spacetime `ParabolicPoint = Vec3 × ℝ`, as in
CKN. A velocity is `u : ParabolicPoint → Vec3`, its weak spatial gradient is
explicit data `Du : ParabolicPoint → Fin 3 → Vec3` with `Du z i j = ∂ⱼuᵢ`, and
a pressure is `p : ParabolicPoint → ℝ`. The CKN primitives (`spaceTimeSet`,
`spaceTimeTestFunction`, `spatialPartial`, `timePartial`,
`spatialSecondPartial`, `spatialGradientSq`, `vec3EuclideanNorm`,
`vec3Ball`, `parabolicCylinder`, `HasWeakGradientOn`, `IsRegularPoint`,
`SingularSet`, `ParabolicHolderVecOn`) are reused unchanged.

Quantitative statements use Euclidean norms (`vec3EuclideanNorm`,
`spatialGradientSq`). Finiteness conditions may use the ambient ENNReal norm
`‖·‖ₑ`, which on these finite-dimensional carriers is equivalent. Masses and
essential suprema are compared in `ℝ≥0∞`, so no infinite quantity is ever
converted to a real number.

## The representative of a Leray–Hopf solution

A Leray–Hopf solution (`def:leray-hopf`, (1.3)–(1.7) of ESS) constrains its
velocity at **every** time:
- weak continuity (1.4) holds on the closed interval [0, T];
- the energy inequality (1.6) holds at every t₀ ∈ [0, T];
- the initial datum is attained in L² as t ↓ 0.

The velocity is therefore a function defined at every point, and the
predicate (`CKN.IsLerayHopfSolution`) is about that function, not an
almost-everywhere class. CKN's suitable weak-solution class is insensitive to
modifications on null sets. The existence theorem `CKN.leray_existence`
asserts both properties for **the same** function u (its construction is in
the CKN library and paper). Every theorem that passes between the two notions
(existence, the associated pressure, ESS Theorem 1.3) works with this one
function.

## Domains

The global statements use space `Set.univ` and time `Set.Ioi 0` (existence)
or `Set.Ioo 0 T` (associated pressure, ESS Theorem 1.3; the existence theorems are in CKN). Both are open and
order-connected, as CKN's class requires.

The one exception is ESS Theorem 1.4 (`thm:ess-local`), which is a local
theorem on the cylinder B₁ × (−1, 0). The source states it there, its
conclusion concerns the closure of B_{1/2} × (−1/4, 0), and it is applied
to rescaled cylinders around each point. It is stated with `vec3Ball 0 1`
and `Set.Ioo (-1) 0`.

## Global Leray–Hopf solutions

A global solution is a Leray–Hopf solution on every finite interval
[0, T] (`rem:global-LH`). Read literally with [0, ∞[, ESS (1.3) would require
∫₀^∞ ∫ |u|² < ∞, which Leray's solutions need not satisfy.

## The Sobolev class of the linear uniqueness theorems

ESS Theorems 4.1 and 5.1 are stated for W^{2,1}_2 fields. The Lean statements
carry the space-time weak derivatives as explicit data
(`CKN.HasSpaceTimeWeakDerivs`) and ask for the field itself to be continuous up
to the time slice at which a value is evaluated. This continuity is the trace
convention that the source leaves unspecified. The class is not narrowed to
C^{2,1}: a suitable solution can be discontinuous in time through a harmonic
pressure mode, and the vorticity then need not have a continuous time
derivative.
