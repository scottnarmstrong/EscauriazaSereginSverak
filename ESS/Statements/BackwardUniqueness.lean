-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Main.BackwardUniqueness
public import CKN.Statements.HasSpaceTimeWeakDerivs
public import CKN.Statements.SpaceTimeSet
public import CKN.Statements.SpaceTimeTestFunction
public import CKN.Statements.SpatialPartial
public import CKN.Statements.SpatialSecondPartial
public import CKN.Statements.TimePartial
public import CKN.Statements.SpatialGradient
public import CKN.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace ESS

/-- Backward uniqueness on a half-space (`thm:bu`; ESS Theorem 5.1). -/
theorem backwardUniqueness (c₁ M : ℝ) (hc₁ : 0 < c₁) (hM : 0 < M)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1), w z = 0 :=
by exact ESS.Main.backwardUniqueness c₁ M hc₁ hM w Dw D2w Dtw hcont hinit hderiv hL2 hineq hgrowth

end ESS
