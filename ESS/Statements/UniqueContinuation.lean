-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Main.UniqueContinuation
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

/-- Unique continuation across spatial boundaries (`thm:uc`; ESS Theorem 4.1). -/
theorem uniqueContinuation (R T c₁ : ℝ) (hR : 0 < R) (hT : 0 < T) (hc₁ : 0 < c₁)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (vec3Ball 0 R ×ˢ Ico 0 T))
    (hderiv : HasSpaceTimeWeakDerivs (vec3Ball 0 R) (Ioo 0 T) w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (vec3Ball 0 R) (Ioo 0 T))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)))
    (hvanish : ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
      vec3EuclideanNorm (w z) ≤ C * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k) :
    ∀ x ∈ vec3Ball 0 R, w (x, 0) = 0 :=
by exact ESS.Main.uniqueContinuation R T c₁ hR hT hc₁ w Dw D2w Dtw hcont hderiv hL2 hineq hvanish

end ESS
