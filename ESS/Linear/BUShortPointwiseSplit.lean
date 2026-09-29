-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Linear.BUShortWideGap

/-!
# Pointwise split of the short-time cutoff error

The error is bounded by a fixed normal-phase polynomial on the
negative phase region and by radius-decaying shell terms elsewhere.
-/

@[expose] public section

set_option autoImplicit false

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The radius-dependent coefficient of the spatial shell error. -/
def buShortShellCoeff (scale R c₁ : ℝ) : ℝ :=
  (9 * (c₁ * scale) + 54) *
      (cutoffGradientConstant / (2 * R)) +
    3 * (cutoffSecondDerivativeConstant / (2 * R) ^ 2)

/-- The spatial shell coefficient is nonnegative. -/
theorem buShortShellCoeff_nonneg
    {scale R c₁ : ℝ} (hscale : 0 < scale)
    (hR : 0 < R) (hc₁ : 0 ≤ c₁) :
    0 ≤ buShortShellCoeff scale R c₁ := by
  have hG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hS : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  unfold buShortShellCoeff
  positivity

end ESS
