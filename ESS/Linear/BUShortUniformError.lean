-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Linear.BUShortUniformSizes

/-!
# Uniform short-time cutoff error bound

For radii at least one, the cutoff heat error has a fixed polynomial
height majorant and one explicit lower-time transition term.
-/

@[expose] public section

set_option autoImplicit false

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A radius-independent coefficient for the heat cutoff error. -/
def buShortUniformErrorCoeff (scale c₁ C₁ C₂ : ℝ) : ℝ :=
  (3 * (c₁ * scale) + 18) * buShortUniformGradientCoeff scale +
    buShortUniformHeatCoeff scale C₁ C₂

end ESS
