-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RieszPressureSpaceTimeLp
public import CKN.Leray.RieszPressureSlices

/-!
# Pressure for a forced Stokes equation

The pressure of a tensor forcing is the negative of its canonical double
Riesz transform, as in `lem:pv-stokes`.
-/

@[expose] public section

open CKN

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace ESS

/-- The canonical pressure paired with a space-time tensor forcing. -/
def pvStokesPressure (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → CKN.Foundation.Parabolic.ParabolicPoint → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure CKN.Foundation.Parabolic.ParabolicPoint)) :
    CKN.Foundation.Parabolic.ParabolicPoint → ℝ :=
  -CKN.Leray.rieszPressureSpaceTime r hr F hF

end ESS

end
