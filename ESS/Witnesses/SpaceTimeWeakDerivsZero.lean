-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.HasSpaceTimeWeakDerivs

/-!
# The zero field has space-time weak derivatives

The predicate `CKN.HasSpaceTimeWeakDerivs` (manuscript §2, space-time weak
derivatives) is satisfied by the zero field with zero derivative data, on any
spatial set and time set.
-/

@[expose] public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

namespace ESS

/-- The zero field and zero derivative data satisfy `HasSpaceTimeWeakDerivs`. -/
theorem hasSpaceTimeWeakDerivs_zero (Ω : Set Vec3) (I : Set ℝ) :
    HasSpaceTimeWeakDerivs Ω I (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, locallyIntegrableOn_zero,
    locallyIntegrableOn_zero, fun φ _ => ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩⟩ <;>
    simp

end ESS
