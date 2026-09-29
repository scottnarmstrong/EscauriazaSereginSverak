-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.LPS.SmoothingSobolevAlgebra

/-!
# All-order smooth product integrability

The integer Sobolev algebra estimate gives square integrability for
every ordered derivative of a product when both factors have it.
-/

@[expose] public section

open CKN

open MeasureTheory
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace ESS

/-- Products of smooth fields with all ordered derivatives in `L²`
retain that property (`eq:lps-regularized-Hm-identity`). -/
theorem lps_smooth_product_all_word_memLp
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (hgL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α g) 2 volume)
    (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x => f x * g x)) 2 volume := by
  let m := max 2 α.length
  have hm : 2 ≤ m := le_max_left _ _
  obtain ⟨_, _, hprod⟩ := lps_smooth_product_normSq m hm
  exact (hprod f g hf hg
    (fun β _ => hfL2 β) (fun β _ => hgL2 β)).1 α
      (le_max_right _ _)

end ESS
