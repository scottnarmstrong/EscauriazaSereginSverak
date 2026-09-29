-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.LPS.SmoothingMollifierWeakContract
public import ESS.LPS.SmoothingMollifierKernel
public import CKN.Leray.RegularisedInitialData

/-!
# Regularized initial data in ordered Sobolev spaces

The physical regularization kernel contracts the integer Sobolev norm
of weak initial data, uniformly in its scale (`eq:lps-Hm-energy`).
-/

@[expose] public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace ESS

/-- The actual mollified initial state is smooth in space even when its
input is only in `J` (`thm:regularised` of the CKN manuscript). -/
theorem lps_regUniformMollifiedInitial_smooth
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : IsInJ a) :
    ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedInitial ρ ε hε a x i) := by
  obtain ⟨hκ, hκc, _, _⟩ :=
    lps_regUniformMollifierKernel_properties ρ ε hε
  intro i
  have hcomp :
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedInitial ρ ε hε a x i) =
        convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
          (fun x : Vec3 => a x i)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact CKN.Leray.regUniformMollifiedInitial_component_convolution
      ρ ε hε ha.1 x i
  rw [hcomp]
  exact hκc.contDiff_convolution_left (n := ⊤)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ
    ((ha.1.eval i).locallyIntegrable (by norm_num))

/-- The regularized initial state has no larger ordered `H^m` energy
than its specified weak Sobolev derivative family (`eq:lps-Hm-energy`). -/
theorem lps_regUniformMollifiedInitial_weak_sobolevNormSq_le
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : IsInJ a) {m : ℕ}
    {D : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hD : ∀ i : Fin 3,
      IsSobolevFamilyOn m univ (fun x => a x i) (D i)) :
    (∑ i : Fin 3, sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (fun x : Vec3 => CKN.Leray.regUniformMollifiedInitial ρ ε hε a x i))) ≤
      ∑ i : Fin 3, sobolevNormSqOn m univ (D i) := by
  obtain ⟨hκ, hκc, hκnonneg, hκone⟩ :=
    lps_regUniformMollifierKernel_properties ρ ε hε
  apply Finset.sum_le_sum
  intro i _
  have hcomp :
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedInitial ρ ε hε a x i) =
        convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
          (fun x : Vec3 => a x i)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact CKN.Leray.regUniformMollifiedInitial_component_convolution
      ρ ε hε ha.1 x i
  rw [hcomp]
  exact lps_sobolevNormSq_convolution_weak_input_le
    hκ hκc hκnonneg hκone (hD i)

end ESS
