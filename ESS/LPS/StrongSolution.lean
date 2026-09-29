-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.HasSpaceTimeWeakDerivs
public import CKN.Statements.IsInJ
public import CKN.Foundation.Sobolev.H1.Basic
public import CKN.Statements.SpaceTimeSet
public import CKN.Statements.SpaceTimeTestFunction
public import CKN.Statements.SpatialPartial
public import CKN.Statements.TimePartial
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Strong Navier–Stokes solutions on a closed time interval

The class records the `C_tH¹ ∩ L²_tH²` regularity, `L²` time derivative,
solenoidal slices, and unregularized equation of `prop:lps-local-strong`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace ESS

/-- A strong solenoidal solution on `[t₀,T]`, in the class of
`prop:lps-local-strong`. Spatial derivatives use `Du z i j = ∂ⱼuᵢ` and
`D2u z i j k = ∂ₖ∂ⱼuᵢ`. Continuity into `H¹` is expressed through the
`L²` distance of the velocity and its specified gradient. -/
def IsLpsStrongSolution (t₀ T : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) : Prop :=
  t₀ < T ∧
    (∀ t ∈ Icc t₀ T,
      IsInJ (fun x : Vec3 => u (x, t)) ∧
      ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => u (x, t) i) ∧
        h.grad = (fun x : Vec3 => Du (x, t) i)) ∧
    (∀ t ∈ Icc t₀ T,
      Tendsto
        (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) ∧
      Tendsto
        (fun s : ℝ => eLpNorm (fun x : Vec3 => Du (x, s) - Du (x, t)) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0)) ∧
    (∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
      ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu ∧
        MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) ∧
        MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) ∧
        MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) ∧
        MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) ∧
    MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) ∧
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0

end ESS
