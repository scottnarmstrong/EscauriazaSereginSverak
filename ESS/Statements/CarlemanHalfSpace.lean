-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Main.CarlemanHalfSpace
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

/-- Carleman inequality on a half-space with an anisotropic weight
(`prop:carleman-halfspace`; ESS Proposition 6.2). -/
theorem carlemanHalfSpace :
    ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ a : ℝ, a₀ < a → ∀ w : ParabolicPoint → Vec3,
        w ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
        ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
                spatialGradientSq w (spatialGradient w) z / z.2) ≤
          c * ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
                ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 :=
by exact ESS.Main.carlemanHalfSpace

end ESS
