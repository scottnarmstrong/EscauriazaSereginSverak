-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Main.CarlemanGaussian
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

/-- Carleman inequality with a Gaussian weight (`prop:carleman-gauss`; ESS
Proposition 6.1). -/
theorem carlemanGaussian :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ a : ℝ, 0 < a → ∀ w : ParabolicPoint → Vec3,
      w ∈ spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2) →
      ∫ z in spaceTimeSet univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
              spatialGradientSq w (spatialGradient w) z) ≤
        c₀ * ∫ z in spaceTimeSet univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
              ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 :=
by exact ESS.Main.carlemanGaussian

end ESS
