-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Linear.BUShortPositiveDecay
public import ESS.Linear.BUShortCoreEstimate

/-!
# Quadratic densities in the short-time rescaling

These densities abbreviate the source field energy and its two fixed
Gaussian weights in the short-time half-space argument.
-/

@[expose] public section

set_option autoImplicit false

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Quadratic velocity and spatial-gradient energy of the rescaled
source field. -/
def buShortQuadraticEnergy (scale : ℝ)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (buAffineField (-scale ^ 2 / 2) scale w z) ^ 2 +
    spatialGradientSq
      (buAffineField (-scale ^ 2 / 2) scale w)
      (buAffineDw (-scale ^ 2 / 2) scale Dw) z

/-- Tangential Gaussian density with the normal polynomial needed for
the negative-phase error. -/
def buShortTangentialDensity (scale : ℝ)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
    (1 + z.1 2) ^ 4 * buShortQuadraticEnergy scale w Dw z

/-- Fixed-parameter shifted Carleman density with the polynomial
height factor needed for the shell estimates. -/
def buShortWeightedPolynomialDensity (scale a : ℝ)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4 *
    buShortQuadraticEnergy scale w Dw z

/-- Fixed-parameter shifted Carleman quadratic density. -/
def buShortWeightedDensity (scale a : ℝ)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  buShortShiftedWeight scale a z * buShortQuadraticEnergy scale w Dw z

end ESS
