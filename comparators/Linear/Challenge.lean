-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import Mathlib

/-!
# Unique continuation, backward uniqueness and Carleman inequalities

A standalone, Mathlib-only statement of the four linear results of Escauriaza,
Seregin and Šverák: unique continuation across spatial boundaries
(`thm:uc`), backward uniqueness on a half-space (`thm:bu`) and the two
Carleman inequalities (`prop:carleman-gauss`, `prop:carleman-halfspace`).
Space-time is `ℝ³ × ℝ` with `ℝ³ = EuclideanSpace ℝ (Fin 3)`, and all
derivatives are Fréchet derivatives or weak derivatives against smooth
compactly supported test functions.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace ESSChallenge

/-- Three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Test functions and derivatives -/

/-- Smooth compactly supported `Y`-valued functions on space-time `ℝ³ × ℝ`
whose topological support lies in `Ω × I`. -/
def testFunctions {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set ℝ³) (I : Set ℝ) : Set (ℝ³ × ℝ → Y) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ×ˢ I}

/-- The partial derivative `∂ⱼ g` of a scalar space-time function in the `j`-th
coordinate direction of `ℝ³`, at the point `z = (x, t)`. -/
def spatialDeriv (g : ℝ³ × ℝ → ℝ) (j : Fin 3) (z : ℝ³ × ℝ) : ℝ :=
  fderiv ℝ (fun x : ℝ³ => g (x, z.2)) z.1 (EuclideanSpace.single j 1)

/-- The iterated spatial derivative `∂ₖ ∂ⱼ g` at the point `z`. -/
def spatialSecondDeriv (g : ℝ³ × ℝ → ℝ) (j k : Fin 3) (z : ℝ³ × ℝ) : ℝ :=
  spatialDeriv (fun y => spatialDeriv g j y) k z

/-- The time derivative `∂ₜ g` of a scalar space-time function at the point
`z = (x, t)`. -/
def timeDeriv (g : ℝ³ × ℝ → ℝ) (z : ℝ³ × ℝ) : ℝ :=
  fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2 1

/-- Space-time weak derivatives on `Ω × I` (manuscript §2): `Dw z i j` is
`∂ⱼ wᵢ`, `D2w z i j k` is `∂ₖ ∂ⱼ wᵢ` and `Dtw z i` is `∂ₜ wᵢ`, each defined by
integration by parts against smooth compactly supported scalar test functions
on `Ω × I`; all four fields are locally integrable on `Ω × I`. -/
def HasSpaceTimeWeakDerivs (Ω : Set ℝ³) (I : Set ℝ) (w : ℝ³ × ℝ → ℝ³)
    (Dw : ℝ³ × ℝ → Fin 3 → Fin 3 → ℝ) (D2w : ℝ³ × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Dtw : ℝ³ × ℝ → ℝ³) : Prop :=
  LocallyIntegrableOn w (Ω ×ˢ I) ∧ LocallyIntegrableOn Dw (Ω ×ˢ I) ∧
  LocallyIntegrableOn D2w (Ω ×ˢ I) ∧ LocallyIntegrableOn Dtw (Ω ×ˢ I) ∧
  ∀ φ ∈ testFunctions (Y := ℝ) Ω I,
    (∀ i j : Fin 3,
      ∫ z in Ω ×ˢ I, w z i * spatialDeriv φ j z =
        -∫ z in Ω ×ˢ I, Dw z i j * φ z) ∧
    (∀ i j k : Fin 3,
      ∫ z in Ω ×ˢ I, Dw z i j * spatialDeriv φ k z =
        -∫ z in Ω ×ˢ I, D2w z i j k * φ z) ∧
    (∀ i : Fin 3,
      ∫ z in Ω ×ˢ I, w z i * timeDeriv φ z =
        -∫ z in Ω ×ˢ I, Dtw z i * φ z)

/-! ## The four theorems -/

/-- Unique continuation across spatial boundaries (`thm:uc`; ESS Theorem 4.1):
a differential inequality `|∂ₜ w + Δw| ≤ c₁ (|w| + |∇w|)` on `B_R × (0,T)`,
together with finite `H²`-type energy and vanishing to infinite order at the
origin in parabolic scaling, forces `w(·, 0) = 0` on the ball. (The coefficient
arrays Dw and D2w are measured in the maximum norm; finiteness of the
energy does not depend on the choice of norm.) -/
theorem uniqueContinuation (R T c₁ : ℝ) (hR : 0 < R) (hT : 0 < T) (hc₁ : 0 < c₁)
    (w : ℝ³ × ℝ → ℝ³) (Dw : ℝ³ × ℝ → Fin 3 → Fin 3 → ℝ)
    (D2w : ℝ³ × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ) (Dtw : ℝ³ × ℝ → ℝ³)
    (hcont : ContinuousOn w (Metric.ball (0 : ℝ³) R ×ˢ Ico 0 T))
    (hderiv : HasSpaceTimeWeakDerivs (Metric.ball (0 : ℝ³) R) (Ioo 0 T) w Dw D2w Dtw)
    (hL2 : (∫⁻ z in Metric.ball (0 : ℝ³) R ×ˢ Ioo 0 T,
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
          ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℝ³) R ×ˢ Ioo 0 T)),
      ‖(WithLp.toLp 2 fun i => Dtw z i + ∑ j, D2w z i j j : ℝ³)‖ ≤
        c₁ * (‖w z‖ + Real.sqrt (∑ i, ∑ j, Dw z i j ^ 2)))
    (hvanish : ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ Metric.ball (0 : ℝ³) R ×ˢ Ioo 0 T,
      ‖w z‖ ≤ C * (‖z.1‖ + Real.sqrt z.2) ^ k) :
    ∀ x ∈ Metric.ball (0 : ℝ³) R, w (x, 0) = 0 :=
  by sorry

/-- Backward uniqueness on a half-space (`thm:bu`; ESS Theorem 5.1): a solution
of the differential inequality `|∂ₜ w + Δw| ≤ c₁ (|∇w| + |w|)` on
`{x₃ > 0} × (0,1)` with `w(·, 0) = 0`, locally finite energy and Gaussian
growth vanishes identically. -/
theorem backwardUniqueness (c₁ M : ℝ) (hc₁ : 0 < c₁)
    (w : ℝ³ × ℝ → ℝ³) (Dw : ℝ³ × ℝ → Fin 3 → Fin 3 → ℝ)
    (D2w : ℝ³ × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ) (Dtw : ℝ³ × ℝ → ℝ³)
    (hcont : ContinuousOn w ({x : ℝ³ | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : ℝ³, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : ℝ³ | 0 < x 2} (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set (ℝ³ × ℝ), S ⊆ {x : ℝ³ | 0 < x 2} ×ˢ Ioo 0 1 →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict ({x : ℝ³ | 0 < x 2} ×ˢ Ioo 0 1)),
      ‖(WithLp.toLp 2 fun i => Dtw z i + ∑ j, D2w z i j j : ℝ³)‖ ≤
        c₁ * (Real.sqrt (∑ i, ∑ j, Dw z i j ^ 2) + ‖w z‖))
    (hgrowth : ∀ z ∈ {x : ℝ³ | 0 < x 2} ×ˢ Ioo 0 1,
      ‖w z‖ ≤ Real.exp (M * ‖z.1‖ ^ 2)) :
    ∀ z ∈ {x : ℝ³ | 0 < x 2} ×ˢ Ioo 0 1, w z = 0 :=
  by sorry

/-- Carleman inequality with a Gaussian weight (`prop:carleman-gauss`; ESS
Proposition 6.1), for smooth compactly supported vector fields on
`ℝ³ × (0,2)`. -/
theorem carlemanGaussian :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ a : ℝ, 0 < a → ∀ w : ℝ³ × ℝ → ℝ³,
      w ∈ testFunctions (Y := ℝ³) Set.univ (Ioo 0 2) →
      ∫ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 2,
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(‖z.1‖ ^ 2) / (4 * z.2)) *
            (a / z.2 * ‖w z‖ ^ 2 +
              ∑ i, ∑ j, spatialDeriv (fun y => w y i) j z ^ 2) ≤
        c₀ * ∫ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 2,
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(‖z.1‖ ^ 2) / (4 * z.2)) *
            ∑ i, (timeDeriv (fun y => w y i) z +
              ∑ j, spatialSecondDeriv (fun y => w y i) j j z) ^ 2 :=
  by sorry

/-- Carleman inequality on a half-space with an anisotropic weight
(`prop:carleman-halfspace`; ESS Proposition 6.2), for smooth compactly
supported vector fields on `{x₃ > 1} × (0,1)`. -/
theorem carlemanHalfSpace :
    ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ a : ℝ, a₀ < a → ∀ w : ℝ³ × ℝ → ℝ³,
        w ∈ testFunctions (Y := ℝ³) {x : ℝ³ | 1 < x 2} (Ioo 0 1) →
        ∫ z in {x : ℝ³ | 1 < x 2} ×ˢ Ioo 0 1,
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              (a * ‖w z‖ ^ 2 / z.2 ^ 2 +
                (∑ i, ∑ j, spatialDeriv (fun y => w y i) j z ^ 2) / z.2) ≤
          c * ∫ z in {x : ℝ³ | 1 < x 2} ×ˢ Ioo 0 1,
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              ∑ i, (timeDeriv (fun y => w y i) z +
                ∑ j, spatialSecondDeriv (fun y => w y i) j j z) ^ 2 :=
  by sorry

end ESSChallenge
