-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# The Escauriaza–Seregin–Šverák regularity theorems

A standalone, Mathlib-only statement of the local and global regularity theorems
`thm:ess-local`, `thm:ess-global`, `thm:ess-l5-unique`, `thm:lps`,
`cor:ess-smooth` and `cor:serrin-criterion` of the manuscript. Space is `EuclideanSpace ℝ (Fin 3)`, a
space-time point is a pair `(x, t)` in the ordinary product, the weak gradient
`Du` of a velocity is a continuous-linear-map valued field, and every notion is
defined below from Mathlib.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Gradient InnerProductSpace NNReal Topology

set_option autoImplicit false

noncomputable section

namespace ESSChallenge

/-- Three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Test functions and differential operators -/

/-- Smooth compactly supported `Y`-valued functions supported in `Ω`
(`sec:notation`). -/
def testFunctions
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) : Set (X → Y) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}

local notation "Dₓ" g:arg z:arg =>
  fderiv ℝ (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "∂ₜ" g:arg z:arg =>
  fderiv ℝ (fun t : ℝ ↦ g (Prod.fst z, t)) (Prod.snd z) 1
local notation "∇ₓ" g:arg z:arg =>
  gradient (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "divₓ" g:arg z:arg =>
  LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap (Dₓ g z))
local notation "⟪" A ", " B "⟫ₕₛ" =>
  LinearMap.trace ℝ ℝ³
    (ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint A ∘L B))
local infixr:100 " ⊗ᵣ " => InnerProductSpace.rankOne ℝ

/-- `Du` is the weak derivative of `u` on `U`: both are locally integrable on `U`
and `∫ φ ∂_v u = -∫ (∂_v φ) u` for every test function `φ` supported in `U`
(`sec:notation`). -/
structure HasWeakDerivativeOn
    {X Y : Type*}
    [MeasureSpace X]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (u : X → Y) (Du : X → (X →L[ℝ] Y)) : Prop where
  functionLocallyIntegrable : LocallyIntegrableOn u U volume
  derivativeLocallyIntegrable : LocallyIntegrableOn Du U volume
  integral_eq : ∀ φ ∈ testFunctions ℝ U, ∀ v (y' : Y →L[ℝ] ℝ),
    ∫ x in U, φ x * y' (Du x v) ∂volume =
      -∫ x in U, ⟪∇ φ x, v⟫_ℝ * y' (u x) ∂volume

/-! ## Hölder regularity and the singular set -/

/-- The backward cylinder `Qᵣ(z₀) = Bᵣ(x₀) × (t₀-r²,t₀]`, with optional top
centre `z₀ = (x₀,t₀)` defaulting to the origin. -/
abbrev Q (r : ℝ) (z₀ : ℝ³ × ℝ := 0) : Set (ℝ³ × ℝ) :=
  Metric.ball z₀.1 r ×ˢ Ioc (z₀.2 - r ^ 2) z₀.2

/-- The Hölder norm of an almost-everywhere equivalence class: the infimum,
over all representatives, of the supremum norm plus Hölder seminorm. -/
def aeHolderNormOn
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (U : Set X) (g : X → Y) (γ : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (w : X → Y) (_ : w =ᵐ[volume.restrict U] g),
    (⨆ x : U, ‖w x‖ₑ) + eHolderNorm γ (U.domRestrict w)

/-- A regular point of `u` in `Ω × I` (`sec:leray-hopf`, following the CKN definition of regular points): an open neighbourhood inside
`Ω × I` on which `u` has a Hölder representative of some exponent in `(0,1]`.
Ordinary space-time Hölder regularity is used; on bounded cylinders it is
equivalent to parabolic Hölder regularity after halving the exponent. -/
def IsHolderRegularPoint (Ω : Set ℝ³) (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³)
    (z₀ : ℝ³ × ℝ) : Prop :=
  ∃ U : Set (ℝ³ × ℝ), IsOpen U ∧ z₀ ∈ U ∧ U ⊆ Ω ×ˢ I ∧
    ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ aeHolderNormOn U u γ < ∞

/-- The points of `Ω × I` that are not regular points of `u` (`sec:leray-hopf`, following the CKN definition of regular points). -/
def singularSet
    (Ω : Set ℝ³) (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) : Set (ℝ³ × ℝ) :=
  {z ∈ Ω ×ˢ I | ¬IsHolderRegularPoint Ω I u z}

/-! ## Leray–Hopf solutions -/

/-- The divergence-free `L²` fields of `def:leray-hopf`: `L²` limits of smooth
compactly supported divergence-free fields. -/
def IsInJ (a : ℝ³ → ℝ³) : Prop :=
  MemLp a 2 volume ∧
    ∃ aSeq : ℕ → ℝ³ → ℝ³,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (aSeq k)) ∧
      (∀ k, HasCompactSupport (aSeq k)) ∧
      (∀ k x, LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap (fderiv ℝ (aSeq k) x)) = 0) ∧
      Tendsto (fun k => eLpNorm (fun x => aSeq k x - a x) 2 volume)
        atTop (𝓝 0)

/-- A Leray–Hopf solution on `ℝ³ × [0,T]` with datum `a` (`def:leray-hopf`, items
LH1–LH5), where `Du z v` is the weak derivative of the velocity in the direction
`v`. -/
def IsLerayHopfSolution (T : ℝ) (a : ℝ³ → ℝ³)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) : Prop :=
  0 < T ∧
    IsInJ a ∧
    AEStronglyMeasurable u
      (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)) ∧
    AEStronglyMeasurable Du
      (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)) ∧
    essSup (fun s : ℝ => ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ∞ ∧
    (∫⁻ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 T,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      HasWeakDerivativeOn (Set.univ : Set ℝ³)
        (fun x => u (x, s)) (fun x => Du (x, s))) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ ∈ testFunctions ℝ (Set.univ : Set ℝ³),
        ∫ x : ℝ³, ⟪u (x, s), ∇ ψ x⟫_ℝ = 0) ∧
    (∀ w : ℝ³ → ℝ³, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ) (Icc 0 T)) ∧
    (∀ φ ∈ testFunctions ℝ³ ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T),
      (∀ z : ℝ³ × ℝ, divₓ φ z = 0) →
      ∫ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 T,
        ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ = 0) ∧
    (∀ t₀ : ℝ, t₀ ∈ Icc 0 T →
      ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 t₀,
            ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ
        ≤ ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ))) ∧
    Tendsto (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ))
      (𝓝[>] 0) (𝓝 0)

/-! ## The regularity theorems -/

/-- The local Escauriaza–Seregin–Šverák regularity theorem `thm:ess-local`: a
local solution of finite energy on `B₁ × (-1,0)` that is bounded in `L^∞_t L³_x`
has a Hölder representative on the closed half cylinder. -/
theorem essLocal :
    ∀ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (p : ℝ³ × ℝ → ℝ),
      AEStronglyMeasurable u
        (volume.restrict (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0)) →
      AEStronglyMeasurable Du
        (volume.restrict (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0)) →
      AEStronglyMeasurable p
        (volume.restrict (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0)) →
      essSup (fun t : ℝ => ∫⁻ x in Metric.ball (0 : ℝ³) 1,
          ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ∞ →
      (∫⁻ z in Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0,
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ →
      MemLp p (3 / 2)
        (volume.restrict (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0)) →
      essSup (fun t : ℝ => ∫⁻ x in Metric.ball (0 : ℝ³) 1,
          ‖u (x, t)‖ₑ ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ∞ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)),
        HasWeakDerivativeOn (Metric.ball (0 : ℝ³) 1)
          (fun x => u (x, t)) (fun x => Du (x, t))) →
      (∀ ψ ∈ testFunctions ℝ (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0),
        ∫ z in Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0,
          ⟪u z, ∇ₓ ψ z⟫_ℝ = 0) →
      (∀ φ ∈ testFunctions ℝ³ (Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0),
        ∫ z in Metric.ball (0 : ℝ³) 1 ×ˢ Ioo (-1) 0,
          ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ
            + p z * divₓ φ z = 0) →
      ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧
        aeHolderNormOn (closure (Q (1 / 2))) u γ < ∞ :=
  by sorry

/-- The global Escauriaza–Seregin–Šverák regularity theorem `thm:ess-global`. -/
theorem essGlobal :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ∞ →
      singularSet (Set.univ : Set ℝ³) (Ioo 0 T) u = ∅ :=
  by sorry

/-- The `L⁵` bound and uniqueness theorem `thm:ess-l5-unique`. -/
theorem essL5Unique :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ∞ →
      MemLp u 5 (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)) ∧
      ∀ (v : ℝ³ × ℝ → ℝ³) (Dv : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsLerayHopfSolution T a v Dv →
          v =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u :=
  by sorry

/-- The Ladyzhenskaya–Prodi–Serrin regularity and uniqueness theorem `thm:lps`.
For finite `s > 3` the hypothesis is the mixed norm `L^ℓ_t L^s_x` with
`ℓ = 2s/(s-3)`; the second alternative is `L²_t L^∞_x`. The smooth
representative is `C^∞` (the exponent `(⊤ : ℕ∞)`, not `ω`) on `ℝ³ × (0,T]`,
with one-sided derivatives at `t = T`. -/
theorem ladyzhenskayaProdiSerrin :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      ((∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ s) ^ ((2 * s / (s - 3)) / s)) < ∞) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : ℝ³ => ‖u (x, t)‖ₑ) (volume : Measure ℝ³)) ^
            (2 : ℝ)) < ∞) →
      (∀ (v : ℝ³ × ℝ → ℝ³) (Dv : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsLerayHopfSolution T a v Dv →
          v =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u) ∧
      (∃ uSmooth : ℝ³ × ℝ → ℝ³,
        uSmooth =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) uSmooth ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T)) :=
  by sorry

/-- The full regularity, integrability and uniqueness conclusion of
`cor:ess-smooth`: the `L⁵` bound, uniqueness among Leray–Hopf solutions with the
same datum, and a `C^∞` representative on `ℝ³ × (0,T]`. -/
theorem essSmooth :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ∞ →
      MemLp u 5 (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)) ∧
      (∀ (v : ℝ³ × ℝ → ℝ³) (Dv : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsLerayHopfSolution T a v Dv →
          v =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u) ∧
      (∃ uSmooth : ℝ³ × ℝ → ℝ³,
        uSmooth =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) uSmooth ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T)) :=
  by sorry

/-- The regularity criterion `cor:serrin-criterion` over the whole range
`3 ≤ s ≤ ∞`: a Leray–Hopf solution on `[0,T]` in `L^ℓ(0,T;L^s(ℝ³))` with
`3/s + 2/ℓ = 1` is the only Leray–Hopf solution with its datum and agrees almost
everywhere with a function that is infinitely differentiable (the exponent
`(⊤ : ℕ∞)`, not `ω`) on `ℝ³ × (0,T]`, with one-sided derivatives at `T`. The
hypothesis is a disjunction of the endpoint `s = 3` (`L^∞_t L³_x`), the finite
range `3 < s < ∞` with `ℓ = 2s/(s-3)` and the endpoint `s = ∞` (`L²_t L^∞_x`). -/
theorem serrinCriterion :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      ((essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ∞) ∨
        (∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ s) ^ ((2 * s / (s - 3)) / s)) < ∞) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : ℝ³ => ‖u (x, t)‖ₑ) (volume : Measure ℝ³)) ^
            (2 : ℝ)) < ∞) →
      (∀ (v : ℝ³ × ℝ → ℝ³) (Dv : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsLerayHopfSolution T a v Dv →
          v =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u) ∧
      (∃ uSmooth : ℝ³ × ℝ → ℝ³,
        uSmooth =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) uSmooth ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T)) :=
  by sorry

end ESSChallenge
