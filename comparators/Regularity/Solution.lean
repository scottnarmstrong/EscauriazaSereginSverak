-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Statements.EssLocal
public import ESS.Statements.EssGlobal
public import ESS.Statements.EssL5Unique
public import ESS.Statements.LadyzhenskayaProdiSerrin
public import ESS.Statements.EssSmooth
public import ESS.Statements.SerrinCriterion
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


/-! ## Transport between the library and the Mathlib-native statements -/

abbrev RawSpace := CKN.Foundation.Parabolic.Vec3
abbrev RawPoint := CKN.Foundation.Parabolic.ParabolicPoint

theorem volume_rawPoint_eq_product :
    (volume : Measure RawPoint) =
      (volume : Measure (RawSpace × ℝ)) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
    MeasureTheory.Measure.volume_eq_prod]

theorem ofReal_three_halves :
    ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

def rawToEuclidean : RawSpace ≃L[ℝ] ℝ³ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm


def rawSpaceTimeLinear : (RawSpace × ℝ) ≃L[ℝ] (ℝ³ × ℝ) :=
  rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem rawSpaceTimeLinear_apply (z : RawSpace × ℝ) :
    rawSpaceTimeLinear z = (rawToEuclidean z.1, z.2) := by
  rfl

@[simp] theorem rawToEuclidean_prodCongr_refl_apply (z : RawSpace × ℝ) :
    (rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) z =
      (rawToEuclidean z.1, z.2) := by
  rfl

def rawSpaceTimeToEuclidean : (RawSpace × ℝ) ≃ₜ (ℝ³ × ℝ) :=
  rawSpaceTimeLinear.toHomeomorph

/-- The identity on space-time coordinates, first forgetting the old
parabolic topology and then using Euclidean spatial coordinates. -/
def parabolicToEuclideanHomeomorph : RawPoint ≃ₜ (ℝ³ × ℝ) :=
  CKN.Foundation.Parabolic.parabolicHomeomorph.trans
    rawSpaceTimeToEuclidean

@[simp] theorem parabolicToEuclideanHomeomorph_apply (z : RawPoint) :
    parabolicToEuclideanHomeomorph z = (rawToEuclidean z.1, z.2) := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_fst (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).1 = rawToEuclidean z.1 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_snd (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).2 = z.2 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_apply (z : RawSpace × ℝ) :
    rawSpaceTimeToEuclidean z = (rawToEuclidean z.1, z.2) := by
  rfl

theorem rawSpaceTimeToEuclidean_measurePreserving :
    MeasurePreserving rawSpaceTimeToEuclidean := by
  change MeasurePreserving (Prod.map (WithLp.toLp 2) id)
    (volume.prod volume) (volume.prod volume)
  exact (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id volume)

theorem parabolicToEuclidean_measurePreserving :
    MeasurePreserving parabolicToEuclideanHomeomorph
      (volume : Measure RawPoint) (volume : Measure (ℝ³ × ℝ)) := by
  refine ⟨parabolicToEuclideanHomeomorph.continuous.measurable, ?_⟩
  rw [volume_rawPoint_eq_product]
  exact rawSpaceTimeToEuclidean_measurePreserving.map_eq

theorem rawToEuclidean_measurePreserving : MeasurePreserving rawToEuclidean := by
  change MeasurePreserving (WithLp.toLp 2) volume volume
  exact PiLp.volume_preserving_toLp (Fin 3)

@[simp] theorem vec3EuclideanNorm_rawToEuclidean_symm (v : ℝ³) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (rawToEuclidean.symm v) = ‖v‖ := by
  rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  rfl

def euclideanSpace (U : Set RawSpace) : Set ℝ³ := rawToEuclidean '' U

def rawSpace (Ω : Set ℝ³) : Set RawSpace := rawToEuclidean ⁻¹' Ω

@[simp] theorem euclideanSpace_rawSpace (Ω : Set ℝ³) :
    euclideanSpace (rawSpace Ω) = Ω := by
  exact Equiv.image_preimage rawToEuclidean.toEquiv Ω

@[simp] theorem rawToEuclidean_preimage_euclideanSpace (U : Set RawSpace) :
    rawToEuclidean ⁻¹' euclideanSpace U = U := by
  exact Equiv.preimage_image rawToEuclidean.toEquiv U

@[simp] theorem rawSpaceTime_preimage_product (U : Set RawSpace) (J : Set ℝ) :
    rawSpaceTimeToEuclidean ⁻¹' (euclideanSpace U ×ˢ J) = U ×ˢ J := by
  ext z
  simp [rawSpaceTimeToEuclidean, rawSpaceTimeLinear, euclideanSpace]

theorem rawToEuclidean_restrict_measurePreserving (U : Set RawSpace) :
    MeasurePreserving rawToEuclidean
      (volume.restrict U) (volume.restrict (euclideanSpace U)) := by
  simpa using rawToEuclidean_measurePreserving.restrict_preimage_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding (euclideanSpace U)

theorem rawSpaceTime_restrict_measurePreserving (U : Set RawSpace) (J : Set ℝ) :
    MeasurePreserving rawSpaceTimeToEuclidean
      (volume.restrict (U ×ˢ J))
      (volume.restrict (euclideanSpace U ×ˢ J)) := by
  simpa using rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (euclideanSpace U ×ˢ J)

def pullVelocity (u : ℝ³ × ℝ → ℝ³) : RawSpace × ℝ → RawSpace :=
  fun z ↦ rawToEuclidean.symm (u (rawSpaceTimeToEuclidean z))

def pullScalar (g : ℝ³ × ℝ → ℝ) : RawSpace × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean z)

def pushScalar (g : RawSpace × ℝ → ℝ) : ℝ³ × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean.symm z)

def pushVector (g : RawSpace × ℝ → RawSpace) : ℝ³ × ℝ → ℝ³ :=
  fun z ↦ rawToEuclidean (g (rawSpaceTimeToEuclidean.symm z))

@[simp] theorem pushScalar_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawSpaceTimeToEuclidean z) = g z := by
  change g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z)) = g z
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushVector_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawSpaceTimeToEuclidean z) = rawToEuclidean (g z) := by
  change rawToEuclidean
    (g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z))) = _
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushScalar_rawCoordinates
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawToEuclidean z.1, z.2) = g z := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushScalar_rawSpaceTimeToEuclidean g z

@[simp] theorem pushVector_rawCoordinates
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawToEuclidean z.1, z.2) = rawToEuclidean (g z) := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushVector_rawSpaceTimeToEuclidean g z

@[simp] theorem rawToEuclidean_pullVelocity
    (u : ℝ³ × ℝ → ℝ³) (z : RawSpace × ℝ) :
    rawToEuclidean (pullVelocity u z) = u (rawToEuclidean z.1, z.2) := by
  simp [pullVelocity]

theorem pushScalar_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {ψ : RawSpace × ℝ → ℝ}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushScalar ψ ∈ testFunctions ℝ (Ω ×ˢ I) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hψdiff.comp rawSpaceTimeLinear.symm.contDiff
  · exact hψcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · change tsupport (ψ ∘ rawSpaceTimeToEuclidean.symm) ⊆ Ω ×ˢ I
    rw [tsupport_comp_eq_preimage ψ rawSpaceTimeToEuclidean.symm]
    intro z hz
    have hz' := hψsupport hz
    exact hz'

theorem pushVector_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {φ : RawSpace × ℝ → RawSpace}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushVector φ ∈ testFunctions ℝ³ (Ω ×ˢ I) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  refine ⟨rawToEuclidean.contDiff.comp
    (hφdiff.comp rawSpaceTimeLinear.symm.contDiff), ?_, ?_⟩
  · rw [HasCompactSupport,
      show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm)]
    exact hφcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · rw [show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm),
      tsupport_comp_eq_preimage φ rawSpaceTimeToEuclidean.symm]
    intro z hz
    exact hφsupport hz

theorem pushScalar_gradient_apply
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
      (rawToEuclidean z.1)) i =
        fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1 (CKN.basisVec i) := by
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single i 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right i 1
        (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
          (rawToEuclidean z.1))
    _ = fderiv ℝ (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) := inner_gradient_left
    _ = fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1
        (CKN.basisVec i) := by
      change fderiv ℝ (fun x : ℝ³ ↦ ψ (rawToEuclidean.symm x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) = _
      let g : ℝ³ → RawSpace × ℝ := fun x ↦ (rawToEuclidean.symm x, z.2)
      have hg : DifferentiableAt ℝ g (rawToEuclidean z.1) := by
        dsimp [g]
        fun_prop
      have hc : fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1) =
          fderiv ℝ ψ z ∘L fderiv ℝ g (rawToEuclidean z.1) := by
        simpa [g] using fderiv_comp (rawToEuclidean z.1)
          ((hψ.differentiable (by simp)) z) hg
      change (fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1))
        (EuclideanSpace.single i 1) = _
      rw [hc]
      let k : RawSpace → RawSpace × ℝ := fun x ↦ (x, z.2)
      have hk : DifferentiableAt ℝ k z.1 := by
        dsimp [k]
        fun_prop
      have hc' : fderiv ℝ (ψ ∘ k) z.1 =
          fderiv ℝ ψ z ∘L fderiv ℝ k z.1 := by
        simpa [k] using fderiv_comp z.1 ((hψ.differentiable (by simp)) z) hk
      rw [show (fun x : RawSpace ↦ ψ (x, z.2)) = ψ ∘ k by rfl, hc']
      rw [(rawToEuclidean.symm.hasFDerivAt.prodMk
          (hasFDerivAt_const z.2 (rawToEuclidean z.1))).fderiv]
      have hkf : fderiv ℝ k z.1 =
          (ContinuousLinearMap.id ℝ RawSpace).prod 0 := by
        simpa [k] using ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk
          (hasFDerivAt_const z.2 z.1)).fderiv
      rw [hkf]
      have hb : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
          (EuclideanSpace.single i 1) = CKN.basisVec i := by
        classical
        ext j
        by_cases hji : j = i
        · subst j
          simp [CKN.basisVec, EuclideanSpace.single]
        · simp [CKN.basisVec, EuclideanSpace.single, hji]
      simp [rawToEuclidean, hb]

theorem inner_pushScalar_gradient
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (v : RawSpace) :
    ⟪rawToEuclidean v,
      gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1)⟫_ℝ =
      ∑ i, v i * fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2))
        z.1 (CKN.basisVec i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [pushScalar_gradient_apply ψ hψ z i]
  simp [rawToEuclidean, mul_comm]

def rawGradient (D : ℝ³ →L[ℝ] ℝ³) : Fin 3 → RawSpace :=
  fun i j ↦ WithLp.ofLp (D (EuclideanSpace.single j 1)) i

def rawGradientLinear : (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] (Fin 3 → RawSpace) where
  toFun := rawGradient
  map_add' D E := by
    ext i j
    simp [rawGradient]
  map_smul' c D := by
    ext i j
    simp [rawGradient]

def rawGradientCLM : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] (Fin 3 → RawSpace) :=
  LinearMap.toContinuousLinearMap rawGradientLinear

theorem rawGradient_pushVector
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i j : Fin 3) :
    rawGradient
        (fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, z.2))
          (rawToEuclidean z.1)) i j =
      fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1
        (CKN.basisVec j) := by
  let F : ℝ³ → ℝ³ := fun x ↦ pushVector φ (x, z.2)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hF : DifferentiableAt ℝ F (rawToEuclidean z.1) := by
    have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
      rawToEuclidean.contDiff.comp
        (hφ.comp rawSpaceTimeLinear.symm.contDiff)
    have hfull : DifferentiableAt ℝ (pushVector φ)
        (rawToEuclidean z.1, z.2) :=
      (hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2)
    exact DifferentiableAt.comp (x := rawToEuclidean z.1)
      (f := fun x : ℝ³ ↦ (x, z.2)) (g := pushVector φ)
      hfull (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) (rawToEuclidean z.1) =
      proj ∘L fderiv ℝ F (rawToEuclidean z.1) := by
    simpa using fderiv_comp (rawToEuclidean z.1) proj.differentiableAt hF
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun w ↦ φ w i) := by fun_prop
  have hscalar := pushScalar_gradient_apply (fun w ↦ φ w i) hφi z j
  rw [← hscalar]
  change (proj (fderiv ℝ F (rawToEuclidean z.1)
    (EuclideanSpace.single j 1))) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  change fderiv ℝ (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
      (rawToEuclidean z.1) (EuclideanSpace.single j 1) = _
  symm
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single j 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right j 1
        (gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
          (rawToEuclidean z.1))
    _ = _ := inner_gradient_left

theorem timeDerivative_pushVector_apply
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (rawToEuclidean.symm
      (fderiv ℝ (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1)) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 := by
  let F : ℝ → ℝ³ := fun t ↦ pushVector φ (rawToEuclidean z.1, t)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
    rawToEuclidean.contDiff.comp
      (hφ.comp rawSpaceTimeLinear.symm.contDiff)
  have hF : DifferentiableAt ℝ F z.2 := by
    exact DifferentiableAt.comp (x := z.2)
      (f := fun t : ℝ ↦ (rawToEuclidean z.1, t)) (g := pushVector φ)
      ((hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2))
      (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) z.2 = proj ∘L fderiv ℝ F z.2 := by
    simpa using fderiv_comp z.2 proj.differentiableAt hF
  change proj (fderiv ℝ F z.2 1) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  congr 1


def pullGradient (D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    RawSpace × ℝ → Fin 3 → RawSpace :=
  fun z ↦ rawGradient (D (rawSpaceTimeToEuclidean z))

def pushSpatialScalar (g : RawSpace → ℝ) : ℝ³ → ℝ :=
  fun x ↦ g (rawToEuclidean.symm x)

theorem pushSpatialScalar_testFunction
    {U : Set RawSpace} {g : RawSpace → ℝ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ U) :
    pushSpatialScalar g ∈ testFunctions ℝ (euclideanSpace U) := by
  refine ⟨hgdiff.comp rawToEuclidean.symm.contDiff,
    hgcompact.comp_homeomorph rawToEuclidean.symm.toHomeomorph, ?_⟩
  change tsupport (g ∘ ⇑rawToEuclidean.symm.toHomeomorph) ⊆ euclideanSpace U
  rw [tsupport_comp_eq_preimage g rawToEuclidean.symm.toHomeomorph]
  intro x hx
  exact ⟨rawToEuclidean.symm x, hgsupport hx,
    rawToEuclidean.apply_symm_apply x⟩

theorem fderiv_pushSpatialScalar_basis
    (g : RawSpace → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : RawSpace) (j : Fin 3) :
    fderiv ℝ (pushSpatialScalar g) (rawToEuclidean x)
        (EuclideanSpace.single j 1) =
      fderiv ℝ g x (CKN.basisVec j) := by
  have hc := fderiv_comp (rawToEuclidean x)
    ((hg.differentiable (by simp)) x)
    rawToEuclidean.symm.differentiableAt
  change fderiv ℝ (g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace))
      (rawToEuclidean x) = _ at hc
  rw [show pushSpatialScalar g =
      g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace) by rfl,
    hc, rawToEuclidean.symm.fderiv]
  simp only [rawToEuclidean.symm_apply_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

theorem weakGradient_transport
    {U : Set RawSpace} {t : ℝ}
    {u : ℝ³ × ℝ → ℝ³}
    {D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)}
    (hD : HasWeakDerivativeOn (euclideanSpace U)
      (fun x ↦ u (x, t)) (fun x ↦ D (x, t))) :
    ∀ i, CKN.HasWeakGradientOn U
      (fun x ↦ pullVelocity u (x, t) i)
      (fun x ↦ pullGradient D (x, t) i) := by
  intro i j g hgdiff hgcompact hgsupport
  let ge := pushSpatialScalar g
  have hge : ge ∈ testFunctions ℝ (euclideanSpace U) :=
    pushSpatialScalar_testFunction hgdiff hgcompact hgsupport
  have hscalar := hD.integral_eq ge hge
    (EuclideanSpace.single j 1)
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i)
  simp_rw [inner_gradient_left] at hscalar
  have hmp := rawToEuclidean_restrict_measurePreserving U
  have hemb := rawToEuclidean.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb, ← hmp.integral_comp hemb] at hscalar
  have hderiv (x : RawSpace) :
      fderiv ℝ ge (rawToEuclidean x) (EuclideanSpace.single j 1) =
        fderiv ℝ g x (CKN.basisVec j) :=
    fderiv_pushSpatialScalar_basis g hgdiff x j
  have hge_apply (x : RawSpace) : ge (rawToEuclidean x) = g x := by
    simp [ge, pushSpatialScalar]
  simp_rw [hge_apply, hderiv] at hscalar
  simp only [PiLp.proj_apply] at hscalar
  have hscalar' :
      (∫ x in U, g x * pullGradient D (x, t) i j) =
        -∫ x in U,
          fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
    simpa [pullVelocity, pullGradient, rawGradient,
      rawSpaceTimeToEuclidean, rawSpaceTimeLinear, rawToEuclidean,
      hderiv] using hscalar
  change
    ∫ x in U,
        pullVelocity u (x, t) i * fderiv ℝ g x (CKN.basisVec j) =
      -∫ x in U, pullGradient D (x, t) i j * g x
  calc
    _ = ∫ x in U,
        fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
      congr 1
      funext x
      ring
    _ = -∫ x in U, g x * pullGradient D (x, t) i j := by
      linarith
    _ = _ := by
      congr 2
      funext x
      ring

theorem rawGradient_sq (D : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, (rawGradient D i j) ^ 2 =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L D)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j ^ 2 =
        ∑ j, ∑ i, rawGradient D i j ^ 2 := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          D (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, pow_two]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (D (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (D (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_pair (D E : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L E)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
        ∑ j, ∑ i, rawGradient D i j * rawGradient E i j := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          E (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, mul_comm]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (E (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (E (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_rankOne (v : RawSpace) (i j : Fin 3) :
    rawGradient (InnerProductSpace.rankOne ℝ
      (rawToEuclidean v) (rawToEuclidean v)) i j = v i * v j := by
  simp [rawGradient, rawToEuclidean, InnerProductSpace.rankOne_apply,
    PiLp.inner_apply, mul_comm]

theorem trace_eq_sum_rawGradient_diagonal (D : ℝ³ →L[ℝ] ℝ³) :
    LinearMap.trace ℝ ℝ³ D.toLinearMap = ∑ i, rawGradient D i i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  rfl

theorem momentum_integrand_transport
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (u f : RawSpace) (p : ℝ)
    (D : ℝ³ →L[ℝ] ℝ³) :
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪rawToEuclidean u, dtφ⟫_ℝ
        + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℝ (rawToEuclidean u) (rawToEuclidean u)) ∘L Dφ))
        - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L Dφ))
        + p * LinearMap.trace ℝ ℝ³ Dφ.toLinearMap
        + ⟪rawToEuclidean f, pushVector φ ze⟫_ℝ =
      -(-∑ i, u i * fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1
        - ∑ i, ∑ j, u i * u j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        + ∑ i, ∑ j, rawGradient D i j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        - p * ∑ i,
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec i)
        - ∑ i, f i * φ z i) := by
  dsimp only
  simp only [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]
  rw [← rawGradient_pair, ← rawGradient_pair,
    trace_eq_sum_rawGradient_diagonal]
  simp_rw [rawGradient_rankOne]
  simp_rw [rawGradient_pushVector φ hφ z]
  have ht (i : Fin 3) := timeDerivative_pushVector_apply φ hφ z i
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [show ∀ i, (fderiv ℝ
      (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 by
    intro i
    simpa [rawToEuclidean] using ht i]
  have hzraw : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
      (WithLp.toLp 2 z.1) = z.1 := by
    ext i
    simp [PiLp.continuousLinearEquiv_apply]
  simp [pushVector, rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    rawToEuclidean, hzraw, mul_comm, mul_assoc]
  ring


@[simp] theorem rawToEuclidean_symm_apply_apply (v : ℝ³) (i : Fin 3) :
    rawToEuclidean.symm v i = v.ofLp i := rfl

@[simp] theorem ofLp_rawToEuclidean (v : RawSpace) (i : Fin 3) :
    (rawToEuclidean v).ofLp i = v i := rfl

theorem euclideanSpace_univ : euclideanSpace (Set.univ : Set RawSpace) = Set.univ := by
  simp [euclideanSpace]

theorem rawSpace_univ : rawSpace (Set.univ : Set ℝ³) = Set.univ := rfl

theorem rawSpace_ball :
    rawSpace (Metric.ball (0 : ℝ³) 1) = CKN.Foundation.Parabolic.vec3Ball 0 1 := by
  ext x
  simp [rawSpace, CKN.Foundation.Parabolic.vec3Ball,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2, rawToEuclidean]

/-- Transport of a space-time map on the Euclidean side to a map on
the raw side, spatial only. -/
def pullSpace (a : ℝ³ → ℝ³) : RawSpace → RawSpace :=
  fun x ↦ rawToEuclidean.symm (a (rawToEuclidean x))

theorem vec3EuclideanNorm_pullSpace (a : ℝ³ → ℝ³) (x : RawSpace) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpace a x) =
      ‖a (rawToEuclidean x)‖ := by
  simp [pullSpace]

theorem vec3EuclideanNorm_pullVelocity (u : ℝ³ × ℝ → ℝ³) (z : RawSpace × ℝ) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u z) =
      ‖u (rawSpaceTimeToEuclidean z)‖ := by
  simp [pullVelocity]

theorem norm_pullVelocity_le (u : ℝ³ × ℝ → ℝ³) (z : RawSpace × ℝ) :
    ‖pullVelocity u z‖ ≤ ‖u (rawSpaceTimeToEuclidean z)‖ := by
  rw [← vec3EuclideanNorm_pullVelocity]
  exact CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _

theorem norm_rawGradient_le (D : ℝ³ →L[ℝ] ℝ³) : ‖rawGradient D‖ ≤ ‖D‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg D)).2 fun i ↦ ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg D)).2 fun j ↦ ?_
  calc ‖rawGradient D i j‖ = ‖(D (EuclideanSpace.single j 1)) i‖ := rfl
    _ ≤ ‖D (EuclideanSpace.single j 1)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖D‖ * ‖(EuclideanSpace.single j (1 : ℝ) : ℝ³)‖ := D.le_opNorm _
    _ = ‖D‖ := by simp

theorem norm_pullGradient_le (D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (z : RawSpace × ℝ) :
    ‖pullGradient D z‖ ≤ ‖D (rawSpaceTimeToEuclidean z)‖ :=
  norm_rawGradient_le _

theorem pushVector_pullVelocity (u : ℝ³ × ℝ → ℝ³) :
    pushVector (pullVelocity u) = u := by
  funext z
  simp [pushVector, pullVelocity]

theorem lintegral_space_transport (g : ℝ³ → ℝ≥0∞) :
    ∫⁻ x : RawSpace, g (rawToEuclidean x) = ∫⁻ y : ℝ³, g y :=
  rawToEuclidean_measurePreserving.lintegral_comp_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding g

theorem lintegral_spaceTimeSet_transport (U : Set RawSpace) (J : Set ℝ)
    (g : ℝ³ × ℝ → ℝ≥0∞) :
    ∫⁻ z in CKN.spaceTimeSet U J, g (rawSpaceTimeToEuclidean z) =
      ∫⁻ z in euclideanSpace U ×ˢ J, g z := by
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  exact (rawSpaceTime_restrict_measurePreserving U J).lintegral_comp_emb
    rawSpaceTimeToEuclidean.measurableEmbedding g

theorem lintegral_slice_pull (U : Set RawSpace) (t : ℝ) (u : ℝ³ × ℝ → ℝ³) (r : ℝ) :
    ∫⁻ x in U, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ r =
      ∫⁻ y in euclideanSpace U, ‖u (y, t)‖ₑ ^ r := by
  have h : ∀ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ r =
      (fun y : ℝ³ ↦ ‖u (y, t)‖ₑ ^ r) (rawToEuclidean x) := by
    intro x
    simp only [vec3EuclideanNorm_pullVelocity, rawSpaceTimeToEuclidean_apply,
      ofReal_norm]
  simp_rw [h]
  exact (rawToEuclidean_restrict_measurePreserving U).lintegral_comp_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding
    (fun y : ℝ³ ↦ ‖u (y, t)‖ₑ ^ r)

theorem lintegral_slice_pull_le (U : Set RawSpace) (t : ℝ) (u : ℝ³ × ℝ → ℝ³)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ x in U, ‖pullVelocity u (x, t)‖ₑ ^ r ≤
      ∫⁻ y in euclideanSpace U, ‖u (y, t)‖ₑ ^ r := by
  rw [← lintegral_slice_pull U t u r]
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ hr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _)

theorem lintegral_energy_pull_le (U : Set RawSpace) (J : Set ℝ)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    ∫⁻ z in CKN.spaceTimeSet U J,
        ‖pullVelocity u z‖ₑ ^ (2 : ℝ) + ‖pullGradient Du z‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ z in euclideanSpace U ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_spaceTimeSet_transport U J
    (fun z ↦ ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ))]
  apply lintegral_mono
  intro z
  dsimp only
  gcongr
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_pullVelocity_le u z)
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_pullGradient_le Du z)

theorem aesm_pullVelocity {U : Set RawSpace} {J : Set ℝ} {u : ℝ³ × ℝ → ℝ³}
    (h : AEStronglyMeasurable u (volume.restrict (euclideanSpace U ×ˢ J))) :
    AEStronglyMeasurable (pullVelocity u) ((volume : Measure RawPoint).restrict (CKN.spaceTimeSet U J)) := by
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  exact rawToEuclidean.symm.continuous.comp_aestronglyMeasurable
    (h.comp_measurePreserving (rawSpaceTime_restrict_measurePreserving U J))

theorem aesm_pullGradient {U : Set RawSpace} {J : Set ℝ}
    {Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)}
    (h : AEStronglyMeasurable Du (volume.restrict (euclideanSpace U ×ˢ J))) :
    AEStronglyMeasurable (pullGradient Du) ((volume : Measure RawPoint).restrict (CKN.spaceTimeSet U J)) := by
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  exact rawGradientCLM.continuous.comp_aestronglyMeasurable
    (h.comp_measurePreserving (rawSpaceTime_restrict_measurePreserving U J))

theorem aesm_pullScalar {U : Set RawSpace} {J : Set ℝ} {p : ℝ³ × ℝ → ℝ}
    (h : AEStronglyMeasurable p (volume.restrict (euclideanSpace U ×ˢ J))) :
    AEStronglyMeasurable (pullScalar p) ((volume : Measure RawPoint).restrict (CKN.spaceTimeSet U J)) := by
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  exact h.comp_measurePreserving (rawSpaceTime_restrict_measurePreserving U J)

theorem memLp_pullScalar {U : Set RawSpace} {J : Set ℝ} {p : ℝ³ × ℝ → ℝ}
    (h : MemLp p (3 / 2) (volume.restrict (euclideanSpace U ×ˢ J))) :
    MemLp (pullScalar p) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure RawPoint).restrict (CKN.spaceTimeSet U J)) := by
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product, ofReal_three_halves]
  exact h.comp_measurePreserving (rawSpaceTime_restrict_measurePreserving U J)


theorem rawSpaceTime_preimage_Q (r : ℝ) (z₀ : ℝ³ × ℝ) :
    rawSpaceTimeToEuclidean ⁻¹' Q r z₀ =
      CKN.Foundation.Parabolic.parabolicCylinder
        (rawToEuclidean.symm z₀.1) z₀.2 r := by
  ext z
  change
    (dist (rawToEuclidean z.1) z₀.1 < r ∧
      z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2) ↔
    (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (z.1 - rawToEuclidean.symm z₀.1) < r ∧
      z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2)
  have hnorm : dist (rawToEuclidean z.1) z₀.1 =
      CKN.Foundation.Parabolic.vec3EuclideanNorm
        (z.1 - rawToEuclidean.symm z₀.1) := by
    rw [dist_eq_norm,
      CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
    change ‖rawToEuclidean z.1 - z₀.1‖ =
      ‖rawToEuclidean (z.1 - rawToEuclidean.symm z₀.1)‖
    rw [map_sub, rawToEuclidean.apply_symm_apply]
  rw [hnorm]

theorem rawSpaceTime_image_cylinder (x₀ : RawSpace) (t₀ r : ℝ) :
    rawSpaceTimeToEuclidean ''
        CKN.Foundation.Parabolic.parabolicCylinder x₀ t₀ r =
      Q r (rawToEuclidean x₀, t₀) := by
  have hpre := rawSpaceTime_preimage_Q r (rawToEuclidean x₀, t₀)
  simp only [rawToEuclidean.symm_apply_apply] at hpre
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hpre ⊢
  rw [← hpre]
  exact Equiv.image_preimage rawSpaceTimeToEuclidean.toEquiv _

theorem closure_Q {r : ℝ} (hr : 0 < r) (z₀ : ℝ³ × ℝ) :
    closure (Q r z₀) =
      Metric.closedBall z₀.1 r ×ˢ Icc (z₀.2 - r ^ 2) z₀.2 := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  rw [Q, closure_prod_eq,
    closure_ball z₀.1 hr.ne',
    closure_Ioc (by linarith : z₀.2 - r ^ 2 ≠ z₀.2)]

theorem mem_closure_cylinder_iff_mem_closure_Q
    {r : ℝ} (hr : 0 < r) (z₀ : RawPoint) (z : RawPoint) :
    z ∈ closure (CKN.Foundation.Parabolic.parabolicCylinder z₀.1 z₀.2 r) ↔
      rawSpaceTimeToEuclidean z ∈
        closure (Q r (rawToEuclidean z₀.1, z₀.2)) := by
  rw [CKN.Foundation.Parabolic.closure_parabolicCylinder hr,
    closure_Q hr]
  change
    (CKN.Foundation.Parabolic.vec3EuclideanNorm (z.1 - z₀.1) ≤ r ∧
      z.2 ∈ Icc (z₀.2 - r ^ 2) z₀.2) ↔
    (dist (rawToEuclidean z.1) (rawToEuclidean z₀.1) ≤ r ∧
      z.2 ∈ Icc (z₀.2 - r ^ 2) z₀.2)
  have hnorm :
      CKN.Foundation.Parabolic.vec3EuclideanNorm (z.1 - z₀.1) =
        dist (rawToEuclidean z.1) (rawToEuclidean z₀.1) := by
    rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2,
      dist_eq_norm, ← map_sub]
    rfl
  rw [hnorm]

theorem Q_aeEq_closure {r : ℝ} (hr : 0 < r) (z₀ : ℝ³ × ℝ) :
    Q r z₀ =ᵐ[(volume : Measure (ℝ³ × ℝ))] closure (Q r z₀) := by
  rw [ae_eq_set]
  constructor
  · rw [sdiff_eq_empty.mpr subset_closure, measure_empty]
  · apply measure_mono_null (t :=
      (Metric.sphere z₀.1 r ×ˢ Icc (z₀.2 - r ^ 2) z₀.2) ∪
        (Metric.closedBall z₀.1 r ×ˢ {z₀.2 - r ^ 2}))
    · intro z hz
      rw [closure_Q hr] at hz
      rcases hz with ⟨⟨hx, ht⟩, hnQ⟩
      change ¬(dist z.1 z₀.1 < r ∧
        z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2) at hnQ
      rcases not_and_or.mp hnQ with hnx | hnt
      · left
        refine ⟨?_, ht⟩
        rw [Metric.mem_sphere]
        exact le_antisymm hx (not_lt.mp hnx)
      · right
        refine ⟨hx, ?_⟩
        simp only [mem_singleton_iff]
        rcases ht with ⟨htlo, hthi⟩
        have hnotlo : ¬z₀.2 - r ^ 2 < z.2 := fun hz ↦ hnt ⟨hz, hthi⟩
        exact le_antisymm (not_lt.mp hnotlo) htlo
    · apply measure_union_null
      · rw [MeasureTheory.Measure.volume_eq_prod,
          MeasureTheory.Measure.prod_prod,
          MeasureTheory.Measure.addHaar_sphere, zero_mul]
      · rw [MeasureTheory.Measure.volume_eq_prod,
          MeasureTheory.Measure.prod_prod, measure_singleton, mul_zero]

theorem parabolicDist_le_sqrt_dist_on_halfCylinder
    {z w : RawPoint}
    (hz : rawSpaceTimeToEuclidean z ∈ closure (Q (1 / 2)))
    (hw : rawSpaceTimeToEuclidean w ∈ closure (Q (1 / 2))) :
    CKN.Foundation.Parabolic.parabolicDist z w ≤
      Real.sqrt (dist (rawSpaceTimeToEuclidean z)
        (rawSpaceTimeToEuclidean w)) := by
  rw [closure_Q (by norm_num : (0 : ℝ) < 1 / 2)] at hz hw
  change rawToEuclidean z.1 ∈ Metric.closedBall 0 (1 / 2) ∧
    z.2 ∈ Icc (0 - (1 / 2 : ℝ) ^ 2) 0 at hz
  change rawToEuclidean w.1 ∈ Metric.closedBall 0 (1 / 2) ∧
    w.2 ∈ Icc (0 - (1 / 2 : ℝ) ^ 2) 0 at hw
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  have hx : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤ 1 := by
    calc
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
          dist (rawToEuclidean z.1) 0 + dist 0 (rawToEuclidean w.1) :=
        dist_triangle _ _ _
      _ ≤ 1 / 2 + 1 / 2 := by
        gcongr
        · simpa [Metric.mem_closedBall] using hzx
        · rw [dist_comm]
          simpa [Metric.mem_closedBall] using hwx
      _ = 1 := by norm_num
  have ht : dist z.2 w.2 ≤ 1 := by
    rw [Real.dist_eq, abs_le]
    constructor <;> rcases hzt with ⟨hztl, hztr⟩ <;>
      rcases hwt with ⟨hwtl, hwtr⟩ <;> norm_num at * <;> linarith
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean w)
  have hd : d = max (dist (rawToEuclidean z.1) (rawToEuclidean w.1))
      (dist z.2 w.2) := by
    rfl
  have hdle : d ≤ 1 := by rw [hd]; exact max_le hx ht
  have hspace : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
      Real.sqrt d := by
    exact (hd.symm ▸ le_max_left _ _).trans
      (Real.le_sqrt_self_iff.mpr hdle)
  have htime : Real.sqrt (dist z.2 w.2) ≤ Real.sqrt d := by
    apply Real.sqrt_le_sqrt
    exact hd.symm ▸ le_max_right _ _
  rw [CKN.Foundation.Parabolic.parabolicDist,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hspace_eq : ‖WithLp.toLp 2 (z.1 - w.1)‖ =
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) := by
    rw [dist_eq_norm, ← map_sub]
    rfl
  rw [hspace_eq, ← Real.dist_eq]
  exact max_le hspace htime

theorem parabolicDist_le_sqrt_dist_of_dist_le_one
    (z w : RawPoint)
    (hd : dist (rawSpaceTimeToEuclidean z)
      (rawSpaceTimeToEuclidean w) ≤ 1) :
    CKN.Foundation.Parabolic.parabolicDist z w ≤
      Real.sqrt (dist (rawSpaceTimeToEuclidean z)
        (rawSpaceTimeToEuclidean w)) := by
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean w)
  have hspace : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
      Real.sqrt d := by
    exact (le_max_left _ _).trans
      (Real.le_sqrt_self_iff.mpr hd)
  have htime : Real.sqrt (dist z.2 w.2) ≤ Real.sqrt d := by
    apply Real.sqrt_le_sqrt
    exact le_max_right _ _
  rw [CKN.Foundation.Parabolic.parabolicDist,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hspace_eq : ‖WithLp.toLp 2 (z.1 - w.1)‖ =
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) := by
    rw [dist_eq_norm, ← map_sub]
    rfl
  rw [hspace_eq, ← Real.dist_eq]
  exact max_le hspace htime

theorem pushVector_dist_eq_vec3EuclideanNorm
    (w : RawSpace × ℝ → RawSpace) (z z' : RawSpace × ℝ) :
    dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z')) =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') := by
  rw [pushVector_rawSpaceTimeToEuclidean,
    pushVector_rawSpaceTimeToEuclidean, dist_eq_norm,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  change ‖rawToEuclidean (w z) - rawToEuclidean (w z')‖ =
    ‖rawToEuclidean (w z - w z')‖
  rw [map_sub]

theorem pushVector_holderOnWith_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {γ B K : ℝ}
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hsup : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B)
    (hseminorm : ∀ z ∈ N, ∀ z' ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    HolderOnWith ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ (pushVector w)
      (parabolicToEuclideanHomeomorph '' N) := by
  intro x hx x' hx'
  rcases hx with ⟨z, hz, hzx⟩
  rcases hx' with ⟨z', hz', hzx'⟩
  have hxcoord : x = rawSpaceTimeToEuclidean z := by rw [← hzx]; rfl
  have hx'coord : x' = rawSpaceTimeToEuclidean z' := by rw [← hzx']; rfl
  rw [hxcoord, hx'coord]
  have hout := pushVector_dist_eq_vec3EuclideanNorm w z z'
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean z')
  have hreal :
      dist (pushVector w (rawSpaceTimeToEuclidean z))
          (pushVector w (rawSpaceTimeToEuclidean z')) ≤
        max K (2 * B) * d ^ (γ / 2) := by
    rw [hout]
    by_cases hd : d ≤ 1
    · have hpar := parabolicDist_le_sqrt_dist_of_dist_le_one z z' hd
      have hpar0 : 0 ≤ CKN.Foundation.Parabolic.parabolicDist z z' := by
        unfold CKN.Foundation.Parabolic.parabolicDist
        positivity
      have hpow := Real.rpow_le_rpow hpar0 hpar hγ.le
      calc
        _ ≤ K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ :=
          hseminorm z hz z' hz'
        _ ≤ K * Real.sqrt d ^ γ :=
          mul_le_mul_of_nonneg_left hpow hK
        _ = K * d ^ (γ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (dist_nonneg : 0 ≤ d)]
          congr 2
          ring
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          gcongr
          exact le_max_left _ _
    · have hnorm :
          CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
            CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) +
              CKN.Foundation.Parabolic.vec3EuclideanNorm (w z') := by
          simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2,
            WithLp.toLp_sub]
          exact norm_sub_le _ _
      have hd1 : 1 ≤ d := le_of_not_ge hd
      have hpow1 : 1 ≤ d ^ (γ / 2) := by
        exact Real.one_le_rpow hd1 (div_nonneg hγ.le (by norm_num))
      calc
        _ ≤ 2 * B := by linarith [hsup z hz, hsup z' hz']
        _ ≤ max K (2 * B) := le_max_right _ _
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          nlinarith [hK.trans (le_max_left K (2 * B))]
  rw [edist_dist, edist_dist]
  let C : ℝ≥0 :=
    ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  change ENNReal.ofReal
      (dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z'))) ≤
    (C : ℝ≥0∞) * ENNReal.ofReal d ^ (γ / 2)
  rw [show (C : ℝ≥0∞) = ENNReal.ofReal (max K (2 * B)) by
      rw [ENNReal.ofReal_eq_coe_nnreal
        (hK.trans (le_max_left K (2 * B)))]; rfl,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg
      (div_nonneg hγ.le (by norm_num)),
    ← ENNReal.ofReal_mul (hK.trans (le_max_left K (2 * B)))]
  exact ENNReal.ofReal_le_ofReal hreal

theorem pushVector_holder_dist_half
    {w : RawSpace × ℝ → RawSpace} {γ K : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      ∀ z' ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    ∀ z ∈ closure (Q (1 / 2)), ∀ z' ∈ closure (Q (1 / 2)),
      dist (pushVector w z) (pushVector w z') ≤
        K * dist z z' ^ (γ / 2) := by
  intro ze hze we hwe
  let z : RawPoint := rawSpaceTimeToEuclidean.symm ze
  let z' : RawPoint := rawSpaceTimeToEuclidean.symm we
  have hzmap : rawSpaceTimeToEuclidean z = ze := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply ze
  have hz'map : rawSpaceTimeToEuclidean z' = we := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply we
  have hzraw : z ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z).mpr
    apply hzq
    rw [hzmap]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact hze
  have hz'raw : z' ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z').mpr
    apply hzq
    rw [hz'map]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact hwe
  have hpar := parabolicDist_le_sqrt_dist_on_halfCylinder
    (z := z) (w := z') (hzmap.symm ▸ hze) (hz'map.symm ▸ hwe)
  have hpar_nonneg :
      0 ≤ CKN.Foundation.Parabolic.parabolicDist z z' := by
    unfold CKN.Foundation.Parabolic.parabolicDist
    positivity
  have hpow := Real.rpow_le_rpow hpar_nonneg hpar hγ
  have hout : dist (pushVector w ze) (pushVector w we) =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') := by
    rw [dist_eq_norm,
      CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
    change ‖rawToEuclidean (w z) - rawToEuclidean (w z')‖ =
      ‖rawToEuclidean (w z - w z')‖
    rw [map_sub]
  rw [hout]
  calc
    _ ≤ K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ :=
      hw z hzraw z' hz'raw
    _ ≤ K * Real.sqrt (dist ze we) ^ γ := by
      rw [← hzmap, ← hz'map]
      exact mul_le_mul_of_nonneg_left hpow hK
    _ = K * dist ze we ^ (γ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (dist_nonneg : 0 ≤ dist ze we)]
      congr 2
      ring

theorem pushVector_holderOnWith_half
    {w : RawSpace × ℝ → RawSpace} {γ K : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      ∀ z' ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    HolderOnWith ⟨K, hK⟩ ⟨γ / 2, div_nonneg hγ (by norm_num)⟩
      (pushVector w) (closure (Q (1 / 2))) := by
  intro z hz z' hz'
  have hreal := pushVector_holder_dist_half hγ hK hw z hz z' hz'
  rw [edist_dist, edist_dist]
  let Kpos : ℝ≥0 := ⟨K, hK⟩
  change ENNReal.ofReal (dist (pushVector w z) (pushVector w z')) ≤
    (Kpos : ℝ≥0∞) *
      ENNReal.ofReal (dist z z') ^ (γ / 2)
  rw [show (Kpos : ℝ≥0∞) = ENNReal.ofReal K by
      rw [ENNReal.ofReal_eq_coe_nnreal hK]; rfl,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg
      (div_nonneg hγ (by norm_num)),
    ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal hreal

theorem pushVector_aeEq_on_Q
    {r : ℝ} {z₀ : ℝ³ × ℝ} {w : RawSpace × ℝ → RawSpace}
    {u : ℝ³ × ℝ → ℝ³}
    (hw : w =ᵐ[(volume : Measure RawPoint).restrict
        (CKN.Foundation.Parabolic.parabolicCylinder
          (rawToEuclidean.symm z₀.1) z₀.2 r)] pullVelocity u) :
    pushVector w =ᵐ[(volume : Measure (ℝ³ × ℝ)).restrict (Q r z₀)] u := by
  rw [volume_rawPoint_eq_product] at hw
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hw
  let hmp := rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (Q r z₀)
  rw [← hmp.map_eq]
  apply rawSpaceTimeToEuclidean.measurableEmbedding.ae_map_iff.mpr
  rw [rawSpaceTime_preimage_Q]
  filter_upwards [hw] with z hz
  rw [pushVector_rawSpaceTimeToEuclidean, hz,
    rawToEuclidean_pullVelocity]
  rfl

theorem pushVector_aeEq_on_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace}
    {u : ℝ³ × ℝ → ℝ³}
    (hw : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u) :
    pushVector w =ᵐ[(volume : Measure (ℝ³ × ℝ)).restrict
      (parabolicToEuclideanHomeomorph '' N)] u := by
  let hmp := parabolicToEuclidean_measurePreserving.restrict_preimage_emb
    parabolicToEuclideanHomeomorph.measurableEmbedding
      (parabolicToEuclideanHomeomorph '' N)
  have hpre : parabolicToEuclideanHomeomorph ⁻¹'
      (parabolicToEuclideanHomeomorph '' N) = N :=
    Equiv.preimage_image parabolicToEuclideanHomeomorph.toEquiv N
  rw [hpre] at hmp
  rw [← hmp.map_eq]
  apply parabolicToEuclideanHomeomorph.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hw] with z hz
  change rawToEuclidean (w z) = u (rawToEuclidean z.1, z.2)
  rw [hz]
  change rawToEuclidean
    (rawToEuclidean.symm (u (rawToEuclidean z.1, z.2))) = _
  rw [rawToEuclidean.apply_symm_apply]

theorem pushVector_enorm_le_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {B : ℝ}
    (hw : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B) :
    ∀ z : parabolicToEuclideanHomeomorph '' N,
      ‖pushVector w z‖ₑ ≤ ENNReal.ofReal B := by
  rintro ⟨ze, z, hz, hze⟩
  subst ze
  change ‖rawToEuclidean (w z)‖ₑ ≤ ENNReal.ofReal B
  rw [← ofReal_norm,
    show ‖rawToEuclidean (w z)‖ =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) by
        exact (CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2 _).symm]
  exact ENNReal.ofReal_le_ofReal (hw z hz)

theorem pushVector_aeHolderNormOn_image_lt_top
    {N : Set RawPoint} {u : ℝ³ × ℝ → ℝ³}
    {w : RawSpace × ℝ → RawSpace} {γ : ℝ} (hγ : 0 < γ)
    (hae : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u)
    (hholder : CKN.ParabolicHolderVecOn N w γ) :
    aeHolderNormOn (parabolicToEuclideanHomeomorph '' N) u
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ < ∞ := by
  rcases hholder with ⟨B, K, hB, hK, hsup, hseminorm⟩
  have haeImage := pushVector_aeEq_on_image hae
  have hHolder :=
    (pushVector_holderOnWith_image hγ hK hsup hseminorm).holderWith
  let C : ℝ≥0 := ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  have hHolderNorm :
      eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
          ((parabolicToEuclideanHomeomorph '' N).domRestrict
            (pushVector w)) ≤ (C : ℝ≥0∞) :=
    hHolder.eHolderNorm_le
  unfold aeHolderNormOn
  calc
    (⨅ (v : ℝ³ × ℝ → ℝ³)
        (_ : v =ᵐ[volume.restrict
          (parabolicToEuclideanHomeomorph '' N)] u),
        (⨆ z : parabolicToEuclideanHomeomorph '' N, ‖v z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict v)) ≤
        (⨆ z : parabolicToEuclideanHomeomorph '' N,
          ‖pushVector w z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict
              (pushVector w)) :=
      iInf_le_of_le (pushVector w) (iInf_le_of_le haeImage le_rfl)
    _ ≤ ENNReal.ofReal B + (C : ℝ≥0∞) :=
      add_le_add (iSup_le (pushVector_enorm_le_image hsup)) hHolderNorm
    _ < ∞ := ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.coe_lt_top⟩

theorem pushVector_enorm_le_half
    {w : RawSpace × ℝ → RawSpace} {B : ℝ}
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B) :
    ∀ z : closure (Q (1 / 2)), ‖pushVector w z‖ₑ ≤
      ENNReal.ofReal B := by
  intro ze
  let z : RawPoint := rawSpaceTimeToEuclidean.symm ze
  have hzmap : rawSpaceTimeToEuclidean z = ze := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply ze
  have hzraw : z ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z).mpr
    apply hzq
    rw [hzmap]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact ze.property
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖pushVector w ze‖ =
        CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) := by
      rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
      change ‖rawToEuclidean
        (w (rawSpaceTimeToEuclidean.symm ze))‖ = ‖rawToEuclidean (w z)‖
      rw [show rawSpaceTimeToEuclidean.symm ze = z by rfl]
    _ ≤ B := hw z hzraw


theorem isHolderRegularPoint_of_rawRegular
    {Ω : Set ℝ³} {I : Set ℝ} {u : ℝ³ × ℝ → ℝ³} {z₀ : RawPoint}
    (hreg : CKN.IsRegularPoint (rawSpace Ω) I (pullVelocity u) z₀) :
    IsHolderRegularPoint Ω I u (parabolicToEuclideanHomeomorph z₀) := by
  rcases hreg with ⟨_, N, hNopen, hzN, hNsub, γ, hγ, hγle, w, hae, hholder⟩
  refine ⟨parabolicToEuclideanHomeomorph '' N,
    parabolicToEuclideanHomeomorph.isOpenMap N hNopen,
    ⟨z₀, hzN, rfl⟩, ?_,
    ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hNsub hz
  · exact div_pos hγ (by norm_num)
  · change γ / 2 ≤ (1 : ℝ)
    linarith
  · exact pushVector_aeHolderNormOn_image_lt_top hγ hae hholder

theorem trace_pushVector (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) :
    LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
      (fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, z.2)) (rawToEuclidean z.1))) =
      ∑ i, CKN.spatialPartial (fun y ↦ φ y i) i z := by
  rw [trace_eq_sum_rawGradient_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [rawGradient_pushVector φ hφ z i i]
  rfl

theorem gradient_pushSpatialScalar_apply (g : RawSpace → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : RawSpace) (i : Fin 3) :
    (gradient (pushSpatialScalar g) (rawToEuclidean x)) i =
      fderiv ℝ g x (CKN.basisVec i) := by
  calc
    _ = ⟪gradient (pushSpatialScalar g) (rawToEuclidean x),
        EuclideanSpace.single i 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right i 1
        (gradient (pushSpatialScalar g) (rawToEuclidean x))
    _ = fderiv ℝ (pushSpatialScalar g) (rawToEuclidean x)
        (EuclideanSpace.single i 1) := inner_gradient_left
    _ = _ := fderiv_pushSpatialScalar_basis g hg x i

theorem rawToEuclidean_fst_symm (z : ℝ³ × ℝ) :
    rawToEuclidean (rawSpaceTimeToEuclidean.symm z).1 = z.1 := by
  have := congrArg Prod.fst (rawSpaceTimeToEuclidean.apply_symm_apply z)
  rw [rawSpaceTimeToEuclidean_fst] at this
  exact this

theorem snd_symm (z : ℝ³ × ℝ) : (rawSpaceTimeToEuclidean.symm z).2 = z.2 := by
  have := congrArg Prod.snd (rawSpaceTimeToEuclidean.apply_symm_apply z)
  rw [rawSpaceTimeToEuclidean_snd] at this
  exact this

theorem divergence_pullSpace (F : ℝ³ → ℝ³) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x : RawSpace) :
    ∑ i : Fin 3, CKN.spatialDeriv (fun y ↦ pullSpace F y i) i x =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap (fderiv ℝ F (rawToEuclidean x))) := by
  let φ : RawSpace × ℝ → RawSpace := fun z ↦ pullSpace F z.1
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have : ContDiff ℝ (⊤ : ℕ∞) (pullSpace F) :=
      rawToEuclidean.symm.contDiff.comp (hF.comp rawToEuclidean.contDiff)
    exact this.comp contDiff_fst
  have hpush : (fun y : ℝ³ ↦ pushVector φ (y, (0 : ℝ))) = F := by
    funext y
    simp [pushVector, φ, pullSpace, rawToEuclidean_fst_symm]
  have h := trace_pushVector φ hφ (x, 0)
  rw [hpush] at h
  simp only at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem rawIsInJ {a : ℝ³ → ℝ³} (h : IsInJ a) : CKN.IsInJ (pullSpace a) := by
  obtain ⟨hmem, aSeq, hsm, hcs, hdiv, htend⟩ := h
  refine ⟨?_, fun k ↦ pullSpace (aSeq k), ?_, ?_, ?_, ?_⟩
  · exact (hmem.comp_measurePreserving rawToEuclidean_measurePreserving).continuousLinearMap_comp
      (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace)
  · intro k
    exact rawToEuclidean.symm.contDiff.comp ((hsm k).comp rawToEuclidean.contDiff)
  · intro k
    exact ((hcs k).comp_homeomorph rawToEuclidean.toHomeomorph).comp_left
      (g := (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace)) rawToEuclidean.symm.map_zero
  · intro k x
    rw [divergence_pullSpace _ (hsm k)]
    exact hdiv k _
  · have hle : ∀ k, eLpNorm (fun x ↦ pullSpace (aSeq k) x - pullSpace a x) 2 volume ≤
        eLpNorm (fun x ↦ aSeq k x - a x) 2 volume := by
      intro k
      calc
        _ ≤ eLpNorm ((fun x ↦ aSeq k x - a x) ∘ rawToEuclidean) 2 volume := by
          have hpa : AEStronglyMeasurable (pullSpace a) volume :=
            rawToEuclidean.symm.continuous.comp_aestronglyMeasurable
              (hmem.aestronglyMeasurable.comp_measurePreserving
                rawToEuclidean_measurePreserving)
          have hpk : AEStronglyMeasurable (pullSpace (aSeq k)) volume :=
            (rawToEuclidean.symm.continuous.comp
              ((hsm k).continuous.comp rawToEuclidean.continuous)).aestronglyMeasurable
          refine eLpNorm_mono (hpk.sub hpa) ?_
          intro x
          have hsub : pullSpace (aSeq k) x - pullSpace a x =
              pullSpace (fun y ↦ aSeq k y - a y) x := by
            simp [pullSpace, map_sub]
          rw [hsub]
          calc ‖pullSpace (fun y ↦ aSeq k y - a y) x‖
              ≤ CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullSpace (fun y ↦ aSeq k y - a y) x) :=
                CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _
            _ = ‖aSeq k (rawToEuclidean x) - a (rawToEuclidean x)‖ :=
                vec3EuclideanNorm_pullSpace _ _
            _ ≤ _ := by simp
        _ = _ := eLpNorm_comp_measurePreserving
          (((hsm k).continuous.aestronglyMeasurable).sub hmem.aestronglyMeasurable)
          rawToEuclidean_measurePreserving
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
      (fun _ ↦ bot_le) hle

theorem rawSliceDivFree {u : ℝ³ × ℝ → ℝ³} {s : ℝ}
    (hs : ∀ ψ ∈ testFunctions ℝ (Set.univ : Set ℝ³),
      ∫ x : ℝ³, ⟪u (x, s), ∇ ψ x⟫_ℝ = 0) :
    ∀ ψ : CKN.WeakTestFunction (Set.univ : Set RawSpace),
      ∫ x : RawSpace, ∑ i, pullVelocity u (x, s) i * ψ.partialDeriv i x = 0 := by
  intro ψ
  have hψe : pushSpatialScalar ψ.toFun ∈ testFunctions ℝ (Set.univ : Set ℝ³) := by
    have := pushSpatialScalar_testFunction (U := (Set.univ : Set RawSpace))
      ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
    rwa [euclideanSpace_univ] at this
  have h := hs _ hψe
  rw [← rawToEuclidean_measurePreserving.integral_comp
    rawToEuclidean.toHomeomorph.measurableEmbedding] at h
  rw [← h]
  congr 1
  funext x
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hg := gradient_pushSpatialScalar_apply ψ.toFun ψ.contDiff x i
  simp [pullVelocity, CKN.WeakTestFunction.partialDeriv, hg, mul_comm]

theorem rawWeakContinuity {T : ℝ} {u : ℝ³ × ℝ → ℝ³}
    (hcont : ∀ w : ℝ³ → ℝ³, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ ↦ ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ) (Icc 0 T)) :
    ∀ w : RawSpace → RawSpace, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ ↦ ∫ x : RawSpace,
        ∑ i, pullVelocity u (x, t) i * w x i) (Icc 0 T) := by
  intro w hw
  let w' : ℝ³ → ℝ³ := fun y ↦ rawToEuclidean (w (rawToEuclidean.symm y))
  have hsymm : MeasurePreserving (rawToEuclidean.symm : ℝ³ → RawSpace) volume volume :=
    rawToEuclidean_measurePreserving.symm rawToEuclidean.toHomeomorph.toMeasurableEquiv
  have hw' : MemLp w' 2 volume :=
    (hw.comp_measurePreserving hsymm).continuousLinearMap_comp
      (rawToEuclidean.toContinuousLinearMap)
  refine (hcont w' hw').congr ?_
  intro t _
  beta_reduce
  rw [← rawToEuclidean_measurePreserving.integral_comp
    rawToEuclidean.toHomeomorph.measurableEmbedding]
  congr 1
  funext x
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [w', pullVelocity, mul_comm]

theorem rawMomentumLH {T : ℝ} {u : ℝ³ × ℝ → ℝ³} {Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)}
    (hmom : ∀ φ ∈ testFunctions ℝ³ ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T),
      (∀ z : ℝ³ × ℝ, divₓ φ z = 0) →
      ∫ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 T,
        ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ = 0) :
    ∀ φ : RawPoint → RawSpace,
      φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) (Set.univ : Set RawSpace) (Ioo 0 T) →
      (∀ z : RawPoint, ∑ i, CKN.spatialPartial (fun y ↦ φ y i) i z = 0) →
      ∫ z in CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 T),
        (-(∑ i, pullVelocity u z i * CKN.timePartial (fun w ↦ φ w i) z))
          - ∑ i, ∑ j, pullVelocity u z i * pullVelocity u z j *
              CKN.spatialPartial (fun w ↦ φ w i) j z
          + ∑ i, ∑ j, pullGradient Du z i j *
              CKN.spatialPartial (fun w ↦ φ w i) j z = 0 := by
  intro φ hφ hdivφ
  have hdiv : ∀ z : ℝ³ × ℝ, divₓ (pushVector φ) z = 0 := by
    intro ze
    have h := trace_pushVector φ hφ.1 (rawSpaceTimeToEuclidean.symm ze)
    rw [snd_symm, rawToEuclidean_fst_symm] at h
    exact h.trans (hdivφ _)
  have hnew := hmom (pushVector φ) (pushVector_testFunction (Ω := Set.univ) hφ) hdiv
  have hmp := rawSpaceTime_restrict_measurePreserving (Set.univ : Set RawSpace) (Ioo 0 T)
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  rw [euclideanSpace_univ] at hmp
  rw [← hmp.integral_comp hemb] at hnew
  let old : RawSpace × ℝ → ℝ := fun z ↦
    (-(∑ i, pullVelocity u z i * CKN.timePartial (fun w ↦ φ w i) z))
      - ∑ i, ∑ j, pullVelocity u z i * pullVelocity u z j *
          CKN.spatialPartial (fun w ↦ φ w i) j z
      + ∑ i, ∑ j, pullGradient Du z i j * CKN.spatialPartial (fun w ↦ φ w i) j z
  let new : RawSpace × ℝ → ℝ := fun z ↦
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪u ze, dtφ⟫_ℝ
      + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint (u ze ⊗ᵣ u ze) ∘L Dφ))
      - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint (Du ze) ∘L Dφ))
  have hnew' : ∫ z in (Set.univ : Set RawSpace) ×ˢ Ioo 0 T, new z = 0 := by
    simpa [new] using hnew
  have hpoint (z : RawSpace × ℝ) : new z = -old z := by
    have h := momentum_integrand_transport φ hφ.1 z (pullVelocity u z) 0 0
      (Du (rawSpaceTimeToEuclidean z))
    simp only [zero_mul, add_zero, sub_zero] at h
    simp only [new, old, pullGradient, CKN.timePartial, CKN.spatialPartial]
    simpa [rawToEuclidean_pullVelocity] using h
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change (∫ z : RawSpace × ℝ in (Set.univ : Set RawSpace) ×ˢ Ioo 0 T, old z) = 0
  calc
    _ = ∫ z in (Set.univ : Set RawSpace) ×ˢ Ioo 0 T, -new z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hpoint]
      simp
    _ = -∫ z in (Set.univ : Set RawSpace) ×ˢ Ioo 0 T, new z := integral_neg _
    _ = 0 := by rw [hnew']; simp

theorem lintegral_pullSpace_sq (a : ℝ³ → ℝ³) :
    ∫⁻ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpace a x)) ^ (2 : ℝ) =
      ∫⁻ y : ℝ³, ‖a y‖ₑ ^ (2 : ℝ) := by
  have h : ∀ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpace a x)) ^ (2 : ℝ) =
      (fun y : ℝ³ ↦ ‖a y‖ₑ ^ (2 : ℝ)) (rawToEuclidean x) := by
    intro x
    simp only [vec3EuclideanNorm_pullSpace, ofReal_norm]
  simp_rw [h]
  exact lintegral_space_transport (fun y : ℝ³ ↦ ‖a y‖ₑ ^ (2 : ℝ))

theorem lintegral_slice_pull_univ (t : ℝ) (u : ℝ³ × ℝ → ℝ³) (r : ℝ) :
    ∫⁻ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ r =
      ∫⁻ y : ℝ³, ‖u (y, t)‖ₑ ^ r := by
  have := lintegral_slice_pull Set.univ t u r
  simpa [euclideanSpace_univ] using this

theorem rawLerayHopf {T : ℝ} {a : ℝ³ → ℝ³} {u : ℝ³ × ℝ → ℝ³}
    {Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)} (h : IsLerayHopfSolution T a u Du) :
    CKN.IsLerayHopfSolution T (pullSpace a) (pullVelocity u) (pullGradient Du) := by
  obtain ⟨hT, ha, hu, hDu, hsup, hL2, hweak, hdiv, hcont, hmom, hen, hinit⟩ := h
  refine ⟨hT, rawIsInJ ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aesm_pullVelocity (U := Set.univ) (by rwa [euclideanSpace_univ])
  · exact aesm_pullGradient (U := Set.univ) (by rwa [euclideanSpace_univ])
  · refine lt_of_le_of_lt (essSup_mono_ae (Eventually.of_forall fun s ↦ ?_)) hsup
    have := lintegral_slice_pull_le Set.univ s u (r := 2) (by norm_num)
    simpa [euclideanSpace_univ] using this
  · have := lintegral_energy_pull_le Set.univ (Ioo 0 T) u Du
    rw [euclideanSpace_univ] at this
    exact lt_of_le_of_lt this hL2
  · filter_upwards [hweak] with s hs
    exact weakGradient_transport (U := Set.univ) (by rwa [euclideanSpace_univ])
  · filter_upwards [hdiv] with s hs
    exact rawSliceDivFree hs
  · exact rawWeakContinuity hcont
  · exact rawMomentumLH hmom
  · intro t₀ ht₀
    have h := hen t₀ ht₀
    have e1 := lintegral_slice_pull_univ t₀ u 2
    have e3 := lintegral_pullSpace_sq a
    have e2 : ∫⁻ z in CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 t₀),
        ENNReal.ofReal (CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z) =
        ∫⁻ z in (Set.univ : Set ℝ³) ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ := by
      have := lintegral_spaceTimeSet_transport (Set.univ : Set RawSpace) (Ioo 0 t₀)
        (fun z ↦ ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ)
      rw [euclideanSpace_univ] at this
      rw [← this]
      apply lintegral_congr
      intro z
      congr 1
      exact rawGradient_sq _
    rw [e1, e2, e3]
    exact h
  · refine hinit.congr (fun t ↦ ?_)
    have h : ∀ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm
          (pullVelocity u (x, t) - pullSpace a x)) ^ (2 : ℝ) =
        (fun y : ℝ³ ↦ ‖u (y, t) - a y‖ₑ ^ (2 : ℝ)) (rawToEuclidean x) := by
      intro x
      have : pullVelocity u (x, t) - pullSpace a x =
          rawToEuclidean.symm (u (rawToEuclidean x, t) - a (rawToEuclidean x)) := by
        simp [pullVelocity, pullSpace, map_sub]
      simp only [this, vec3EuclideanNorm_rawToEuclidean_symm, ofReal_norm]
    simp_rw [h]
    exact (lintegral_space_transport (fun y : ℝ³ ↦ ‖u (y, t) - a y‖ₑ ^ (2 : ℝ))).symm

theorem rawEssL3 {T : ℝ} {u : ℝ³ × ℝ → ℝ³}
    (h : essSup (fun t : ℝ ↦ ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ∞) :
    essSup (fun t : ℝ ↦ ∫⁻ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ := by
  have : (fun t : ℝ ↦ ∫⁻ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ)) =
      fun t : ℝ ↦ ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ) :=
    funext fun t ↦ lintegral_slice_pull_univ t u 3
  rw [this]
  exact h

theorem rawEssLPS {T : ℝ} {u : ℝ³ × ℝ → ℝ³}
    (h : (∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ s) ^ ((2 * s / (s - 3)) / s)) < ∞) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : ℝ³ => ‖u (x, t)‖ₑ) (volume : Measure ℝ³)) ^
            (2 : ℝ)) < ∞) :
    ((∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : RawSpace, ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity u (x, t))) ^ s) ^ ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : RawSpace => ENNReal.ofReal
            (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))))
            (volume : Measure RawSpace)) ^ (2 : ℝ)) < ⊤) := by
  rcases h with ⟨s, hs, h⟩ | h
  · left
    refine ⟨s, hs, ?_⟩
    simp_rw [lintegral_slice_pull_univ _ u s]
    exact h
  · right
    have hess : ∀ t : ℝ, essSup (fun x : RawSpace => ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))))
          (volume : Measure RawSpace) =
        essSup (fun x : ℝ³ => ‖u (x, t)‖ₑ) (volume : Measure ℝ³) := by
      intro t
      have := rawToEuclidean.toHomeomorph.measurableEmbedding.essSup_map_measure
        (μ := (volume : Measure RawSpace)) (g := fun y : ℝ³ ↦ ‖u (y, t)‖ₑ)
      have hmap : Measure.map (⇑rawToEuclidean.toHomeomorph)
          (volume : Measure RawSpace) = volume :=
        rawToEuclidean_measurePreserving.map_eq
      rw [hmap] at this
      rw [this]
      congr 1
      funext x
      simp only [Function.comp_apply, vec3EuclideanNorm_pullVelocity, ofReal_norm,
        rawSpaceTimeToEuclidean_apply]
      rfl
    simp_rw [hess]
    exact h

theorem memLp_push_univ {T : ℝ} {g : RawSpace × ℝ → RawSpace} {p : ℝ≥0∞}
    (h : MemLp g p ((volume : Measure RawPoint).restrict
      (CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 T)))) :
    MemLp (pushVector g) p
      (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)) := by
  unfold CKN.spaceTimeSet at h
  rw [volume_rawPoint_eq_product] at h
  have hmp := rawSpaceTime_restrict_measurePreserving (Set.univ : Set RawSpace) (Ioo 0 T)
  rw [euclideanSpace_univ] at hmp
  have hsymm : MeasurePreserving (rawSpaceTimeToEuclidean.symm : ℝ³ × ℝ → RawSpace × ℝ)
      (volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T))
      (volume.restrict ((Set.univ : Set RawSpace) ×ˢ Ioo 0 T)) :=
    hmp.symm rawSpaceTimeToEuclidean.toMeasurableEquiv
  exact (h.continuousLinearMap_comp
    (rawToEuclidean.toContinuousLinearMap)).comp_measurePreserving hsymm

theorem aeEq_push_univ {T : ℝ} {g g' : RawSpace × ℝ → RawSpace}
    (h : g =ᵐ[(volume : Measure RawPoint).restrict
      (CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 T))] g') :
    pushVector g =ᵐ[volume.restrict ((Set.univ : Set ℝ³) ×ˢ Ioo 0 T)] pushVector g' := by
  unfold CKN.spaceTimeSet at h
  rw [volume_rawPoint_eq_product] at h
  have hmp := rawSpaceTime_restrict_measurePreserving (Set.univ : Set RawSpace) (Ioo 0 T)
  rw [euclideanSpace_univ] at hmp
  rw [← hmp.map_eq]
  apply rawSpaceTimeToEuclidean.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [h] with z hz
  have hz' : g z = g' z := hz
  rw [pushVector_rawSpaceTimeToEuclidean, pushVector_rawSpaceTimeToEuclidean, hz']

theorem contDiffOn_push_univ {T : ℝ} {w : RawSpace × ℝ → RawSpace}
    (h : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : RawSpace × ℝ ↦ w z)
      ((Set.univ : Set RawSpace) ×ˢ Ioc (0 : ℝ) T)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pushVector w) ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T) := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (rawSpaceTimeLinear.symm : ℝ³ × ℝ → RawSpace × ℝ)
      ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T) :=
    rawSpaceTimeLinear.symm.contDiff.contDiffOn
  have hmaps : MapsTo (rawSpaceTimeLinear.symm : ℝ³ × ℝ → RawSpace × ℝ)
      ((Set.univ : Set ℝ³) ×ˢ Ioc (0 : ℝ) T)
      ((Set.univ : Set RawSpace) ×ˢ Ioc (0 : ℝ) T) := by
    intro z hz
    exact ⟨trivial, hz.2⟩
  exact rawToEuclidean.contDiff.comp_contDiffOn (h.comp hf hmaps)

theorem singularSet_push_univ {T : ℝ} {u : ℝ³ × ℝ → ℝ³}
    (h : CKN.SingularSet (Set.univ : Set RawSpace) (Ioo 0 T) (pullVelocity u) = ∅) :
    singularSet (Set.univ : Set ℝ³) (Ioo 0 T) u = ∅ := by
  ext ze
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hze, hnot⟩
  let z : RawPoint := parabolicToEuclideanHomeomorph.symm ze
  have hz : z ∈ CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 T) := by
    have h2 : (parabolicToEuclideanHomeomorph z) = ze :=
      parabolicToEuclideanHomeomorph.apply_symm_apply ze
    change z.1 ∈ (Set.univ : Set RawSpace) ∧ z.2 ∈ Ioo 0 T
    refine ⟨trivial, ?_⟩
    have := hze.2
    rw [← h2] at this
    exact this
  by_cases hreg : CKN.IsRegularPoint (Set.univ : Set RawSpace) (Ioo 0 T) (pullVelocity u) z
  · apply hnot
    have := isHolderRegularPoint_of_rawRegular (Ω := (Set.univ : Set ℝ³)) (I := Ioo 0 T)
      (u := u) (z₀ := z) hreg
    rwa [show parabolicToEuclideanHomeomorph z = ze from
      parabolicToEuclideanHomeomorph.apply_symm_apply ze] at this
  · have : z ∈ CKN.SingularSet (Set.univ : Set RawSpace) (Ioo 0 T) (pullVelocity u) :=
      ⟨hz, hreg⟩
    rw [h] at this
    exact this

theorem rawDivergenceFree {Ω : Set ℝ³} {I : Set ℝ} {u : ℝ³ × ℝ → ℝ³}
    (hinc : ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I),
      ∫ z in Ω ×ˢ I, ⟪u z, ∇ₓ ψ z⟫_ℝ = 0) :
    ∀ ψ : RawPoint → ℝ,
      ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) (rawSpace Ω) I →
      ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
        ∑ i, pullVelocity u z i * CKN.spatialPartial ψ i z = 0 := by
  intro ψ hψ
  have hnew := hinc (pushScalar ψ) (pushScalar_testFunction hψ)
  have hmp := rawSpaceTime_restrict_measurePreserving (rawSpace Ω) I
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  simp only [euclideanSpace_rawSpace] at hmp
  rw [← hmp.integral_comp hemb] at hnew
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change (∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I,
    ∑ i, pullVelocity u z i * CKN.spatialPartial ψ i z) = 0
  calc
    _ = ∫ z in rawSpace Ω ×ˢ I,
        ⟪u (rawToEuclidean z.1, z.2),
          gradient (fun x : ℝ³ ↦
            pushScalar ψ (x, z.2)) (rawToEuclidean z.1)⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards with z
      have hi := inner_pushScalar_gradient ψ hψ.1 z (pullVelocity u z)
      rw [rawToEuclidean_pullVelocity] at hi
      simpa [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
        ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply, CKN.spatialPartial] using
          hi.symm
    _ = 0 := by
      simpa [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
        ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply] using hnew

theorem rawMomentumPressure {Ω : Set ℝ³} {I : Set ℝ} {u : ℝ³ × ℝ → ℝ³}
    {Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)} {p : ℝ³ × ℝ → ℝ}
    (hmom : ∀ φ ∈ testFunctions ℝ³ (Ω ×ˢ I),
      ∫ z in Ω ×ˢ I,
        ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ
          + p z * divₓ φ z = 0) :
    ∀ φ : RawPoint → RawSpace,
      φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) (rawSpace Ω) I →
      ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
        (-(∑ i, pullVelocity u z i * CKN.timePartial (fun w ↦ φ w i) z))
          - ∑ i, ∑ j, pullVelocity u z i * pullVelocity u z j *
              CKN.spatialPartial (fun w ↦ φ w i) j z
          + ∑ i, ∑ j, pullGradient Du z i j *
              CKN.spatialPartial (fun w ↦ φ w i) j z
          - pullScalar p z * ∑ i, CKN.spatialPartial (fun w ↦ φ w i) i z
          - ∑ i, ((0 : RawPoint → RawSpace) z i) * φ z i = 0 := by
  intro φ hφ
  have hnew := hmom (pushVector φ) (pushVector_testFunction hφ)
  have hmp := rawSpaceTime_restrict_measurePreserving (rawSpace Ω) I
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  simp only [euclideanSpace_rawSpace] at hmp
  rw [← hmp.integral_comp hemb] at hnew
  let old : RawSpace × ℝ → ℝ := fun z ↦
    (-(∑ i, pullVelocity u z i * CKN.timePartial (fun w ↦ φ w i) z))
      - ∑ i, ∑ j, pullVelocity u z i * pullVelocity u z j *
          CKN.spatialPartial (fun w ↦ φ w i) j z
      + ∑ i, ∑ j, pullGradient Du z i j * CKN.spatialPartial (fun w ↦ φ w i) j z
      - pullScalar p z * ∑ i, CKN.spatialPartial (fun w ↦ φ w i) i z
      - ∑ i, ((0 : RawPoint → RawSpace) z i) * φ z i
  let new : RawSpace × ℝ → ℝ := fun z ↦
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪u ze, dtφ⟫_ℝ
      + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint (u ze ⊗ᵣ u ze) ∘L Dφ))
      - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint (Du ze) ∘L Dφ))
      + p ze * LinearMap.trace ℝ ℝ³ Dφ.toLinearMap
  have hnew' : ∫ z in rawSpace Ω ×ˢ I, new z = 0 := by
    simpa [new] using hnew
  have hpoint (z : RawSpace × ℝ) : new z = -old z := by
    have h := momentum_integrand_transport φ hφ.1 z (pullVelocity u z) 0
      (pullScalar p z) (Du (rawSpaceTimeToEuclidean z))
    have h0 : ∑ i, ((0 : RawPoint → RawSpace) z i) * φ z i = 0 :=
      Finset.sum_eq_zero (fun i _ ↦ by
        rw [show ((0 : RawPoint → RawSpace) z i) = 0 from rfl, zero_mul])
    simp only [old, new, pullGradient, pullScalar, CKN.timePartial, CKN.spatialPartial]
    rw [h0]
    simpa [rawToEuclidean_pullVelocity, pullScalar] using h
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change (∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I, old z) = 0
  calc
    _ = ∫ z in rawSpace Ω ×ˢ I, -new z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hpoint]
      simp
    _ = -∫ z in rawSpace Ω ×ˢ I, new z := integral_neg _
    _ = 0 := by rw [hnew']; simp

theorem pushVector_aeHolderNorm_half_lt_top
    {u : ℝ³ × ℝ → ℝ³} {w : RawSpace × ℝ → RawSpace} {γ : ℝ} (hγ : 0 < γ)
    (hae : w =ᵐ[(volume : Measure RawPoint).restrict
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2))]
      pullVelocity u)
    (hholder : CKN.ParabolicHolderVecOn
      (closure (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2))) w γ) :
    aeHolderNormOn (closure (Q (1 / 2))) u
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ < ∞ := by
  rcases hholder with ⟨B, K, hB, hK, hsup, hseminorm⟩
  have haeQ : pushVector w =ᵐ[
      (volume : Measure (ℝ³ × ℝ)).restrict (Q (1 / 2))] u := by
    apply pushVector_aeEq_on_Q (r := 1 / 2) (z₀ := 0)
    have hc : rawToEuclidean.symm (0 : ℝ³) = (0 : RawSpace) := by simp
    simpa only [Prod.fst_zero, Prod.snd_zero, hc] using hae
  have haeClosure : pushVector w =ᵐ[
      (volume : Measure (ℝ³ × ℝ)).restrict (closure (Q (1 / 2)))] u := by
    have hmeas := Measure.restrict_congr_set
      (Q_aeEq_closure (by norm_num : (0 : ℝ) < 1 / 2) (0 : ℝ³ × ℝ))
    rw [← hmeas]
    exact haeQ
  have hHolder := (pushVector_holderOnWith_half hγ.le hK hseminorm).holderWith
  have hHolderNorm :
      eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
          ((closure (Q (1 / 2))).domRestrict (pushVector w)) ≤
        ENNReal.ofReal K := by
    rw [ENNReal.ofReal_eq_coe_nnreal hK]
    exact hHolder.eHolderNorm_le
  unfold aeHolderNormOn
  calc
    (⨅ (v : ℝ³ × ℝ → ℝ³)
        (_ : v =ᵐ[volume.restrict (closure (Q (1 / 2)))] u),
        (⨆ z : closure (Q (1 / 2)), ‖v z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((closure (Q (1 / 2))).domRestrict v)) ≤
        (⨆ z : closure (Q (1 / 2)), ‖pushVector w z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((closure (Q (1 / 2))).domRestrict (pushVector w)) :=
      iInf_le_of_le (pushVector w) (iInf_le_of_le haeClosure le_rfl)
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal K :=
      add_le_add (iSup_le (pushVector_enorm_le_half hsup)) hHolderNorm
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

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
  by
  intro u Du p hu hDu hp hL2 hE2 hpMem hL3 hweak hinc hmom
  have hE : euclideanSpace (CKN.Foundation.Parabolic.vec3Ball 0 1) =
      Metric.ball (0 : ℝ³) 1 := by
    rw [← rawSpace_ball, euclideanSpace_rawSpace]
  have key := ESS.essLocal (pullVelocity u) (pullGradient Du) (pullScalar p)
  obtain ⟨γ, hγ, hγ1, w, hw, hholder⟩ := key
    (aesm_pullVelocity (by rw [hE]; exact hu))
    (aesm_pullGradient (by rw [hE]; exact hDu))
    (aesm_pullScalar (by rw [hE]; exact hp))
    (by
      refine lt_of_le_of_lt (essSup_mono_ae (Eventually.of_forall fun t ↦ ?_)) hL2
      have := lintegral_slice_pull_le (CKN.Foundation.Parabolic.vec3Ball 0 1) t u
        (r := 2) (by norm_num)
      rwa [hE] at this)
    (by
      have := lintegral_energy_pull_le (CKN.Foundation.Parabolic.vec3Ball 0 1)
        (Ioo (-1) 0) u Du
      rw [hE] at this
      exact lt_of_le_of_lt this hE2)
    (memLp_pullScalar (by rw [hE]; exact hpMem))
    (by
      have : (fun t : ℝ ↦ ∫⁻ x in CKN.Foundation.Parabolic.vec3Ball 0 1, ENNReal.ofReal
            (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ)) =
          fun t : ℝ ↦ ∫⁻ x in Metric.ball (0 : ℝ³) 1, ‖u (x, t)‖ₑ ^ (3 : ℝ) :=
        funext fun t ↦ by rw [lintegral_slice_pull, hE]
      rw [this]
      exact hL3)
    (by
      filter_upwards [hweak] with t ht
      exact weakGradient_transport (by rw [hE]; exact ht))
    (by
      have := rawDivergenceFree hinc
      rw [rawSpace_ball] at this
      exact this)
    (by
      have := rawMomentumPressure hmom
      rw [rawSpace_ball] at this
      exact this)
  refine ⟨⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩, ?_, ?_,
    pushVector_aeHolderNorm_half_lt_top hγ hw hholder⟩
  · exact div_pos hγ (by norm_num)
  · change γ / 2 ≤ (1 : ℝ)
    linarith

/-- The global Escauriaza–Seregin–Šverák regularity theorem `thm:ess-global`. -/
theorem essGlobal :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ∞ →
      singularSet (Set.univ : Set ℝ³) (Ioo 0 T) u = ∅ :=
  by
  intro T a u Du hLH hL3
  exact singularSet_push_univ
    (ESS.essGlobal T (pullSpace a) (pullVelocity u) (pullGradient Du)
      (rawLerayHopf hLH) (rawEssL3 hL3))

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
  by
  intro T a u Du hLH hL3
  obtain ⟨hL5, huniq⟩ := ESS.essL5Unique T (pullSpace a) (pullVelocity u)
    (pullGradient Du) (rawLerayHopf hLH) (rawEssL3 hL3)
  refine ⟨?_, ?_⟩
  · have := memLp_push_univ hL5
    rwa [pushVector_pullVelocity, ENNReal.ofReal_ofNat] at this
  · intro v Dv hv
    have := aeEq_push_univ (huniq (pullVelocity v) (pullGradient Dv) (rawLerayHopf hv))
    simpa only [pushVector_pullVelocity] using this

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
  by
  intro T a u Du hLH hs
  obtain ⟨huniq, w, hw, hsm⟩ := ESS.ladyzhenskayaProdiSerrin T (pullSpace a)
    (pullVelocity u) (pullGradient Du) (rawLerayHopf hLH) (rawEssLPS hs)
  refine ⟨?_, pushVector w, ?_, contDiffOn_push_univ hsm⟩
  · intro v Dv hv
    have := aeEq_push_univ (huniq (pullVelocity v) (pullGradient Dv) (rawLerayHopf hv))
    simpa only [pushVector_pullVelocity] using this
  · have := aeEq_push_univ hw
    simpa only [pushVector_pullVelocity] using this

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
  by
  intro T a u Du hLH hL3
  obtain ⟨hL5, huniq, w, hw, hsm⟩ := ESS.essSmooth T (pullSpace a) (pullVelocity u)
    (pullGradient Du) (rawLerayHopf hLH) (rawEssL3 hL3)
  refine ⟨?_, ?_, pushVector w, ?_, contDiffOn_push_univ hsm⟩
  · have := memLp_push_univ hL5
    rwa [pushVector_pullVelocity, ENNReal.ofReal_ofNat] at this
  · intro v Dv hv
    have := aeEq_push_univ (huniq (pullVelocity v) (pullGradient Dv) (rawLerayHopf hv))
    simpa only [pushVector_pullVelocity] using this
  · have := aeEq_push_univ hw
    simpa only [pushVector_pullVelocity] using this

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
  by
  intro T a u Du hLH hs
  have hs' : ((essSup (fun t : ℝ ↦ ∫⁻ x : RawSpace, ENNReal.ofReal
        (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤) ∨
      (∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : RawSpace, ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity u (x, t))) ^ s) ^ ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup (fun x : RawSpace => ENNReal.ofReal
            (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))))
            (volume : Measure RawSpace)) ^ (2 : ℝ)) < ⊤) := by
    rcases hs with hA | hBC
    · exact Or.inl (rawEssL3 hA)
    · exact Or.inr (rawEssLPS hBC)
  obtain ⟨huniq, w, hw, hsm⟩ := ESS.serrinCriterion T (pullSpace a)
    (pullVelocity u) (pullGradient Du) (rawLerayHopf hLH) hs'
  refine ⟨?_, pushVector w, ?_, contDiffOn_push_univ hsm⟩
  · intro v Dv hv
    have := aeEq_push_univ (huniq (pullVelocity v) (pullGradient Dv) (rawLerayHopf hv))
    simpa only [pushVector_pullVelocity] using this
  · have := aeEq_push_univ hw
    simpa only [pushVector_pullVelocity] using this


end ESSChallenge
