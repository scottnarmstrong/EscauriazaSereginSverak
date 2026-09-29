-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Statements.UniqueContinuation
public import ESS.Statements.BackwardUniqueness
public import ESS.Statements.CarlemanGaussian
public import ESS.Statements.CarlemanHalfSpace
public import CKN.Statements.HasSpaceTimeWeakDerivs
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

open CKN

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

/-! ## Transport to the library's coordinates

The library states the same theorems for functions on the product `(Fin 3 → ℝ) × ℝ`
(carried by its parabolic space-time point type), with derivatives taken coordinate-wise.
The maps below identify `EuclideanSpace ℝ (Fin 3) × ℝ` with that space linearly,
homeomorphically and measure-preservingly, and every notion of the statements above is then
shown to agree with the corresponding library notion. -/

/-- The linear homeomorphism from `ℝ³ × ℝ` to the library's ordinary product
`(Fin 3 → ℝ) × ℝ`. -/
def spaceTimeEquiv : (EuclideanSpace ℝ (Fin 3) × ℝ) ≃L[ℝ] ((Fin 3 → ℝ) × ℝ) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

/-- The same identification as a measurable equivalence. -/
def spaceTimeMeasurableEquiv : (EuclideanSpace ℝ (Fin 3) × ℝ) ≃ᵐ ((Fin 3 → ℝ) × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr (MeasurableEquiv.refl ℝ)

theorem spaceTimeMeasurableEquiv_apply (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    spaceTimeMeasurableEquiv z = spaceTimeEquiv z := rfl

theorem spaceTimeEquiv_apply (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    spaceTimeEquiv z = (z.1.ofLp, z.2) := rfl

theorem spaceTimeMeasurePreserving :
    MeasurePreserving spaceTimeMeasurableEquiv
      (volume : Measure (EuclideanSpace ℝ (Fin 3) × ℝ))
      (volume : Measure ((Fin 3 → ℝ) × ℝ)) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).prod (MeasurePreserving.id volume)

/-- The identification of `ℝ³ × ℝ` with the library's space-time point type. -/
def spaceTimeHomeo : (EuclideanSpace ℝ (Fin 3) × ℝ) ≃ₜ ((Fin 3 → ℝ) × ℝ) :=
  spaceTimeEquiv.toHomeomorph

theorem spaceTimeHomeo_apply (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    spaceTimeHomeo z = (z.1.ofLp, z.2) := rfl

theorem spaceTimeHomeo_symm_apply (p : (Fin 3 → ℝ) × ℝ) :
    spaceTimeHomeo.symm p = (WithLp.toLp 2 p.1, p.2) := rfl

theorem spaceTimeMeasurePreservingP :
    MeasurePreserving spaceTimeMeasurableEquiv
      (volume : Measure (EuclideanSpace ℝ (Fin 3) × ℝ))
      (volume : Measure CKN.Foundation.Parabolic.ParabolicPoint) :=
  spaceTimeMeasurePreserving

theorem spatialDeriv_comp (g : (Fin 3 → ℝ) × ℝ → ℝ) (j : Fin 3)
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    spatialDeriv (g ∘ spaceTimeHomeo) j z = CKN.spatialPartial g j (spaceTimeHomeo z) := by
  unfold spatialDeriv CKN.spatialPartial
  have h : (fun x : EuclideanSpace ℝ (Fin 3) => (g ∘ spaceTimeHomeo) (x, z.2)) =
      (fun x' : Fin 3 → ℝ => g (x', z.2)) ∘ (EuclideanSpace.equiv (Fin 3) ℝ) := rfl
  rw [h, ContinuousLinearEquiv.comp_right_fderiv]
  change (fderiv ℝ (fun x' : Fin 3 → ℝ => g (x', z.2)) z.1.ofLp)
      (EuclideanSpace.single j 1).ofLp = _
  rw [PiLp.ofLp_single]
  rfl

theorem timeDeriv_comp (g : (Fin 3 → ℝ) × ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    timeDeriv (g ∘ spaceTimeHomeo) z = CKN.timePartial g (spaceTimeHomeo z) := rfl

theorem vec3EuclideanNorm_ofLp (v : EuclideanSpace ℝ (Fin 3)) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm v.ofLp = ‖v‖ := by
  rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]

theorem norm_ofLp_le (v : EuclideanSpace ℝ (Fin 3)) : ‖v.ofLp‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => PiLp.norm_apply_le v i

theorem enorm_ofLp_le (v : EuclideanSpace ℝ (Fin 3)) : ‖v.ofLp‖ₑ ≤ ‖v‖ₑ :=
  enorm_le_iff_norm_le.2 (norm_ofLp_le v)

theorem preimage_spaceTimeSet (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ) :
    spaceTimeHomeo ⁻¹' CKN.spaceTimeSet Ω' I = Ω ×ˢ I := by
  ext z
  show (z.1.ofLp ∈ Ω' ∧ z.2 ∈ I) ↔ z.1 ∈ Ω ∧ z.2 ∈ I
  rw [hΩ z.1]

theorem symm_preimage_spaceTimeSet (Ω : Set (EuclideanSpace ℝ (Fin 3)))
    (Ω' : Set (Fin 3 → ℝ)) (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω)
    (I : Set ℝ) : spaceTimeHomeo.symm ⁻¹' (Ω ×ˢ I) = CKN.spaceTimeSet Ω' I := by
  ext p
  have h := spaceTimeHomeo.apply_symm_apply p
  rw [← preimage_spaceTimeSet Ω Ω' hΩ I]
  change spaceTimeHomeo (spaceTimeHomeo.symm p) ∈ CKN.spaceTimeSet Ω' I ↔ _
  rw [h]
  exact Iff.rfl

theorem lintegral_transport (T : Set CKN.Foundation.Parabolic.ParabolicPoint)
    (F : CKN.Foundation.Parabolic.ParabolicPoint → ℝ≥0∞) :
    ∫⁻ p in T, F p = ∫⁻ z in spaceTimeHomeo ⁻¹' T, F (spaceTimeHomeo z) :=
  (spaceTimeMeasurePreservingP.setLIntegral_comp_preimage_emb
    spaceTimeMeasurableEquiv.measurableEmbedding F T).symm

theorem integral_transport (T : Set CKN.Foundation.Parabolic.ParabolicPoint)
    (F : CKN.Foundation.Parabolic.ParabolicPoint → ℝ) :
    ∫ p in T, F p = ∫ z in spaceTimeHomeo ⁻¹' T, F (spaceTimeHomeo z) :=
  (spaceTimeMeasurePreservingP.setIntegral_preimage_emb
    spaceTimeMeasurableEquiv.measurableEmbedding F T).symm

theorem ae_transport (T : Set ((Fin 3 → ℝ) × ℝ)) (P : (Fin 3 → ℝ) × ℝ → Prop)
    (h : ∀ᵐ z ∂(volume.restrict (spaceTimeHomeo ⁻¹' T)), P (spaceTimeHomeo z)) :
    ∀ᵐ p ∂(volume.restrict T), P p := by
  have hmp := (spaceTimeMeasurePreservingP.restrict_preimage_emb
    spaceTimeMeasurableEquiv.measurableEmbedding T)
  have := hmp.symm spaceTimeMeasurableEquiv |>.quasiMeasurePreserving.ae h
  filter_upwards [this] with p hp
  have e : spaceTimeHomeo (spaceTimeMeasurableEquiv.symm p) = p :=
    MeasurableEquiv.apply_symm_apply spaceTimeMeasurableEquiv p
  rwa [e] at hp

/-- The identification of `ℝ³ × ℝ` with the library's space-time point type, whose
topology is the parabolic one (the same as the product topology). -/
def spaceTimeHomeoP : (EuclideanSpace ℝ (Fin 3) × ℝ) ≃ₜ
    CKN.Foundation.Parabolic.ParabolicPoint :=
  spaceTimeHomeo.trans CKN.Foundation.Parabolic.parabolicHomeomorph.symm

theorem locallyIntegrableOn_transport {E : Type*} [NormedAddCommGroup E]
    (S : Set (EuclideanSpace ℝ (Fin 3) × ℝ)) (f : EuclideanSpace ℝ (Fin 3) × ℝ → E)
    (hf : LocallyIntegrableOn f S) :
    LocallyIntegrableOn (f ∘ spaceTimeHomeoP.symm) (spaceTimeHomeoP.symm ⁻¹' S) := by
  intro p hp
  obtain ⟨t, ht, hint⟩ := hf (spaceTimeHomeoP.symm p) hp
  refine ⟨spaceTimeHomeoP.symm ⁻¹' t, ?_, ?_⟩
  · have hc : Filter.Tendsto spaceTimeHomeoP.symm (nhdsWithin p (spaceTimeHomeoP.symm ⁻¹' S))
        (nhdsWithin (spaceTimeHomeoP.symm p) S) :=
      spaceTimeHomeoP.symm.continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
    exact hc ht
  · have hmp : MeasurePreserving spaceTimeMeasurableEquiv.symm volume volume :=
      spaceTimeMeasurePreservingP.symm _
    have hmp' := hmp.restrict_preimage_emb spaceTimeMeasurableEquiv.symm.measurableEmbedding t
    exact (hmp'.integrable_comp_emb spaceTimeMeasurableEquiv.symm.measurableEmbedding).2 hint

theorem tsupport_comp_homeomorph {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero V] (h : X ≃ₜ Y) (f : Y → V) : tsupport (f ∘ h) = h ⁻¹' tsupport f := by
  unfold tsupport
  rw [Function.support_comp_eq_preimage, ← h.preimage_closure]

theorem testFunction_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (φ : (Fin 3 → ℝ) × ℝ → V) (h : φ ∈ CKN.spaceTimeTestFunction (V := V) Ω' I) :
    φ ∘ spaceTimeHomeo ∈ testFunctions (Y := V) Ω I := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.comp spaceTimeEquiv.contDiff, h2.comp_homeomorph spaceTimeEquiv.toHomeomorph, ?_⟩
  have e := tsupport_comp_homeomorph spaceTimeHomeo φ
  have hp : spaceTimeHomeo ⁻¹' ((Ω' ×ˢ I : Set ((Fin 3 → ℝ) × ℝ))) = Ω ×ˢ I :=
    preimage_spaceTimeSet Ω Ω' hΩ I
  refine (subset_of_eq e).trans ?_
  rw [← hp]
  exact preimage_mono h3

theorem testFunction_symm_comp (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (h : w ∈ testFunctions (Y := EuclideanSpace ℝ (Fin 3)) Ω I) :
    (fun p : (Fin 3 → ℝ) × ℝ => (w (spaceTimeHomeo.symm p)).ofLp) ∈
      CKN.spaceTimeTestFunction (V := Fin 3 → ℝ) Ω' I := by
  obtain ⟨h1, h2, h3⟩ := h
  have hL : (EuclideanSpace.equiv (Fin 3) ℝ) (0 : EuclideanSpace ℝ (Fin 3)) = 0 := map_zero _
  refine ⟨(EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp (h1.comp spaceTimeEquiv.symm.contDiff),
    (h2.comp_homeomorph spaceTimeEquiv.symm.toHomeomorph).comp_left hL, ?_⟩
  refine (tsupport_comp_subset hL _).trans ?_
  have e := tsupport_comp_homeomorph spaceTimeHomeo.symm w
  have hp : spaceTimeHomeo.symm ⁻¹' ((Ω ×ˢ I : Set (EuclideanSpace ℝ (Fin 3) × ℝ))) =
      (Ω' ×ˢ I : Set ((Fin 3 → ℝ) × ℝ)) := symm_preimage_spaceTimeSet Ω Ω' hΩ I
  refine (subset_of_eq e).trans ?_
  exact (preimage_mono h3).trans hp.subset

theorem spatial_pairing (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (f g : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) (φ : (Fin 3 → ℝ) × ℝ → ℝ) (j : Fin 3)
    (h : ∫ z in Ω ×ˢ I, f z * spatialDeriv (φ ∘ spaceTimeHomeo) j z =
      -∫ z in Ω ×ˢ I, g z * (φ ∘ spaceTimeHomeo) z) :
    ∫ p in CKN.spaceTimeSet Ω' I, f (spaceTimeHomeo.symm p) * CKN.spatialPartial φ j p =
      -∫ p in CKN.spaceTimeSet Ω' I, g (spaceTimeHomeo.symm p) * φ p := by
  rw [integral_transport _ (fun p => f (spaceTimeHomeo.symm p) * CKN.spatialPartial φ j p),
    integral_transport _ (fun p => g (spaceTimeHomeo.symm p) * φ p),
    preimage_spaceTimeSet Ω Ω' hΩ I]
  simpa [spatialDeriv_comp] using h

theorem time_pairing (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (f g : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) (φ : (Fin 3 → ℝ) × ℝ → ℝ)
    (h : ∫ z in Ω ×ˢ I, f z * timeDeriv (φ ∘ spaceTimeHomeo) z =
      -∫ z in Ω ×ˢ I, g z * (φ ∘ spaceTimeHomeo) z) :
    ∫ p in CKN.spaceTimeSet Ω' I, f (spaceTimeHomeo.symm p) * CKN.timePartial φ p =
      -∫ p in CKN.spaceTimeSet Ω' I, g (spaceTimeHomeo.symm p) * φ p := by
  rw [integral_transport _ (fun p => f (spaceTimeHomeo.symm p) * CKN.timePartial φ p),
    integral_transport _ (fun p => g (spaceTimeHomeo.symm p) * φ p),
    preimage_spaceTimeSet Ω Ω' hΩ I]
  simpa [timeDeriv_comp] using h

theorem hasSpaceTimeWeakDerivs_transport (Ω : Set (EuclideanSpace ℝ (Fin 3)))
    (Ω' : Set (Fin 3 → ℝ)) (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω)
    (I : Set ℝ) (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (Dw : EuclideanSpace ℝ (Fin 3) × ℝ → Fin 3 → Fin 3 → ℝ)
    (D2w : EuclideanSpace ℝ (Fin 3) × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Dtw : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (h : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    CKN.HasSpaceTimeWeakDerivs Ω' I (fun p => (w (spaceTimeHomeo.symm p)).ofLp)
      (fun p => Dw (spaceTimeHomeo.symm p)) (fun p => D2w (spaceTimeHomeo.symm p))
      (fun p => (Dtw (spaceTimeHomeo.symm p)).ofLp) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hs := symm_preimage_spaceTimeSet Ω Ω' hΩ I
  have hs' := preimage_spaceTimeSet Ω Ω' hΩ I
  have hsP : spaceTimeHomeoP.symm ⁻¹' (Ω ×ˢ I) = CKN.spaceTimeSet Ω' I := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := locallyIntegrableOn_transport _ w h1
    rw [hsP] at this
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.locallyIntegrableOn_comp this
  · have := locallyIntegrableOn_transport _ Dw h2
    rwa [hsP] at this
  · have := locallyIntegrableOn_transport _ D2w h3
    rwa [hsP] at this
  · have := locallyIntegrableOn_transport _ Dtw h4
    rw [hsP] at this
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.locallyIntegrableOn_comp this
  · intro φ hφ
    obtain ⟨a, b, c⟩ := h5 _ (testFunction_comp Ω Ω' hΩ I φ hφ)
    exact ⟨fun i j => spatial_pairing Ω Ω' hΩ I (fun z => (w z).ofLp i) (fun z => Dw z i j) φ j
        (a i j),
      fun i j k => spatial_pairing Ω Ω' hΩ I (fun z => Dw z i j) (fun z => D2w z i j k) φ k
        (b i j k),
      fun i => time_pairing Ω Ω' hΩ I (fun z => (w z).ofLp i) (fun z => (Dtw z).ofLp i) φ (c i)⟩

/-- The library-side vector field attached to a Challenge vector field. -/
def toLib (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)) :
    CKN.Foundation.Parabolic.ParabolicPoint → CKN.Foundation.Parabolic.Vec3 :=
  fun p => (w (spaceTimeHomeo.symm p)).ofLp

theorem mem_vec3Ball_iff (R : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    x.ofLp ∈ CKN.Foundation.Parabolic.vec3Ball 0 R ↔ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := by
  rw [CKN.Foundation.Parabolic.mem_vec3Ball, sub_zero, vec3EuclideanNorm_ofLp, mem_ball_zero_iff]

theorem continuousOn_transport (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (J : Set ℝ)
    (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (h : ContinuousOn w (Ω ×ˢ J)) :
    ContinuousOn (toLib w) (Ω' ×ˢ J : Set CKN.Foundation.Parabolic.ParabolicPoint) := by
  have hc : ContinuousOn (w ∘ spaceTimeHomeoP.symm) (Ω' ×ˢ J : Set CKN.Foundation.Parabolic.ParabolicPoint) :=
    h.comp spaceTimeHomeoP.symm.continuous.continuousOn fun p hp => ⟨(hΩ _).1 hp.1, hp.2⟩
  exact (EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp_continuousOn hc

theorem lintegral_le_transport (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (Fl : CKN.Foundation.Parabolic.ParabolicPoint → ℝ≥0∞)
    (F : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ≥0∞) (h : ∀ z, Fl (spaceTimeHomeo z) ≤ F z) :
    ∫⁻ p in CKN.spaceTimeSet Ω' I, Fl p ≤ ∫⁻ z in Ω ×ˢ I, F z := by
  rw [lintegral_transport, preimage_spaceTimeSet Ω Ω' hΩ I]
  exact lintegral_mono h

theorem integral_eq_transport (Ω : Set (EuclideanSpace ℝ (Fin 3))) (Ω' : Set (Fin 3 → ℝ))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin 3), x.ofLp ∈ Ω' ↔ x ∈ Ω) (I : Set ℝ)
    (F : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) (Fl : CKN.Foundation.Parabolic.ParabolicPoint → ℝ)
    (h : ∀ z, F z = Fl (spaceTimeHomeo z)) :
    ∫ z in Ω ×ˢ I, F z = ∫ p in CKN.spaceTimeSet Ω' I, Fl p := by
  rw [integral_transport, preimage_spaceTimeSet Ω Ω' hΩ I]
  exact integral_congr_ae (Filter.Eventually.of_forall h)

theorem isBounded_preimage (S : Set CKN.Foundation.Parabolic.ParabolicPoint)
    (h : Bornology.IsBounded S) : Bornology.IsBounded (spaceTimeHomeo ⁻¹' S) := by
  rw [Metric.isBounded_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨max C (C ^ 2), fun x hx y hy => ?_⟩
  have h1 : CKN.Foundation.Parabolic.parabolicDist (spaceTimeHomeo x) (spaceTimeHomeo y) ≤ C :=
    le_of_eq_of_le (CKN.Foundation.Parabolic.dist_eq_parabolicDist _ _).symm (hC hx hy)
  have h2 : CKN.Foundation.Parabolic.vec3EuclideanNorm
      ((spaceTimeHomeo x).1 - (spaceTimeHomeo y).1) ≤ C :=
    (le_max_left _ _).trans h1
  have h3 : Real.sqrt |(spaceTimeHomeo x).2 - (spaceTimeHomeo y).2| ≤ C :=
    (le_max_right _ _).trans h1
  rw [Prod.dist_eq]
  refine max_le ((le_of_eq ?_).trans (h2.trans (le_max_left _ _))) ?_
  · rw [dist_eq_norm, ← vec3EuclideanNorm_ofLp]
    rfl
  · rw [Real.dist_eq]
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
    rw [Real.sq_sqrt (abs_nonneg _)] at h4
    exact h4.trans (le_max_right _ _)

theorem spatialPartial_toLib (g : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) (j : Fin 3)
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.spatialPartial (fun p : CKN.Foundation.Parabolic.ParabolicPoint =>
      g (spaceTimeHomeo.symm p)) j (spaceTimeHomeo z) = spatialDeriv g j z := by
  have h := spatialDeriv_comp (fun p : (Fin 3 → ℝ) × ℝ => g (spaceTimeHomeo.symm p)) j z
  have e : ((fun p : (Fin 3 → ℝ) × ℝ => g (spaceTimeHomeo.symm p)) ∘ spaceTimeHomeo) = g := by
    funext y
    simp
  rw [e] at h
  exact h.symm

theorem timePartial_toLib (g : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.timePartial (fun p : CKN.Foundation.Parabolic.ParabolicPoint =>
      g (spaceTimeHomeo.symm p)) (spaceTimeHomeo z) = timeDeriv g z := by
  have h := timeDeriv_comp (fun p : (Fin 3 → ℝ) × ℝ => g (spaceTimeHomeo.symm p)) z
  have e : ((fun p : (Fin 3 → ℝ) × ℝ => g (spaceTimeHomeo.symm p)) ∘ spaceTimeHomeo) = g := by
    funext y
    simp
  rw [e] at h
  exact h.symm

theorem spatialSecondPartial_toLib (g : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) (j k : Fin 3)
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.spatialSecondPartial (fun p : CKN.Foundation.Parabolic.ParabolicPoint =>
      g (spaceTimeHomeo.symm p)) j k (spaceTimeHomeo z) = spatialSecondDeriv g j k z := by
  unfold CKN.spatialSecondPartial spatialSecondDeriv
  have e : (fun v : CKN.Foundation.Parabolic.ParabolicPoint => CKN.spatialPartial
      (fun p : CKN.Foundation.Parabolic.ParabolicPoint => g (spaceTimeHomeo.symm p)) j v) =
      fun v => spatialDeriv g j (spaceTimeHomeo.symm v) := by
    funext v
    have := spatialPartial_toLib g j (spaceTimeHomeo.symm v)
    have h2 : (spaceTimeHomeo (spaceTimeHomeo.symm v) : CKN.Foundation.Parabolic.ParabolicPoint) = v :=
      spaceTimeHomeo.apply_symm_apply v
    rw [h2] at this
    exact this
  rw [e]
  exact spatialPartial_toLib (fun y => spatialDeriv g j y) k z

theorem norm_toLib (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w (spaceTimeHomeo z)) = ‖w z‖ := by
  unfold toLib
  rw [Homeomorph.symm_apply_apply, vec3EuclideanNorm_ofLp]

theorem gradSq_toLib (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.spatialGradientSq (toLib w) (CKN.spatialGradient (toLib w)) (spaceTimeHomeo z) =
      ∑ i, ∑ j, spatialDeriv (fun y => w y i) j z ^ 2 := by
  unfold CKN.spatialGradientSq CKN.spatialGradient
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : CKN.spatialPartial (fun y => toLib w y i) j (spaceTimeHomeo z) =
      spatialDeriv (fun y => w y i) j z := spatialPartial_toLib (fun y => w y i) j z
  rw [h1]

theorem heat_toLib (w : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3) × ℝ) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (fun i => CKN.timePartial
        (fun y => toLib w y i) (spaceTimeHomeo z) + ∑ j, CKN.spatialSecondPartial
        (fun y => toLib w y i) j j (spaceTimeHomeo z)) ^ 2 =
      ∑ i, (timeDeriv (fun y => w y i) z +
        ∑ j, spatialSecondDeriv (fun y => w y i) j j z) ^ 2 := by
  rw [CKN.Foundation.Parabolic.vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : CKN.timePartial (fun y => toLib w y i) (spaceTimeHomeo z) =
      timeDeriv (fun y => w y i) z := timePartial_toLib (fun y => w y i) z
  have h2 : ∀ j, CKN.spatialSecondPartial (fun y => toLib w y i) j j (spaceTimeHomeo z) =
      spatialSecondDeriv (fun y => w y i) j j z :=
    fun j => spatialSecondPartial_toLib (fun y => w y i) j j z
  rw [h1]
  simp only [h2]

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
  by
    have hΩ := mem_vec3Ball_iff R
    have hmem : ∀ p ∈ CKN.spaceTimeSet (CKN.Foundation.Parabolic.vec3Ball 0 R) (Ioo 0 T),
        spaceTimeHomeo.symm p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R ×ˢ Ioo 0 T :=
      fun p hp => (symm_preimage_spaceTimeSet _ _ hΩ (Ioo 0 T)).ge hp
    have hS := preimage_spaceTimeSet _ _ hΩ (Ioo 0 T)
    have hL2' : (∫⁻ z in CKN.spaceTimeSet (CKN.Foundation.Parabolic.vec3Ball 0 R) (Ioo 0 T),
        ‖toLib w z‖ₑ ^ (2 : ℝ) + ‖(fun p => Dw (spaceTimeHomeo.symm p)) z‖ₑ ^ (2 : ℝ) +
          ‖(fun p => D2w (spaceTimeHomeo.symm p)) z‖ₑ ^ (2 : ℝ) +
          ‖toLib Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_le_transport _ _ hΩ _ _ _ fun z => ?_) hL2
      simp only [toLib, Homeomorph.symm_apply_apply]
      gcongr <;> exact enorm_ofLp_le _
    have hineq' : ∀ᵐ z ∂(volume.restrict (CKN.spaceTimeSet
        (CKN.Foundation.Parabolic.vec3Ball 0 R) (Ioo 0 T))),
        CKN.Foundation.Parabolic.vec3EuclideanNorm (fun i => toLib Dtw z i +
          ∑ j, (fun p => D2w (spaceTimeHomeo.symm p)) z i j j) ≤
        c₁ * (CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w z) +
          Real.sqrt (CKN.spatialGradientSq (toLib w) (fun p => Dw (spaceTimeHomeo.symm p)) z)) := by
      refine ae_transport _ _ ?_
      rw [hS]
      filter_upwards [hineq] with z hz
      simp only [toLib, Homeomorph.symm_apply_apply]
      rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_ofLp]
      exact hz
    have hvanish' : ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ CKN.spaceTimeSet
        (CKN.Foundation.Parabolic.vec3Ball 0 R) (Ioo 0 T),
        CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w z) ≤
          C * (CKN.Foundation.Parabolic.vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k := by
      intro k
      obtain ⟨C, hC⟩ := hvanish k
      refine ⟨C, fun p hp => ?_⟩
      have h := hC _ (hmem p hp)
      have e1 : CKN.Foundation.Parabolic.vec3EuclideanNorm p.1 = ‖(spaceTimeHomeo.symm p).1‖ := by
        rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
        rfl
      have e2 : CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w p) = ‖w (spaceTimeHomeo.symm p)‖ :=
        vec3EuclideanNorm_ofLp _
      rw [e1, e2]
      exact h
    have h0 := ESS.uniqueContinuation R T c₁ hR hT hc₁ (toLib w) (fun p => Dw (spaceTimeHomeo.symm p))
      (fun p => D2w (spaceTimeHomeo.symm p)) (toLib Dtw) (continuousOn_transport _ _ hΩ _ w hcont)
      (hasSpaceTimeWeakDerivs_transport _ _ hΩ _ w Dw D2w Dtw hderiv) hL2' hineq' hvanish'
    intro x hx
    have h1 := h0 x.ofLp ((hΩ x).2 hx)
    have h2 : toLib w (x.ofLp, 0) = (w (x, 0)).ofLp := rfl
    rw [h2] at h1
    ext i
    exact congrFun h1 i

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
  by
    have hΩ : ∀ x : EuclideanSpace ℝ (Fin 3),
        x.ofLp ∈ {x : Fin 3 → ℝ | 0 < x 2} ↔ x ∈ {x : EuclideanSpace ℝ (Fin 3) | 0 < x 2} :=
      fun x => Iff.rfl
    have hmem : ∀ p ∈ CKN.spaceTimeSet {x : Fin 3 → ℝ | 0 < x 2} (Ioo 0 1),
        spaceTimeHomeo.symm p ∈ {x : EuclideanSpace ℝ (Fin 3) | 0 < x 2} ×ˢ Ioo 0 1 :=
      fun p hp => (symm_preimage_spaceTimeSet _ _ hΩ (Ioo 0 1)).ge hp
    have hS := preimage_spaceTimeSet _ _ hΩ (Ioo 0 1)
    have hinit' : ∀ x : CKN.Foundation.Parabolic.Vec3, 0 < x 2 → toLib w (x, 0) = 0 := by
      intro x hx
      have h := hinit (WithLp.toLp 2 x) hx
      have h2 : toLib w (x, 0) = (w (WithLp.toLp 2 x, 0)).ofLp := rfl
      rw [h2, h]
      rfl
    have hL2' : ∀ S : Set CKN.Foundation.Parabolic.ParabolicPoint,
        S ⊆ CKN.spaceTimeSet {x : Fin 3 → ℝ | 0 < x 2} (Ioo 0 1) → Bornology.IsBounded S →
        (∫⁻ z in S, ‖(fun p => Dw (spaceTimeHomeo.symm p)) z‖ₑ ^ (2 : ℝ) +
          ‖(fun p => D2w (spaceTimeHomeo.symm p)) z‖ₑ ^ (2 : ℝ) + ‖toLib Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      intro S hSsub hSb
      have hsub : spaceTimeHomeo ⁻¹' S ⊆ {x : EuclideanSpace ℝ (Fin 3) | 0 < x 2} ×ˢ Ioo 0 1 := by
        intro z hz
        rw [← hS]
        exact hSsub hz
      refine lt_of_le_of_lt ?_ (hL2 _ hsub (isBounded_preimage S hSb))
      rw [lintegral_transport]
      refine lintegral_mono fun z => ?_
      simp only [toLib, Homeomorph.symm_apply_apply]
      gcongr
      exact enorm_ofLp_le _
    have hineq' : ∀ᵐ z ∂(volume.restrict (CKN.spaceTimeSet
        {x : Fin 3 → ℝ | 0 < x 2} (Ioo 0 1))),
        CKN.Foundation.Parabolic.vec3EuclideanNorm (fun i => toLib Dtw z i +
          ∑ j, (fun p => D2w (spaceTimeHomeo.symm p)) z i j j) ≤
        c₁ * (Real.sqrt (CKN.spatialGradientSq (toLib w) (fun p => Dw (spaceTimeHomeo.symm p)) z) +
          CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w z)) := by
      refine ae_transport _ _ ?_
      rw [hS]
      filter_upwards [hineq] with z hz
      simp only [toLib, Homeomorph.symm_apply_apply]
      rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_ofLp]
      exact hz
    -- The library theorem takes a positive growth rate; `max M 1` is one.
    have hgrowth' : ∀ z ∈ CKN.spaceTimeSet {x : Fin 3 → ℝ | 0 < x 2} (Ioo 0 1),
        CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w z) ≤
          Real.exp (max M 1 * CKN.Foundation.Parabolic.vec3EuclideanNorm z.1 ^ 2) := by
      intro p hp
      have h := hgrowth _ (hmem p hp)
      have e1 : CKN.Foundation.Parabolic.vec3EuclideanNorm p.1 = ‖(spaceTimeHomeo.symm p).1‖ := by
        rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
        rfl
      have e2 : CKN.Foundation.Parabolic.vec3EuclideanNorm (toLib w p) = ‖w (spaceTimeHomeo.symm p)‖ :=
        vec3EuclideanNorm_ofLp _
      rw [e1, e2]
      exact h.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left M 1) (sq_nonneg _)))
    have h0 := ESS.backwardUniqueness c₁ (max M 1) hc₁
      (lt_of_lt_of_le one_pos (le_max_right M 1)) (toLib w) (fun p => Dw (spaceTimeHomeo.symm p))
      (fun p => D2w (spaceTimeHomeo.symm p)) (toLib Dtw) (continuousOn_transport _ _ hΩ _ w hcont)
      hinit' (hasSpaceTimeWeakDerivs_transport _ _ hΩ _ w Dw D2w Dtw hderiv) hL2' hineq' hgrowth'
    intro z hz
    have h1 := h0 (spaceTimeHomeo z) (by rw [← hS] at hz; exact hz)
    have h2 : toLib w (spaceTimeHomeo z) = (w z).ofLp := by
      unfold toLib
      rw [Homeomorph.symm_apply_apply]
    rw [h2] at h1
    ext i
    exact congrFun h1 i

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
  by
    obtain ⟨c₀, hc₀, h⟩ := ESS.carlemanGaussian
    refine ⟨c₀, hc₀, fun a ha w hw => ?_⟩
    have hΩ : ∀ x : EuclideanSpace ℝ (Fin 3),
        x.ofLp ∈ (Set.univ : Set (Fin 3 → ℝ)) ↔ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
      fun x => by simp
    have e1 : ∀ z : EuclideanSpace ℝ (Fin 3) × ℝ,
        CKN.Foundation.Parabolic.vec3EuclideanNorm (spaceTimeHomeo z).1 = ‖z.1‖ :=
      fun z => vec3EuclideanNorm_ofLp z.1
    have h1 := h a ha (toLib w) (testFunction_symm_comp _ _ hΩ _ w hw)
    refine (integral_eq_transport _ _ hΩ _ _ _ fun z => ?_).trans_le (h1.trans_eq ?_)
    · rw [norm_toLib, gradSq_toLib]
      show _ = (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
        Real.exp (-(CKN.Foundation.Parabolic.vec3EuclideanNorm (spaceTimeHomeo z).1 ^ 2) / (4 * z.2)) * _
      rw [e1]
      rfl
    · congr 1
      refine (integral_eq_transport _ _ hΩ _ _ _ fun z => ?_).symm
      show _ = (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
        Real.exp (-(CKN.Foundation.Parabolic.vec3EuclideanNorm (spaceTimeHomeo z).1 ^ 2) / (4 * z.2)) * _
      rw [heat_toLib, e1]

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
  by
    intro α hα1 hα2
    obtain ⟨a₀, c, ha₀, hc, h⟩ := ESS.carlemanHalfSpace α hα1 hα2
    refine ⟨a₀, c, ha₀, hc, fun a ha w hw => ?_⟩
    have hΩ : ∀ x : EuclideanSpace ℝ (Fin 3),
        x.ofLp ∈ {x : Fin 3 → ℝ | 1 < x 2} ↔ x ∈ {x : EuclideanSpace ℝ (Fin 3) | 1 < x 2} :=
      fun x => Iff.rfl
    have h1 := h a ha (toLib w) (testFunction_symm_comp _ _ hΩ _ w hw)
    refine (integral_eq_transport _ _ hΩ _ _ _ fun z => ?_).trans_le (h1.trans_eq ?_)
    · rw [norm_toLib, gradSq_toLib]
      rfl
    · congr 1
      refine (integral_eq_transport _ _ hΩ _ _ _ fun z => ?_).symm
      rw [heat_toLib]
      rfl

end ESSChallenge
