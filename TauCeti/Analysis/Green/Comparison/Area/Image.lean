/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Area.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Embedding
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Planar image area of an oriented manifold embedding

The canonical manifold integral of pulled-back weighted planar area equals the Lebesgue
integral over the actual embedding image. The source can have boundary or corners. Orientation
preservation is imposed on the actual manifold derivative, rather than on a stored Jacobian or
an assumed integral identity.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]

/-- A continuous weight and a C1 map from a compact manifold give genuine intrinsic
integrability of the pulled-back weighted planar area, including at corners. -/
theorem _root_.Module.Basis.integrableTopForm_mpullback_areaForm (b : Module.Basis (Fin 2) ℝ E)
    {f : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) 1 f) {g : ℂ → ℝ} (hg : Continuous g) :
    IntegrableTopForm (mpullback I 𝓘(ℝ, ℂ) f (fun z ↦ g z • manifoldAreaForm z)) := by
  have hω : IsSmoothForm 𝓘(ℝ, ℂ) 0 (fun z ↦ g z • manifoldAreaForm z) := by
    apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
    intro x
    have he : RoughForm.inChartAt (I := 𝓘(ℝ, ℂ)) (fun z ↦ g z • manifoldAreaForm z) x =
        fun z ↦ g z • Complex.orientation.volumeFormL := by
      funext z
      rw [RoughForm.inChartAt_fun_smul, manifoldAreaForm_inChartAt]
      simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, id_eq]
    rw [he]
    exact (contDiff_zero.mpr (hg.smul continuous_const)).contDiffWithinAt
  exact (hω.mpullback hf).integrableTopForm
    (_root_.isClosed_tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ)
      (mpullback I 𝓘(ℝ, ℂ) f (fun z ↦ g z • manifoldAreaForm z))).isCompact b

/-- Integration of actual pulled-back planar area along an injective orientation-preserving
manifold map is integration over its image. Intrinsic integrability implies image integrability;
weights may be rough, and boundary and corner points are retained. -/
theorem integralTopForm_mpullback_area_eq_integral_image
    (l : Manifold.OrientationLift I M (Fin 2))
    {f : M → ℂ} (hf : MDifferentiable I 𝓘(ℝ, ℂ) f) (hinj : Function.Injective f)
    (F : M → E ≃L[ℝ] ℂ)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, ℂ) f x))
    -- Read tangent orientations on the fixed model E so composition rewrites use its instances.
    (ho : ∀ x, _root_.Orientation.map (Fin 2) (F x).toLinearEquiv
      (show _root_.Orientation ℝ E (Fin 2) from
        (Manifold.Orientation.mk l).orientationAt x) =
        Complex.orientation)
    (g : ℂ → ℝ)
    (hi : IntegrableTopForm (mpullback I 𝓘(ℝ, ℂ) f (fun z ↦ g z • manifoldAreaForm z))) :
    IntegrableOn g (range f) ∧
    integralTopForm (Manifold.Orientation.mk l)
      (mpullback I 𝓘(ℝ, ℂ) f (fun z ↦ g z • manifoldAreaForm z)) = ∫ z in range f, g z := by
  let e : E ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    (by simpa only [Fintype.card_fin, Complex.finrank_real_complex] using l.card_eq.symm)
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let b := Complex.basisOneI.map e.symm.toLinearEquiv
  let f' : M → E := e.symm ∘ f
  let F' : M → E ≃L[ℝ] E := fun x ↦ (F x).trans e.symm
  let ω : RoughForm 𝓘(ℝ, E) E ℝ 2 :=
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) e (fun z ↦ g z • manifoldAreaForm z)
  have he : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℂ) e :=
    fun _ ↦ e.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have he' : MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, E) e.symm :=
    fun _ ↦ e.symm.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hf' : MDifferentiable I 𝓘(ℝ, E) f' := he'.comp hf
  have hF' : ∀ x, (F' x).toContinuousLinearMap = mfderiv I 𝓘(ℝ, E) f' x := by
    intro x
    rw [mfderiv_comp x (he' (f x)) (hf x), mfderiv_eq_fderiv, e.symm.fderiv]
    -- Expose the underlying continuous linear map of the composed coordinate equivalence F'.
    change e.symm.toContinuousLinearMap.comp (F x).toContinuousLinearMap = _
    rw [hF x]
    convert! rfl using 1
  -- The model-fibre annotation keeps the orientation transport independent of tangent instances.
  have ho' : ∀ x, _root_.Orientation.map (Fin 2) (F' x).toLinearEquiv
      (show _root_.Orientation ℝ E (Fin 2) from
        (Manifold.Orientation.mk l).orientationAt x) =
        b.orientation := by
    intro x
    rw [Module.Basis.orientation_map]
    -- The composed coordinate equivalence acts on the fixed real model orientation.
    change _root_.Orientation.map (Fin 2) ((F x).toLinearEquiv.trans e.symm.toLinearEquiv)
      _ = _
    rw [_root_.Orientation.map_trans, ho x]
    rfl
  have hpull : mpullback I 𝓘(ℝ, E) f' ω =
      mpullback I 𝓘(ℝ, ℂ) f (fun z ↦ g z • manifoldAreaForm z) := by
    rw [← mpullback_comp hf' he]
    have hcomp : (e ∘ f') = f := by funext x; exact e.apply_symm_apply (f x)
    rw [hcomp]
  have hcoef : ∀ y, ω y (fun i ↦ (NormedSpace.fromTangentSpace y).symm (b i)) = g (e y) := by
    intro y
    dsimp only [ω]
    rw [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      manifoldAreaForm_apply, mfderiv_eq_fderiv, e.fderiv]
    have hv : (fun i ↦ NormedSpace.fromTangentSpace (e y)
        (((NormedSpace.fromTangentSpace (e y)).symm.toContinuousLinearMap.comp
          (e.toContinuousLinearMap.comp
            (NormedSpace.fromTangentSpace y).toContinuousLinearMap))
            ((NormedSpace.fromTangentSpace y).symm (b i)))) = Complex.basisOneI := by
      funext i
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      exact e.apply_symm_apply _
    rw [hv, Complex.coe_basisOneI, Orientation.volumeFormL_apply, complexAreaForm_one_I, mul_one]
  have hi' : IntegrableTopForm (mpullback I 𝓘(ℝ, E) f' ω) := hpull.symm ▸ hi
  obtain ⟨hgi, hge⟩ := integralTopForm_mpullback_eq_integral_image l b hf'
    (e.symm.injective.comp hinj) F' hF' ho' ω hi'
  simp_rw [hcoef] at hgi hge
  rw [hpull] at hge
  have hb : b.map e.toLinearEquiv = Complex.basisOneI := by
    ext i
    exact e.apply_symm_apply _
  have hmp : MeasurePreserving e b.addHaar volume := ⟨e.continuous.measurable, by
    rw [b.map_addHaar e, hb, basisOneI_addHaar]⟩
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm : MeasurableSet (range f) := (isCompact_range hf.continuous).measurableSet
  have hr : range f' = e ⁻¹' range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (e.apply_symm_apply (f x)).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, e.injective ((e.apply_symm_apply (f x)).trans hx)⟩
  rw [hr] at hgi hge
  exact ⟨((hmp.restrict_preimage hm).integrable_comp_emb hme).mp hgi,
    hge.trans ((hmp.restrict_preimage hm).integral_comp hme g)⟩

end TauCeti.Green
