/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Integration along orientation-preserving embeddings

Actual inverse-chart derivatives identify the signed top-form coefficient with the absolute
Jacobian of an orientation-preserving embedding. Finite disjoint chart partitions then compare
manifold integration with Haar integration over the image, including boundary and corner points.

## Formal sources

The integral and integrability comparisons use Mathlib.MeasureTheory.Function.Jacobian,
specifically `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` and
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}

/-- Orientation preservation by the actual derivative implies the signed Jacobian identity
in every preferred chart, including at intrinsic boundary points. -/
theorem Manifold.OrientationLift.sign_mul_det_embedding (l : Manifold.OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) {f : M → E} (hf : MDifferentiable I 𝓘(ℝ, E) f)
    (F : M → E ≃L[ℝ] E)
    (hF : ∀ x, (F x).toContinuousLinearMap = mfderiv I 𝓘(ℝ, E) f x)
    (ho : ∀ x, _root_.Orientation.map (Fin k) (F x).toLinearEquiv
      ((Manifold.Orientation.mk l).orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        b.orientation)
    (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    (_root_.Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α x : ℝ) *
      (fderivWithin ℝ (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)).det =
        |(fderivWithin ℝ (f ∘ (extChartAt I α).symm)
          (range I) (extChartAt I α x)).det| := by
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  have hc := l.compatible α x x hx' (mem_chart_source H x)
  rw [← tangentCoordChange_def] at hc
  have hp := ho x
  rw [Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite] at hp
  -- Orientation transport for the fixed model basis unfolds to the pointwise orientationAt.
  change _root_.Orientation.map (Fin k) ((F x).toLinearEquiv : E ≃ₗ[ℝ] E)
    (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
      else -l.modelOrientation) = b.orientation at hp
  have hd : 0 < (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      (l.sign x ⟨x, mem_chart_source H x⟩ : ℝ) * (F x).toLinearEquiv.toLinearMap.det := by
    rw [← _root_.Orientation.intCast_units_smul_eq_ite] at hp
    exact _root_.Orientation.signBasis_mul_units_mul_det_pos l.modelOrientation b
      (F x).toLinearEquiv _ hp
  rw [(hf x).fderivWithin_comp_extChartAt_symm α hx, ← hF x]
  -- The continuous-linear composition and its underlying linear composition share a determinant.
  change _ * _ * ((F x).toLinearEquiv.toLinearMap.comp
    (tangentCoordChange I α x x).toLinearMap).det =
      |((F x).toLinearEquiv.toLinearMap.comp
        (tangentCoordChange I α x x).toLinearMap).det|
  rw [LinearMap.det_comp]
  rw [l.signAt_of_mem hx']
  have hs : (l.sign x ⟨x, mem_chart_source H x⟩ : ℝ) ^ 2 = 1 := by
    exact_mod_cast Int.isUnit_sq (l.sign x ⟨x, mem_chart_source H x⟩).isUnit
  have hpos := mul_pos hd hc
  have hpos' : 0 < (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      (l.sign α ⟨x, hx'⟩ : ℝ) *
      ((F x).toLinearEquiv.toLinearMap.det * (tangentCoordChange I α x x).det) := by
    nlinarith [hs]
  rcases Int.units_eq_one_or (_root_.Orientation.signBasis l.modelOrientation b) with hb | hb <;>
    rcases Int.units_eq_one_or (l.sign α ⟨x, hx'⟩) with ha | ha
  all_goals simp only [hb, ha, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg,
    one_mul, neg_mul, mul_neg] at hpos' ⊢
  all_goals try rw [_root_.neg_neg ((F x).toLinearEquiv.toLinearMap.det *
    (tangentCoordChange I α x x).det)] at hpos' ⊢
  all_goals first | exact (abs_of_pos hpos').symm | exact (abs_of_neg (neg_pos.mp hpos')).symm


/-- An orientation-preserving actual pullback has the absolute Jacobian as its signed
coefficient in every preferred chart. -/
theorem signedInChartAt_mpullback_eq_abs_det (l : Manifold.OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) {f : M → E} (hf : MDifferentiable I 𝓘(ℝ, E) f)
    (F : M → E ≃L[ℝ] E)
    (hF : ∀ x, (F x).toContinuousLinearMap = mfderiv I 𝓘(ℝ, E) f x)
    (ho : ∀ x, _root_.Orientation.map (Fin k) (F x).toLinearEquiv
      ((Manifold.Orientation.mk l).orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        b.orientation)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) :
    (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
        (mpullback I 𝓘(ℝ, E) f ω).signedInChartAt b α (fun x ↦ l.signAt α x)
          (extChartAt I α x) =
      |(fderivWithin ℝ (f ∘ (extChartAt I α).symm)
        (range I) (extChartAt I α x)).det| *
          ω (f x) (fun i ↦ (NormedSpace.fromTangentSpace (f x)).symm (b i)) := by
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
    RoughForm.inChartAt_mpullback_modelSpace ω f α ((extChartAt I α).map_source hx)
      (by simpa only [(extChartAt I α).left_inv hx] using hf x),
    (extChartAt I α).left_inv hx]
  let D := fderivWithin ℝ (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)
  have he : ((ω (f x)).compContinuousLinearMap
      ((NormedSpace.fromTangentSpace (f x)).symm.toContinuousLinearMap.comp D)) b =
      D.det * ω (f x) (fun i ↦ (NormedSpace.fromTangentSpace (f x)).symm (b i)) := by
    exact ContinuousAlternatingMap.compContinuousLinearMap_apply_basis
      ((ω (f x)).compContinuousLinearMap
        (NormedSpace.fromTangentSpace (f x)).symm.toContinuousLinearMap) b D
  rw [he, ← mul_assoc, ← mul_assoc, l.sign_mul_det_embedding b hf F hF ho α hx]


variable [MeasurableSpace E] [BorelSpace E]

/-- A chartwise Borel piece has the same integral as its actual embedding image. Both
measurability of that image and integrability of its coefficient are consequences. -/
theorem integral_mpullback_chart_piece (l : Manifold.OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) {f : M → E} (hf : MDifferentiable I 𝓘(ℝ, E) f)
    (hinj : Function.Injective f) (F : M → E ≃L[ℝ] E)
    (hF : ∀ x, (F x).toContinuousLinearMap = mfderiv I 𝓘(ℝ, E) f x)
    (ho : ∀ x, _root_.Orientation.map (Fin k) (F x).toLinearEquiv
      ((Manifold.Orientation.mk l).orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        b.orientation)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k) (hi : IntegrableTopForm (mpullback I 𝓘(ℝ, E) f ω))
    (α : M) {s : Set M} (hs : IsChartMeasurable I s)
    (hsub : s ⊆ (extChartAt I α).source) :
    MeasurableSet (f '' s) ∧
    IntegrableOn (fun y ↦ ω y (fun i ↦ (NormedSpace.fromTangentSpace y).symm (b i)))
      (f '' s) b.addHaar ∧
    (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      (∫ z in (extChartAt I α) '' s,
        (mpullback I 𝓘(ℝ, E) f ω).signedInChartAt b α (fun x ↦ l.signAt α x) z ∂b.addHaar) =
      ∫ y in f '' s, ω y (fun i ↦ (NormedSpace.fromTangentSpace y).symm (b i)) ∂b.addHaar := by
  let S := (extChartAt I α) '' s
  let T := f ∘ (extChartAt I α).symm
  let D := fderivWithin ℝ T (range I)
  have hm : MeasurableSet S := hs.image_extChartAt α hsub
  have htarget : S ⊆ (extChartAt I α).target := image_subset_iff.mpr fun x hx ↦
    (extChartAt I α).map_source (hsub hx)
  have hD : ∀ z ∈ S, HasFDerivWithinAt T (D z) S z := by
    intro z hz
    exact ((hf ((extChartAt I α).symm z)).comp_mdifferentiableWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm (htarget hz))).differentiableWithinAt
        |>.hasFDerivWithinAt.mono (htarget.trans (extChartAt_target_subset_range α))
  have hT : InjOn T S := fun z hz w hw he ↦
    (extChartAt I α).symm.injOn (htarget hz) (htarget hw) (hinj he)
  have himage : T '' S = f '' s := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp only [T, Function.comp_apply, (extChartAt I α).left_inv (hsub hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨extChartAt I α x, ⟨x, hx, rfl⟩, by
        simp only [T, Function.comp_apply, (extChartAt I α).left_inv (hsub hx)]⟩
  have hcoef : ∀ z ∈ S,
      (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
        (mpullback I 𝓘(ℝ, E) f ω).signedInChartAt b α (fun x ↦ l.signAt α x) z =
      |(D z).det| • ω (T z) (fun i ↦ (NormedSpace.fromTangentSpace (T z)).symm (b i)) := by
    rintro z ⟨x, hx, rfl⟩
    dsimp only [T, D, Function.comp_apply]
    rw [(extChartAt I α).left_inv (hsub hx)]
    exact signedInChartAt_mpullback_eq_abs_det l b hf F hF ho ω α (hsub hx)
  have hci : Integrable ((mpullback I 𝓘(ℝ, E) f ω).signedInChartAt b α
      (fun x ↦ l.signAt α x)) b.addHaar := by
    apply (RoughForm.integrable_signedInChartAt_iff_unsigned _ b α
      (fun x ↦ l.signAt α x) ?_ b.addHaar).mpr
      (((integrableTopForm_iff _).mp hi).2.2 b α)
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
  refine ⟨?_, ?_, ?_⟩
  · rw [← himage, ← range_domRestrict]
    exact (measurableEmbedding_of_fderivWithin hm hD hT).measurableSet_range
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul b.addHaar hm hD hT]
    exact (hci.const_mul _).integrableOn.congr_fun hcoef hm
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul b.addHaar hm hD hT,
      ← integral_const_mul]
    exact setIntegral_congr_fun hm hcoef

/-- On a compact manifold, integration of an actual orientation-preserving embedding
pullback is Haar integration over the embedding image. No integral identity is assumed. -/
theorem integralTopForm_mpullback_eq_integral_image [CompactSpace M]
    (l : Manifold.OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) {f : M → E} (hf : MDifferentiable I 𝓘(ℝ, E) f)
    (hinj : Function.Injective f) (F : M → E ≃L[ℝ] E)
    (hF : ∀ x, (F x).toContinuousLinearMap = mfderiv I 𝓘(ℝ, E) f x)
    (ho : ∀ x, _root_.Orientation.map (Fin k) (F x).toLinearEquiv
      ((Manifold.Orientation.mk l).orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        b.orientation)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k) (hi : IntegrableTopForm (mpullback I 𝓘(ℝ, E) f ω)) :
    IntegrableOn (fun y ↦ ω y (fun i ↦ (NormedSpace.fromTangentSpace y).symm (b i)))
      (range f) b.addHaar ∧
    integralTopForm (Manifold.Orientation.mk l) (mpullback I 𝓘(ℝ, E) f ω) =
      ∫ y in range f, ω y (fun i ↦ (NormedSpace.fromTangentSpace y).symm (b i)) ∂b.addHaar := by
  obtain ⟨m, α, s, hs, hsub, hdisj, hcover, hform⟩ :=
    exists_chart_partition_integralTopForm l b
  have hp := fun i ↦ integral_mpullback_chart_piece l b hf hinj F hF ho ω hi
    (α i) (hs i) (hsub i)
  have hu : (⋃ i, f '' s i) = range f := by rw [← image_iUnion, hcover, image_univ]
  have hd : Pairwise (fun i j ↦ Disjoint (f '' s i) (f '' s j)) := fun i j hij ↦
    (hdisj hij).image hinj.injOn (subset_univ _) (subset_univ _)
  refine ⟨?_, ?_⟩
  · rw [← hu, integrableOn_finite_iUnion]
    exact fun i ↦ (hp i).2.1
  · rw [hform _ hi, Finset.mul_sum, ← hu,
      integral_iUnion_fintype (fun i ↦ (hp i).1) hd (fun i ↦ (hp i).2.1)]
    exact Finset.sum_congr rfl fun i _ ↦ (hp i).2.2

end TauCeti
