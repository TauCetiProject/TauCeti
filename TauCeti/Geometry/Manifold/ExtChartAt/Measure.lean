/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.ModelWithCorners.Measure

/-!
# Measure pushforwards, pullbacks, and chart change of variables for extended charts

This file provides measure-theoretic pushforward, pullback, chart-localized measure construction,
and coordinate change-of-variables lemmas for arbitrary extended charts `e.extend I` and charts of
the `C¹` maximal atlas.

## Main definitions

* `OpenPartialHomeomorph.localChartMeasure`: pull a weighted measure on the model space back along
  an extended chart `e.extend I` to a measure supported on `e.source`.

## Main results

* `OpenPartialHomeomorph.map_restrict_extend_apply`: evaluation of `(μ.restrict e.source).map
  (e.extend I)` on a measurable set.
* `OpenPartialHomeomorph.comap_restrict_eq_comap_map_restrict`: pulling `μ.restrict e.source` back
  to `e.source` agrees with pulling `(μ.restrict e.source).map (e.extend I)` back along
  `e.source.domRestrict (e.extend I)`.
* `OpenPartialHomeomorph.setLIntegral_eq_of_map_restrict_eq`: converting a chart pushforward
  `withDensity` identity into a coordinate Lebesgue integral over measurable subsets of `e.source`.
* `OpenPartialHomeomorph.localChartMeasure_apply` and
  `OpenPartialHomeomorph.map_restrict_localChartMeasure_apply`: evaluation and chart-overlap
  pushforward formula for `OpenPartialHomeomorph.localChartMeasure`.
* `MeasureTheory.Measure.setLIntegral_extendCoordChange`: change of variables between two charts
  of the `C¹` maximal atlas for a weighted Haar integral.
* `TauCeti.eqOn_abs_det_mul_of_map_restrict_eq`: Jacobian transformation law for two continuous
  nonnegative chart weights presenting the same measure on their chart overlap.
-/

public section

open MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace OpenPartialHomeomorph

section ExtendMeasure

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- Evaluation of the pushforward of a measure restricted to a chart source along the
extended chart `e.extend I`. -/
theorem map_restrict_extend_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {A : Set E} (hA : MeasurableSet A) :
    ((μ.restrict e.source).map (e.extend I)) A = μ (e.extend I ⁻¹' A ∩ e.source) := by
  have hcont : Continuous (e.source.domRestrict (e.extend I)) := by
    rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
    exact e.continuousOn_extend
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_restrict_of_measurable_subtype e.open_source.measurableSet
        hcont.measurable) hA,
    Measure.restrict_apply' e.open_source.measurableSet]

/-- Pulling `μ.restrict e.source` back to `e.source` agrees with pulling the chart pushforward
`(μ.restrict e.source).map (e.extend I)` back along `e.source.domRestrict (e.extend I)`. -/
theorem comap_restrict_eq_comap_map_restrict [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) :
    (μ.restrict e.source).comap (Subtype.val : e.source → M) =
      ((μ.restrict e.source).map (e.extend I)).comap (e.source.domRestrict (e.extend I)) := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  ext B hB
  have hBs : MeasurableSet (Subtype.val '' B : Set M) := hval.measurableSet_image' hB
  have hBim : MeasurableSet (e.source.domRestrict (e.extend I) '' B) := hR.measurableSet_image' hB
  rw [hval.comap_apply, hR.comap_apply, e.map_restrict_extend_apply I μ hBim,
    Measure.restrict_apply hBs, inter_eq_left.2 (Subtype.coe_image_subset e.source B)]
  congr 1
  ext x
  refine ⟨fun ⟨z, hzB, hzx⟩ ↦ ?_, fun ⟨⟨z, hzB, hzx⟩, hxe⟩ ↦ ?_⟩
  · subst hzx
    exact ⟨⟨z, hzB, rfl⟩, z.property⟩
  · have hzs : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
    have hxs : x ∈ (e.extend I).source := by rwa [e.extend_source]
    exact ⟨z, hzB, (e.extend I).injOn hzs hxs hzx⟩

/-- Converting a chart pushforward `withDensity` identity into a coordinate Lebesgue integral over
measurable subsets of the chart source, without measurability of the integrand. -/
theorem setLIntegral_eq_of_map_restrict_eq [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {μ : Measure M} {ν : Measure E} {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s, ENNReal.ofReal (w y) * f ((e.extend I).symm y) ∂ν := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hT := e.measurableSet_extend_target I
  have hA := e.measurableSet_image_extend I hs hsub
  have hAT : e.extend I '' s ⊆ (e.extend I).target := (image_mono hsub).trans
    (by rw [← e.extend_source (I := I)]; exact (e.extend I).image_source_eq_target.subset)
  have hrestrict : μ.restrict s =
      ((((ν.restrict (e.extend I).target).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap
        (e.source.domRestrict (e.extend I))).restrict (Subtype.val ⁻¹' s)).map Subtype.val := by
    rw [← hmap, ← e.comap_restrict_eq_comap_map_restrict I μ, ← hval.restrict_map, hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict e.open_source.measurableSet, inter_self,
      Measure.restrict_restrict hs, inter_eq_left.2 hsub]
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) = e.extend I '' s := by
    rw [image_domRestrict, inter_eq_left.2 hsub]
  have hcongr (ρ : Measure e.source) :
      ∫⁻ z, f z ∂ρ =
        ∫⁻ z, (fun y ↦ f ((e.extend I).symm y)) (e.source.domRestrict (e.extend I) z) ∂ρ :=
    lintegral_congr fun z ↦ by
      have hz : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
      simp only [domRestrict_apply, (e.extend I).left_inv hz]
  rw [hrestrict, hval.lintegral_map, hR.restrict_comap, him, hcongr]
  refine (hR.lintegral_map (fun y ↦ f ((e.extend I).symm y))).symm.trans ?_
  have hw_ae : AEMeasurable (fun y ↦ ENNReal.ofReal (w y))
      ((ν.restrict (e.extend I).target).restrict (e.extend I '' s)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hT).mono_measure
      Measure.restrict_le_self
  rw [hR.map_comap, Measure.restrict_restrict hR.measurableSet_range,
    inter_eq_right.2 (him ▸ image_subset_range _ _),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hw_ae _ hA
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  rfl

/-- Pull a measure `ν` on the model space weighted by `ENNReal.ofReal ∘ f ∘ (e.extend I).symm` back
along the extended chart `e.extend I` to a measure supported on `e.source`. -/
def localChartMeasure [MeasurableSpace E] [MeasurableSpace M]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    (ν : Measure E) (f : M → ℝ) : Measure M :=
  (((ν.restrict (e.extend I).target).withDensity
      fun y ↦ ENNReal.ofReal (f ((e.extend I).symm y))).comap
    (e.source.domRestrict (e.extend I))).map Subtype.val

/-- Evaluating `e.localChartMeasure I ν f` on a measurable set pulls the integral back to
`e.extend I '' (s ∩ e.source)`. -/
theorem localChartMeasure_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (f : M → ℝ) {s : Set M} (hs : MeasurableSet s) :
    e.localChartMeasure I ν f s =
      ∫⁻ z in e.extend I '' (s ∩ e.source),
        ENNReal.ofReal (f ((e.extend I).symm z)) ∂ν := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) =
      e.extend I '' (s ∩ e.source) := image_domRestrict _ _ _
  have hB : MeasurableSet (e.extend I '' (s ∩ e.source)) :=
    e.measurableSet_image_extend I (hs.inter e.open_source.measurableSet) inter_subset_right
  have hBT : e.extend I '' (s ∩ e.source) ⊆ (e.extend I).target :=
    (image_mono (by simpa only [e.extend_source] using inter_subset_right)).trans
      (e.extend I).image_source_eq_target.subset
  rw [localChartMeasure, hval.map_apply, hR.comap_apply, him, withDensity_apply _ hB,
    Measure.restrict_restrict hB, inter_eq_left.2 hBT]

end ExtendMeasure

end OpenPartialHomeomorph

section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Change of variables between two charts of the maximal atlas for a weighted Haar integral. -/
theorem setLIntegral_extendCoordChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source)
    (g : E → ℝ≥0∞) :
    ∫⁻ z in I.extendCoordChange e e' '' A, g z ∂ν =
      ∫⁻ y in A,
        ENNReal.ofReal |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          g (I.extendCoordChange e e' y) ∂ν := by
  have hArange : A ⊆ range I :=
    hAsub.trans (by rw [I.extendCoordChange_source]; exact image_subset_range _ _)
  have hderiv : ∀ y ∈ A,
      HasFDerivWithinAt (I.extendCoordChange e e')
        (fderivWithin ℝ (I.extendCoordChange e e') (range I) y) A y := fun y hy ↦
    ((I.contDiffWithinAt_extendCoordChange he he' (hAsub hy)).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt.mono hArange
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hA hderiv
    ((I.extendCoordChange e e').injOn.mono hAsub) g

end MeasureTheory.Measure

end

open Classical in
/-- Pushing `e₁.localChartMeasure I ν f` restricted to `e₀.source` forward along `e₀.extend I`
yields a weighted Haar integral with density `|det D(e₁ ∘ e₀⁻¹)| * f ∘ (e₀.extend I).symm`
supported on the chart overlap. -/
theorem OpenPartialHomeomorph.map_restrict_localChartMeasure_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
    (e₀ e₁ : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I 1 M) (he₁ : e₁ ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] (f : M → ℝ) {A : Set E} (hA : MeasurableSet A) :
    (((e₁.localChartMeasure I ν f).restrict e₀.source).map (e₀.extend I)) A =
      ∫⁻ y in A ∩ (e₀.extend I).target,
        ENNReal.ofReal
          (if y ∈ (I.extendCoordChange e₀ e₁).source then
            |(fderivWithin ℝ (I.extendCoordChange e₀ e₁) (range I) y).det| *
              f ((e₀.extend I).symm y)
          else 0) ∂ν := by
  set Φ := I.extendCoordChange e₀ e₁
  have hΦ_meas := e₀.measurableSet_extendCoordChange_source e₁ I
  have hT₀ : MeasurableSet (e₀.extend I).target := e₀.measurableSet_extend_target I
  have hs_meas : MeasurableSet (e₀.extend I ⁻¹' A ∩ e₀.source) :=
    e₀.measurableSet_preimage_extend_inter I hA
  rw [e₀.map_restrict_extend_apply I _ hA, e₁.localChartMeasure_apply I ν f hs_meas,
    e₀.image_extend_preimage_inter e₁ I A,
    ν.setLIntegral_extendCoordChange (I := I) he₀ he₁ (hA.inter hΦ_meas) inter_subset_right,
    ← lintegral_indicator (hA.inter hΦ_meas), ← lintegral_indicator (hA.inter hT₀)]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ A ∩ Φ.source
  · have hyT : y ∈ A ∩ (e₀.extend I).target := ⟨hy.1, hy.2.1⟩
    rw [indicator_of_mem hy, indicator_of_mem hyT, ite_eq_left hy.2,
      ENNReal.ofReal_mul (abs_nonneg _)]
    have hxi : (e₀.extend I).symm y ∈ (e₁.extend I).source := hy.2.2
    simp only [Φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
    congr 3
    exact (e₁.extend I).left_inv hxi
  · rw [indicator_of_notMem hy]
    by_cases hy' : y ∈ A ∩ (e₀.extend I).target
    · rw [indicator_of_mem hy', ite_eq_right fun h ↦ hy ⟨hy'.1, h⟩, ENNReal.ofReal_zero]
    · rw [indicator_of_notMem hy']

namespace TauCeti

section OverlapJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]

/-- Helper transferring a measurable subset `B ⊆ (I.extendCoordChange e e').source` back to `M`
and comparing the pushforward integrals in charts `e` and `e'`. -/
private theorem setLIntegral_overlap_eq {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y))
    {B : Set E} (hB : MeasurableSet B) (hBsub : B ⊆ (I.extendCoordChange e e').source) :
    ∫⁻ y in B, ENNReal.ofReal (w y) ∂ν =
      ∫⁻ y in B,
        ENNReal.ofReal (|(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          w' (I.extendCoordChange e e' y)) ∂ν := by
  set Φ := I.extendCoordChange e e'
  set s := e.extend I ⁻¹' B ∩ e.source
  have hs_meas : MeasurableSet s := e.measurableSet_preimage_extend_inter I hB
  have hse' : s ⊆ e'.source := by
    rintro x ⟨hxB, hxe⟩
    have hxe' : x ∈ (e.extend I).source := by rwa [e.extend_source]
    have h2 : (e.extend I).symm (e.extend I x) ∈ (e'.extend I).source := (hBsub hxB).2
    rwa [(e.extend I).left_inv hxe', e'.extend_source] at h2
  have him_e : e.extend I '' s = B := by
    ext y
    refine ⟨fun ⟨_, ⟨hxB, _⟩, hxy⟩ ↦ hxy ▸ hxB, fun hyB ↦ ?_⟩
    have hyT : y ∈ (e.extend I).target := (hBsub hyB).1
    refine ⟨(e.extend I).symm y,
      ⟨by rw [mem_preimage, (e.extend I).right_inv hyT]; exact hyB, ?_⟩,
      (e.extend I).right_inv hyT⟩
    simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hyT
  have him_e' : e'.extend I '' s = Φ '' B := by
    rw [← him_e, image_image]
    refine image_congr fun x hx ↦ ?_
    have hxe_s : x ∈ (e.extend I).source := by rw [e.extend_source]; exact hx.2
    simp only [Φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e.extend I).left_inv hxe_s]
  have h1 := e.setLIntegral_eq_of_map_restrict_eq I hw hmap hs_meas inter_subset_right
    (fun _ ↦ 1)
  have h2 := e'.setLIntegral_eq_of_map_restrict_eq I hw' hmap' hs_meas hse' (fun _ ↦ 1)
  simp only [mul_one, setLIntegral_one] at h1 h2
  conv_lhs => rw [← him_e]
  rw [← h1, h2, him_e', ν.setLIntegral_extendCoordChange (I := I) he he' hB hBsub]
  exact setLIntegral_congr_fun hB fun y _ ↦ (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- Shared Jacobian transformation identity for two continuous nonnegative chart weights presenting
the same measure on their chart overlap. -/
theorem eqOn_abs_det_mul_of_map_restrict_eq
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y) (hw'0 : ∀ y ∈ (e'.extend I).target, 0 ≤ w' y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y)) :
    EqOn w (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
      w' (I.extendCoordChange e e' y)) (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hΦ_src : Φ.source = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
    rw [I.extendCoordChange_source, I.image_eq]
  have hΦ_meas : MeasurableSet Φ.source := e.measurableSet_extendCoordChange_source e' I
  have hsubT : Φ.source ⊆ (e.extend I).target := fun _ hy ↦ hy.1
  have hmeq :
      (ν.restrict Φ.source).withDensity (fun y ↦ ENNReal.ofReal (w y)) =
        (ν.restrict Φ.source).withDensity fun y ↦
          ENNReal.ofReal (|(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) := by
    ext A hA
    rw [withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA]
    exact setLIntegral_overlap_eq he he' hw hw' hmap hmap' (hA.inter hΦ_meas) inter_subset_right
  have hcont_rhs : ContinuousOn
      (fun y ↦ |(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) Φ.source :=
    (continuousOn_abs_det_fderivWithin_extendCoordChange (I := I) he he').mul
      (hw'.comp (I.contDiffOn_extendCoordChange he he').continuousOn fun _ hy ↦
        (Φ.map_source hy).1)
  rw [hΦ_src] at hmeq hcont_rhs ⊢
  exact I.eqOn_of_withDensity_ofReal_eq (e.symm ≫ₕ e').open_source
    (hw.mono (hΦ_src ▸ hsubT)) hcont_rhs
    (fun y hy ↦ hw0 y (hsubT (hΦ_src.symm ▸ hy)))
    (fun y hy ↦ mul_nonneg (abs_nonneg _) (hw'0 _ (Φ.map_source (hΦ_src.symm ▸ hy)).1)) hmeq

end OverlapJacobian

end TauCeti

end
