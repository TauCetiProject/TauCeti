/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.AE
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable

/-!
# Measure-theoretic properties of positive continuous density measures

Every positive continuous density measure on a finite-dimensional real `C¹` manifold `M` is locally
finite (`TauCeti.IsPositiveContinuousDensity.isLocallyFiniteMeasure`) and positive on nonempty open
sets (`TauCeti.IsPositiveContinuousDensity.isOpenPosMeasure`). On the source of every chart of
the `C¹` maximal atlas, an arbitrary subset (not necessarily measurable) has measure zero iff its
coordinate image has additive Haar measure zero
(`TauCeti.IsPositiveContinuousDensity.measure_eq_zero_iff_measure_extend_image_eq_zero`);
consequently, every measure-zero set is chartwise null, and on a Lindelöf manifold the null sets
coincide with `TauCeti.IsNullSet I` and the almost-everywhere filter equals
`TauCeti.Manifold.ae I M`.

## Main results

* `TauCeti.IsPositiveContinuousDensity.isLocallyFiniteMeasure`: local finiteness.
* `TauCeti.IsPositiveContinuousDensity.isOpenPosMeasure`: positivity on nonempty open sets.
* `TauCeti.IsPositiveContinuousDensity.measure_eq_zero_iff_measure_extend_image_eq_zero`:
  chartwise null-set characterization for arbitrary subsets of maximal-atlas chart sources.
* `TauCeti.IsPositiveContinuousDensity.isNullSet_of_measure_eq_zero`,
  `TauCeti.IsPositiveContinuousDensity.isNullSet_iff_measure_eq_zero`,
  `TauCeti.IsPositiveContinuousDensity.ae_eq_manifoldAE`,
  `TauCeti.IsPositiveContinuousDensity.eventually_ae_iff_manifoldAE`: agreement with chartwise null
  sets and the metric-free filter `TauCeti.Manifold.ae I M`.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

section MeasureProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

/-- Every positive continuous density measure is locally finite. -/
theorem IsPositiveContinuousDensity.isLocallyFiniteMeasure {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x ↦ ?_⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  set e := chartAt H x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
  set w := hμ.chartWeight he ν
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hbound : {y | w y < w (extChartAt I x x) + 1} ∈ 𝓝[range I] (extChartAt I x x) := by
    rw [← nhdsWithin_extChartAt_target_eq' hx]
    exact (hμ.continuousOn_chartWeight he ν _ ((extChartAt I x).map_source hx)).eventually_lt_const
      (lt_add_one _)
  set t := {y | w y < w (extChartAt I x x) + 1} ∩ Metric.ball (extChartAt I x x) 1
  have ht : t ∈ 𝓝[range I] (extChartAt I x x) :=
    Filter.inter_mem hbound (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos))
  have hs : e.source ∩ extChartAt I x ⁻¹' t ∈ 𝓝 x :=
    Filter.inter_mem (chart_source_mem_nhds H x)
      (extChartAt_preimage_mem_nhds_of_mem_nhdsWithin hx ht)
  refine ⟨interior (e.source ∩ extChartAt I x ⁻¹' t), interior_mem_nhds.2 hs, ?_⟩
  rw [hμ.measure_apply_of_subset he ν isOpen_interior.measurableSet
    (interior_subset.trans inter_subset_left)]
  have him : e.extend I '' interior (e.source ∩ extChartAt I x ⁻¹' t) ⊆ t := by
    rintro _ ⟨z, hz, rfl⟩
    exact (interior_subset hz).2
  refine setLIntegral_lt_top_of_le_nnreal ?_
    ⟨(w (extChartAt I x x) + 1).toNNReal, fun y hy ↦ ENNReal.ofReal_le_ofReal (him hy).1.le⟩
  exact ((measure_mono (him.trans inter_subset_right)).trans_lt measure_ball_lt_top).ne

/-- Every positive continuous density measure gives positive mass to every nonempty open set. -/
theorem IsPositiveContinuousDensity.isOpenPosMeasure {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) : Measure.IsOpenPosMeasure μ := by
  refine ⟨fun U hU ⟨x, hxU⟩ ↦ ?_⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  set e := chartAt H x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
  set s := U ∩ e.source
  have hs_open : IsOpen s := hU.inter e.open_source
  have hxs : x ∈ s := ⟨hxU, mem_chart_source H x⟩
  have hxs' : s ⊆ (extChartAt I x).source := by
    simpa only [extChartAt_source] using inter_subset_right
  have hpos_nu : 0 < ν (extChartAt I x '' s) := by
    rw [(extChartAt I x).image_eq_target_inter_inv_preimage hxs']
    refine Measure.measure_pos_of_nonempty_interior _ (Nonempty.of_closure ⟨extChartAt I x x, ?_⟩)
    simpa only [inter_comm] using extChartAt_mem_closure_interior (I := I) (x₀ := x)
      (subset_closure (mem_interior_iff_mem_nhds.2 (hs_open.mem_nhds hxs))) (hxs' hxs)
  have hmeas := e.measurableSet_image_extend I hs_open.measurableSet inter_subset_right
  have hsubT : extChartAt I x '' s ⊆ (extChartAt I x).target :=
    (image_mono hxs').trans (extChartAt I x).image_source_eq_target.subset
  intro hU0
  have hs0 : μ s = 0 := measure_mono_null inter_subset_left hU0
  rw [hμ.measure_apply_of_subset he ν hs_open.measurableSet inter_subset_right] at hs0
  have hae := (lintegral_eq_zero_iff' ((ENNReal.continuous_ofReal.comp_continuousOn
    ((hμ.continuousOn_chartWeight he ν).mono hsubT)).aemeasurable hmeas)).1 hs0
  have hfalse : ∀ᵐ _ ∂ν.restrict (extChartAt I x '' s), False := by
    filter_upwards [ae_restrict_mem hmeas, hae] with y hy hy0
    exact (ENNReal.ofReal_pos.2 (hμ.chartWeight_pos he ν (hsubT hy))).ne' hy0
  exact hpos_nu.ne' (by
    simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] using ae_iff.1 hfalse)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- On the source of a chart of the `C¹` maximal atlas, a measurable subset has `μ`-measure zero
iff its coordinate image has additive Haar measure zero. -/
private theorem measure_eq_zero_iff_measure_extend_image_eq_zero_of_measurableSet {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    μ s = 0 ↔ ν (e.extend I '' s) = 0 := by
  have hmeas := e.measurableSet_image_extend I hs hsub
  have hsubT : e.extend I '' s ⊆ (e.extend I).target :=
    (image_mono (by simpa only [e.extend_source] using hsub)).trans
      (e.extend I).image_source_eq_target.subset
  rw [hμ.measure_apply_of_subset he ν hs hsub]
  constructor
  · intro hz
    have hae := (lintegral_eq_zero_iff' ((ENNReal.continuous_ofReal.comp_continuousOn
      ((hμ.continuousOn_chartWeight he ν).mono hsubT)).aemeasurable hmeas)).1 hz
    have hfalse : ∀ᵐ _ ∂ν.restrict (e.extend I '' s), False := by
      filter_upwards [ae_restrict_mem hmeas, hae] with y hy hy0
      exact (ENNReal.ofReal_pos.2 (hμ.chartWeight_pos he ν (hsubT hy))).ne' hy0
    simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] using ae_iff.1 hfalse
  · intro hz
    rw [Measure.restrict_zero_set hz, lintegral_zero_measure]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- On the source of a chart of the `C¹` maximal atlas, an arbitrary (not necessarily measurable)
subset has `μ`-measure zero iff its coordinate image has additive Haar measure zero. -/
theorem IsPositiveContinuousDensity.measure_eq_zero_iff_measure_extend_image_eq_zero
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hsub : s ⊆ e.source) :
    μ s = 0 ↔ ν (e.extend I '' s) = 0 := by
  constructor
  · intro hz
    set t := toMeasurable μ s ∩ e.source
    have hst : s ⊆ t := fun y hy ↦ ⟨subset_toMeasurable μ s hy, hsub hy⟩
    have htm : MeasurableSet t :=
      (measurableSet_toMeasurable μ s).inter e.open_source.measurableSet
    have ht0 : μ t = 0 := measure_mono_null inter_subset_left (by rwa [measure_toMeasurable])
    exact measure_mono_null (image_mono hst)
      ((measure_eq_zero_iff_measure_extend_image_eq_zero_of_measurableSet
        hμ he ν htm inter_subset_right).1 ht0)
  · intro hz
    set A := toMeasurable ν (e.extend I '' s)
    set t : Set M := e.extend I ⁻¹' A ∩ e.source
    have htm : MeasurableSet t :=
      e.measurableSet_preimage_extend_inter I (measurableSet_toMeasurable _ _)
    have hst : s ⊆ t := fun y hy ↦
      ⟨subset_toMeasurable ν _ (mem_image_of_mem _ hy), hsub hy⟩
    have hAt : e.extend I '' t ⊆ A := by
      rintro _ ⟨z, ⟨hzA, _⟩, rfl⟩
      exact hzA
    refine measure_mono_null hst
      ((measure_eq_zero_iff_measure_extend_image_eq_zero_of_measurableSet
        hμ he ν htm inter_subset_right).2 ?_)
    exact measure_mono_null hAt (by rwa [measure_toMeasurable])

omit [FiniteDimensional ℝ E] in
/-- Every `μ`-null set of a positive continuous density measure is chartwise null. No Lindelöf
assumption on `M` is needed for this direction. -/
theorem IsPositiveContinuousDensity.isNullSet_of_measure_eq_zero
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {s : Set M} (hs : μ s = 0) :
    IsNullSet I s := by
  rw [isNullSet_iff]
  intro x ν _
  rw [extChartAt_source]
  exact (hμ.measure_eq_zero_iff_measure_extend_image_eq_zero
    (IsManifold.chart_mem_maximalAtlas x) ν inter_subset_right).1
    (measure_mono_null inter_subset_left hs)

/-- On a Lindelöf manifold, a subset is chartwise null iff it has measure zero for a positive
continuous density measure. -/
theorem IsPositiveContinuousDensity.isNullSet_iff_measure_eq_zero [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {s : Set M} :
    IsNullSet I s ↔ μ s = 0 := by
  refine ⟨fun hs ↦ ?_, hμ.isNullSet_of_measure_eq_zero⟩
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x : M ↦ (chartAt H x).source)
    fun x ↦ chart_source_mem_nhds H x
  have hsub : s ⊆ ⋃ x ∈ t, s ∩ (chartAt H x).source := fun y hy ↦ by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ y)
    exact mem_iUnion₂.2 ⟨x, hxt, hy, hyx⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  refine measure_mono_null hsub ((measure_biUnion_null_iff ht).2 fun x _ ↦ ?_)
  exact (hμ.measure_eq_zero_iff_measure_extend_image_eq_zero
    (IsManifold.chart_mem_maximalAtlas x) ν inter_subset_right).2
    (by simpa only [extChartAt, OpenPartialHomeomorph.extend_source] using hs.chartwise x ν)

/-- On a Lindelöf manifold, the almost-everywhere filter of any positive continuous density
measure coincides with the metric-free filter `TauCeti.Manifold.ae I M`. -/
theorem IsPositiveContinuousDensity.ae_eq_manifoldAE [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) :
    MeasureTheory.ae μ = Manifold.ae I M := by
  ext s
  rw [MeasureTheory.mem_ae_iff, Manifold.mem_ae_iff, hμ.isNullSet_iff_measure_eq_zero]

/-- A property holds almost everywhere for a positive continuous density measure on a Lindelöf
manifold iff it holds in the metric-free filter `TauCeti.Manifold.ae I M`. -/
theorem IsPositiveContinuousDensity.eventually_ae_iff_manifoldAE [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {p : M → Prop} :
    (∀ᵐ x ∂μ, p x) ↔ ∀ᶠ x in Manifold.ae I M, p x := by
  rw [hμ.ae_eq_manifoldAE]

end MeasureProperties

end TauCeti
