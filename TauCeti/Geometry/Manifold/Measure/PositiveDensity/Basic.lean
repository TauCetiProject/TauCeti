/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.ExtChartAt.Measure
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Det
import TauCeti.Geometry.Manifold.ModelWithCorners.Measure
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Maximal-atlas chart weights, Jacobian transformation, and one-atlas sufficiency

This file extends `TauCeti.IsPositiveDensityMeasure` (defined in
`TauCeti.Geometry.Manifold.Measure.PositiveDensity` in terms of the preferred charts `chartAt`) to
arbitrary charts of the `C¹` maximal atlas:

* Any single covering `C¹` atlas and any single additive Haar measure on the model space suffice
  to test `TauCeti.IsPositiveDensityMeasure` (`TauCeti.isPositiveDensityMeasure_of_atlas`).
* Conversely, on a finite-dimensional real `C¹` manifold, every `IsPositiveDensityMeasure` admits
  a strictly positive continuous coordinate density in every chart `e` of `IsManifold.maximalAtlas`
  relative to every additive Haar measure (`TauCeti.IsPositiveDensityMeasure.chartWeight`,
  `TauCeti.isPositiveDensityMeasure_iff_forall_mem_maximalAtlas`).
* The canonical chart weight `IsPositiveDensityMeasure.chartWeight` (extended by zero outside
  `(e.extend I).target`) is uniquely determined by `μ`, `e`, and `ν`, scales by
  `Measure.addHaarScalarFactor` under a change of additive Haar measure, and transforms by the
  absolute Jacobian determinant under `C¹` coordinate changes
  (`TauCeti.IsPositiveDensityMeasure.chartWeight_changeChart`).

## Main definitions

* `TauCeti.IsPositiveDensityMeasure.chartWeight`: the canonical strictly positive continuous
  coordinate weight of a positive continuous density measure in a chart of the `C¹` maximal atlas,
  extended by zero off `(e.extend I).target`.

## Main results

* `TauCeti.isPositiveDensityMeasure_of_atlas`,
  `TauCeti.IsPositiveDensityMeasure.exists_density_of_mem_maximalAtlas`,
  `TauCeti.isPositiveDensityMeasure_iff_forall_mem_maximalAtlas`: one covering `C¹` atlas and one
  additive Haar measure suffice, and every `IsPositiveDensityMeasure` has densities in every chart
  of the `C¹` maximal atlas.
* `TauCeti.IsPositiveDensityMeasure.chartWeight_eqOn_target_of_map_restrict_eq`,
  `TauCeti.IsPositiveDensityMeasure.chartWeight_eq_of_map_restrict_eq`: uniqueness of the
  continuous chart weight on the extended chart target and as a function on the model space.
* `TauCeti.IsPositiveDensityMeasure.chartWeight_eq_addHaarScalarFactor_mul`: scaling of chart
  weights under a change of additive Haar measure.
* `TauCeti.IsPositiveDensityMeasure.chartWeight_changeChart`,
  `TauCeti.IsPositiveDensityMeasure.chartWeight_changeChart_modelWithCornersSelf`: Jacobian
  transformation rule for chart weights across overlapping charts of the `C¹` maximal atlas.
* `TauCeti.IsPositiveDensityMeasure.measure_eq_zero_iff_measure_extend_image_eq_zero`,
  `TauCeti.IsPositiveDensityMeasure.isNullSet_of_measure_eq_zero`: maximal-atlas chartwise
  null-set characterization and non-Lindelöf nullity of `μ`-null sets.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

/-! ### One-atlas sufficiency and maximal-atlas densities -/

section Atlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M]

/-- Overlap compatibility of chart weights pulled back from an atlas to a chart `e`. -/
private theorem atlasPullbackWeight_eq {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M)
    {w : ι → E → ℝ} (hw_cont : ∀ i, ContinuousOn (w i) ((φ i).extend I).target)
    (hw_pos : ∀ i, ∀ y ∈ ((φ i).extend I).target, 0 < w i y)
    (hw_map : ∀ i, (μ.restrict (φ i).source).map ((φ i).extend I) =
      (ν.restrict ((φ i).extend I).target).withDensity fun y ↦ ENNReal.ofReal (w i y))
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    {i j : ι} {y : E}
    (hyi : y ∈ (I.extendCoordChange e (φ i)).source)
    (hyj : y ∈ (I.extendCoordChange e (φ j)).source) :
    |(fderivWithin ℝ (I.extendCoordChange e (φ i)) (range I) y).det| *
        w i (I.extendCoordChange e (φ i) y) =
      |(fderivWithin ℝ (I.extendCoordChange e (φ j)) (range I) y).det| *
        w j (I.extendCoordChange e (φ j) y) := by
  set x := (e.extend I).symm y
  have hxe : x ∈ e.source := by
    simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hyi.1
  have hxi : x ∈ (φ i).source := (φ i).extend_source (I := I) ▸ hyi.2
  have hxj : x ∈ (φ j).source := (φ j).extend_source (I := I) ▸ hyj.2
  have hzij : (φ i).extend I x ∈ (I.extendCoordChange (φ i) (φ j)).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := φ i) (f' := φ j)]
    exact mem_image_of_mem _ ⟨hxi, hxj⟩
  have htr := I.eqOn_abs_det_mul_of_map_restrict_eq (hφ i) (hφ j)
    (hw_cont i) (hw_cont j) (fun _ hz ↦ (hw_pos i _ hz).le) (fun _ hz ↦ (hw_pos j _ hz).le)
    (hw_map i) (hw_map j) hzij
  dsimp only at htr
  have hchain := I.abs_det_fderivWithin_extendCoordChange_comp he (hφ i) (hφ j) hxe hxi hxj
  have hΦij : I.extendCoordChange (φ i) (φ j) ((φ i).extend I x) = (φ j).extend I x := by
    have hxi' : x ∈ ((φ i).extend I).source := by rwa [(φ i).extend_source]
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      ((φ i).extend I).left_inv hxi']
  have hyx : e.extend I x = y := (e.extend I).right_inv hyi.1
  have hΦi : I.extendCoordChange e (φ i) y = (φ i).extend I x :=
    PartialEquiv.trans_apply (e.extend I).symm ((φ i).extend I)
  have hΦj : I.extendCoordChange e (φ j) y = (φ j).extend I x :=
    PartialEquiv.trans_apply (e.extend I).symm ((φ j).extend I)
  rw [hΦi, hΦj, htr, hΦij, ← hyx, hchain]
  ring

omit [ChartedSpace H M] in
/-- Glue local pushforward identities on a covering of `(e.extend I).target` by chart overlaps. -/
private theorem atlasPullback_map_eq {μ : Measure M} {ν : Measure E}
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H} {e : OpenPartialHomeomorph M H}
    (hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source)
    {w0 : E → ℝ}
    (hpiece : ∀ i, ∀ {A : Set E}, MeasurableSet A → A ⊆ (I.extendCoordChange e (φ i)).source →
      ((μ.restrict e.source).map (e.extend I)) A = ∫⁻ y in A, ENNReal.ofReal (w0 y) ∂ν) :
    (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w0 y) := by
  have hT_meas := e.measurableSet_extend_target I
  obtain ⟨t, ht, htcover'⟩ := I.exists_countable_coordChange_cover e hcov_e
  ext A hA
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hAT_eq : ((μ.restrict e.source).map (e.extend I)) A =
      ((μ.restrict e.source).map (e.extend I)) (A ∩ (e.extend I).target) := by
    rw [e.map_restrict_extend_apply I μ hA, e.map_restrict_extend_apply I μ (hA.inter hT_meas)]
    congr 1; ext x
    refine ⟨fun ⟨hxA, hxe⟩ ↦ ⟨⟨hxA, ?_⟩, hxe⟩, fun ⟨⟨hxA, _⟩, hxe⟩ ↦ ⟨hxA, hxe⟩⟩
    exact (e.extend I).map_source (by rwa [e.extend_source])
  rw [hAT_eq]
  rcases t.eq_empty_or_nonempty with rfl | htne
  · have hTe : (e.extend I).target = ∅ := subset_empty_iff.1 (by simpa using htcover')
    rw [hTe, inter_empty, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  obtain ⟨f, rfl⟩ := ht.exists_eq_range htne
  set U : ℕ → Set E := fun n ↦ (I.extendCoordChange e (φ (f n))).source
  have hU_meas (n : ℕ) : MeasurableSet (U n) := I.measurableSet_extendCoordChange_source e _
  set d : ℕ → Set E := fun n ↦ A ∩ (e.extend I).target ∩ disjointed U n
  have hd_meas (n : ℕ) : MeasurableSet (d n) :=
    (hA.inter hT_meas).inter (MeasurableSet.disjointed hU_meas n)
  have hd_disj : Pairwise (Disjoint on d) :=
    (disjoint_disjointed U).mono fun _ _ hmn ↦ hmn.mono inter_subset_right inter_subset_right
  have hd_union : ⋃ n, d n = A ∩ (e.extend I).target := by
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
    exact inter_subset_right.trans (by simpa only [biUnion_range] using htcover')
  rw [← hd_union, measure_iUnion hd_disj hd_meas, lintegral_iUnion hd_meas hd_disj]
  exact tsum_congr fun n ↦
    hpiece (f n) (hd_meas n) (inter_subset_right.trans (disjointed_subset U n))

/-- Pulling positive continuous chart densities from any covering `C¹` atlas to an arbitrary
chart of the maximal atlas and an arbitrary additive Haar measure. -/
private theorem exists_density_mem_maximalAtlas_of_atlas {μ : Measure M}
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (φ i).source = univ)
    (h : ∀ i, ∃ w : E → ℝ, ContinuousOn w ((φ i).extend I).target ∧
      (∀ y ∈ ((φ i).extend I).target, 0 < w y) ∧
      (μ.restrict (φ i).source).map ((φ i).extend I) =
        (ν.restrict ((φ i).extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν' : Measure E) [ν'.IsAddHaarMeasure] :
    ∃ w : E → ℝ, ContinuousOn w (e.extend I).target ∧
      (∀ y ∈ (e.extend I).target, 0 < w y) ∧
      (μ.restrict e.source).map (e.extend I) =
        (ν'.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) := by
  classical
  choose w hw_cont hw_pos hw_map using h
  have hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source := by
    intro y hy
    have hxe : (e.extend I).symm y ∈ e.source := by
      simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover ▸ mem_univ ((e.extend I).symm y))
    refine ⟨i, ?_⟩
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e) (f' := φ i)]
    exact ⟨(e.extend I).symm y, ⟨hxe, hi⟩, (e.extend I).right_inv hy⟩
  let g (i : ι) (y : E) : ℝ :=
    |(fderivWithin ℝ (I.extendCoordChange e (φ i)) (range I) y).det| *
      w i (I.extendCoordChange e (φ i) y)
  let w0 (y : E) : ℝ := if hy : y ∈ (e.extend I).target then g (hcov_e y hy).choose y else 0
  have hw0_eq (i : ι) : EqOn w0 (g i) (I.extendCoordChange e (φ i)).source := fun y hy ↦ by
    have hyT : y ∈ (e.extend I).target := hy.1
    dsimp only [w0]; rw [dite_eq_left hyT]
    exact atlasPullbackWeight_eq hφ hw_cont hw_pos hw_map he (hcov_e y hyT).choose_spec hy
  have hw0_cont : ContinuousOn w0 (e.extend I).target := fun y hy ↦ by
    obtain ⟨i, hyi⟩ := hcov_e y hy
    have hmem : (I.extendCoordChange e (φ i)).source ∈ 𝓝[(e.extend I).target] y :=
      nhdsWithin_mono y e.extend_target_subset_range (I.extendCoordChange_source_mem_nhdsWithin hyi)
    have hgi : ContinuousOn (g i) (I.extendCoordChange e (φ i)).source :=
      (I.continuousOn_abs_det_fderivWithin_extendCoordChange he (hφ i)).mul
        ((hw_cont i).comp (I.contDiffOn_extendCoordChange he (hφ i)).continuousOn
          fun _ hz ↦ ((I.extendCoordChange e (φ i)).map_source hz).1)
    exact ((hgi y hyi).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ hw0_eq i hz) (hw0_eq i hyi)
  have hw0_pos : ∀ y ∈ (e.extend I).target, 0 < w0 y := fun y hy ↦ by
    obtain ⟨i, hyi⟩ := hcov_e y hy
    rw [hw0_eq i hyi]
    exact mul_pos (I.abs_det_fderivWithin_extendCoordChange_pos he (hφ i) hyi)
      (hw_pos i _ ((I.extendCoordChange e (φ i)).map_source hyi).1)
  have hmap_nu : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w0 y) :=
    atlasPullback_map_eq (I := I) (μ := μ) (ν := ν) hcov_e fun i A hA hAsub ↦ by
      rw [e.map_restrict_extend_apply_of_subset_extendCoordChange_source (φ i) I he (hφ i)
        (hw_cont i) (hw_map i) hA hAsub]
      exact setLIntegral_congr_fun hA fun y hy ↦ by
        rw [hw0_eq i (hAsub hy), ENNReal.ofReal_mul (abs_nonneg _)]
  refine ⟨fun y ↦ (Measure.addHaarScalarFactor ν ν' : ℝ) * w0 y,
    continuousOn_const.mul hw0_cont,
    fun y hy ↦ mul_pos (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν ν') (hw0_pos y hy),
    ?_⟩
  rw [hmap_nu, ← restrict_withDensity',
    Measure.withDensity_eq_withDensity_addHaarScalarFactor_mul ν ν', restrict_withDensity']
  refine congrArg (ν'.restrict (e.extend I).target).withDensity (funext fun y ↦ ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]

/-- **One-atlas sufficiency.** To verify that `μ` is a positive continuous density measure, it
suffices that `μ` has a strictly positive continuous density against a single additive Haar measure
in each chart of some covering `C¹` atlas. Neither the atlas nor the manifold need be countable or
Lindelöf. -/
theorem isPositiveDensityMeasure_of_atlas [IsManifold I 1 M] {μ : Measure M}
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (φ i).source = univ)
    (h : ∀ i, ∃ w : E → ℝ, ContinuousOn w ((φ i).extend I).target ∧
      (∀ y ∈ ((φ i).extend I).target, 0 < w y) ∧
      (μ.restrict (φ i).source).map ((φ i).extend I) =
        (ν.restrict ((φ i).extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    IsPositiveDensityMeasure I μ := by
  refine (isPositiveDensityMeasure_iff_of_isAddHaarMeasure ν).2 fun x ↦ ?_
  simpa only [extChartAt, (chartAt H x).extend_source] using
    exists_density_mem_maximalAtlas_of_atlas ν hφ hcover h (IsManifold.chart_mem_maximalAtlas x) ν

/-- A positive continuous density measure admits a strictly positive continuous coordinate density
in **every** chart of the `C¹` maximal atlas and relative to every additive Haar measure. -/
theorem IsPositiveDensityMeasure.exists_density_of_mem_maximalAtlas [IsManifold I 1 M]
    {μ : Measure M} (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] :
    ∃ w : E → ℝ, ContinuousOn w (e.extend I).target ∧
      (∀ y ∈ (e.extend I).target, 0 < w y) ∧
      (μ.restrict e.source).map (e.extend I) =
        (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) := by
  let ν₀ : Measure E := (Module.finBasis ℝ E).addHaar
  exact exists_density_mem_maximalAtlas_of_atlas ν₀ (φ := fun x : M ↦ chartAt H x)
    (fun x ↦ IsManifold.chart_mem_maximalAtlas x)
    (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, mem_chart_source H x⟩)
    (fun x ↦ by
      simpa only [extChartAt, (chartAt H x).extend_source] using hμ.exists_density x ν₀) he ν

/-- A Borel measure on a finite-dimensional `C¹` manifold is a positive continuous density measure
iff it has strictly positive continuous densities in every chart of the `C¹` maximal atlas. -/
theorem isPositiveDensityMeasure_iff_forall_mem_maximalAtlas [IsManifold I 1 M] {μ : Measure M} :
    IsPositiveDensityMeasure I μ ↔
      ∀ e ∈ IsManifold.maximalAtlas I 1 M, ∀ (ν : Measure E) [ν.IsAddHaarMeasure],
        ∃ w : E → ℝ, ContinuousOn w (e.extend I).target ∧
          (∀ y ∈ (e.extend I).target, 0 < w y) ∧
          (μ.restrict e.source).map (e.extend I) =
            (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) :=
  ⟨fun hμ _ he ν _ ↦ hμ.exists_density_of_mem_maximalAtlas he ν, fun h ↦
    (isPositiveDensityMeasure_iff_of_isAddHaarMeasure (Module.finBasis ℝ E).addHaar).2 fun x ↦ by
      simpa only [extChartAt, (chartAt H x).extend_source] using
        h (chartAt H x) (IsManifold.chart_mem_maximalAtlas x) ((Module.finBasis ℝ E).addHaar)⟩

end Atlas

/-! ### Canonical chart weights and Jacobian transformation rule -/

section ChartWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

/-- The coordinate density of a positive continuous density measure `μ` in a chart `e` of the `C¹`
maximal atlas, relative to an additive Haar measure `ν` on the model space, extended by zero
outside `(e.extend I).target`. It is uniquely determined by `μ`, `e`, and `ν`; see
`IsPositiveDensityMeasure.chartWeight_eq_of_map_restrict_eq`. -/
def IsPositiveDensityMeasure.chartWeight {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] : E → ℝ :=
  (e.extend I).target.indicator (hμ.exists_density_of_mem_maximalAtlas he ν).choose

/-- Off `(e.extend I).target`, the canonical chart weight vanishes. -/
theorem IsPositiveDensityMeasure.chartWeight_eq_zero_of_notMem {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {y : E} (hy : y ∉ (e.extend I).target) :
    hμ.chartWeight he ν y = 0 :=
  indicator_of_notMem hy _

theorem IsPositiveDensityMeasure.continuousOn_chartWeight {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] :
    ContinuousOn (hμ.chartWeight he ν) (e.extend I).target :=
  (hμ.exists_density_of_mem_maximalAtlas he ν).choose_spec.1.congr fun _ hy ↦
    indicator_of_mem hy _

theorem IsPositiveDensityMeasure.chartWeight_pos {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {y : E} (hy : y ∈ (e.extend I).target) :
    0 < hμ.chartWeight he ν y := by
  rw [chartWeight, indicator_of_mem hy]
  exact (hμ.exists_density_of_mem_maximalAtlas he ν).choose_spec.2.1 y hy

theorem IsPositiveDensityMeasure.map_restrict_eq_withDensity_chartWeight {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦
        ENNReal.ofReal (hμ.chartWeight he ν y) := by
  refine (hμ.exists_density_of_mem_maximalAtlas he ν).choose_spec.2.2.trans
    (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem (e.measurableSet_extend_target I)] with y hy
  rw [chartWeight, indicator_of_mem hy]

/-- Uniqueness of the continuous chart weight on `(e.extend I).target`: any continuous nonnegative
function on `(e.extend I).target` presenting `(μ.restrict e.source).map (e.extend I)` against `ν`
agrees with `hμ.chartWeight he ν` on `(e.extend I).target`. -/
theorem IsPositiveDensityMeasure.chartWeight_eqOn_target_of_map_restrict_eq {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    EqOn (hμ.chartWeight he ν) w (e.extend I).target := by
  have heq :
      (ν.restrict (e.extend I).target).withDensity
          (fun y ↦ ENNReal.ofReal (hμ.chartWeight he ν y)) =
        (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) :=
    (hμ.map_restrict_eq_withDensity_chartWeight he ν).symm.trans hmap
  rw [e.extend_target] at heq hw hw0 ⊢
  exact I.eqOn_of_withDensity_ofReal_eq e.open_target
    (by simpa only [e.extend_target] using hμ.continuousOn_chartWeight he ν) hw
    (fun y hy ↦ (hμ.chartWeight_pos he ν (by simpa only [e.extend_target] using hy)).le) hw0 heq

/-- Function-level uniqueness of the continuous chart weight: any continuous nonnegative function
on `(e.extend I).target` that vanishes off `(e.extend I).target` and presents
`(μ.restrict e.source).map (e.extend I)` against `ν` equals `hμ.chartWeight he ν`. -/
theorem IsPositiveDensityMeasure.chartWeight_eq_of_map_restrict_eq {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y)
    (hw_out : ∀ y ∉ (e.extend I).target, w y = 0)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    hμ.chartWeight he ν = w := by
  ext y
  by_cases hy : y ∈ (e.extend I).target
  · exact hμ.chartWeight_eqOn_target_of_map_restrict_eq he ν hw hw0 hmap hy
  · rw [hμ.chartWeight_eq_zero_of_notMem he ν hy, hw_out y hy]

/-- Changing the reference additive Haar measure from `ν₁` to `ν₂` multiplies the chart weight by
`Measure.addHaarScalarFactor ν₁ ν₂`. -/
theorem IsPositiveDensityMeasure.chartWeight_eq_addHaarScalarFactor_mul {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν₁ ν₂ : Measure E) [ν₁.IsAddHaarMeasure] [ν₂.IsAddHaarMeasure] :
    hμ.chartWeight he ν₂ =
      fun y ↦ (Measure.addHaarScalarFactor ν₁ ν₂ : ℝ) * hμ.chartWeight he ν₁ y := by
  have hmap : (μ.restrict e.source).map (e.extend I) =
      (ν₂.restrict (e.extend I).target).withDensity fun z ↦
        ENNReal.ofReal ((Measure.addHaarScalarFactor ν₁ ν₂ : ℝ) * hμ.chartWeight he ν₁ z) := by
    rw [hμ.map_restrict_eq_withDensity_chartWeight he ν₁, ← restrict_withDensity',
      Measure.withDensity_eq_withDensity_addHaarScalarFactor_mul ν₁ ν₂, restrict_withDensity']
    refine congrArg (ν₂.restrict (e.extend I).target).withDensity (funext fun z ↦ ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
  exact hμ.chartWeight_eq_of_map_restrict_eq he ν₂
    (continuousOn_const.mul (hμ.continuousOn_chartWeight he ν₁))
    (fun z hz ↦ mul_nonneg (Measure.addHaarScalarFactor ν₁ ν₂).coe_nonneg
      (hμ.chartWeight_pos he ν₁ hz).le)
    (fun z hz ↦ by rw [hμ.chartWeight_eq_zero_of_notMem he ν₁ hz, mul_zero])
    hmap

/-- Integration in coordinates against a positive continuous density measure over a measurable
subset of a chart source. No measurability of `f` is required. -/
theorem IsPositiveDensityMeasure.setLIntegral_of_subset {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s,
        ENNReal.ofReal (hμ.chartWeight he ν y) * f ((e.extend I).symm y) ∂ν :=
  e.setLIntegral_eq_of_map_restrict_eq I (hμ.continuousOn_chartWeight he ν)
    (hμ.map_restrict_eq_withDensity_chartWeight he ν) hs hsub f

/-- Measuring a measurable subset of a chart source in coordinates. -/
theorem IsPositiveDensityMeasure.measure_apply_of_subset {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    μ s = ∫⁻ y in e.extend I '' s, ENNReal.ofReal (hμ.chartWeight he ν y) ∂ν := by
  simpa only [mul_one, setLIntegral_one] using
    hμ.setLIntegral_of_subset he ν hs hsub (fun _ ↦ 1)

/-- **Jacobian change-of-variables rule for chart weights.** On the overlap of two charts `e, e'`
of the `C¹` maximal atlas, the weight in `e` equals the absolute Jacobian determinant of the
transition `e' ∘ e⁻¹` times the weight in `e'`. -/
theorem IsPositiveDensityMeasure.chartWeight_changeChart {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    hμ.chartWeight he ν y =
      |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
        hμ.chartWeight he' ν (I.extendCoordChange e e' y) :=
  I.eqOn_abs_det_mul_of_map_restrict_eq he he'
    (hμ.continuousOn_chartWeight he ν) (hμ.continuousOn_chartWeight he' ν)
    (fun _ hz ↦ (hμ.chartWeight_pos he ν hz).le)
    (fun _ hz ↦ (hμ.chartWeight_pos he' ν hz).le)
    (hμ.map_restrict_eq_withDensity_chartWeight he ν)
    (hμ.map_restrict_eq_withDensity_chartWeight he' ν) hy

/-- Boundaryless specialization of the Jacobian transformation law for chart weights. -/
theorem IsPositiveDensityMeasure.chartWeight_changeChart_modelWithCornersSelf
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]
    [MeasurableSpace N] [BorelSpace N] {μ : Measure N}
    (hμ : IsPositiveDensityMeasure 𝓘(ℝ, E) μ) {e e' : OpenPartialHomeomorph N E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N)
    (ν : Measure E) [ν.IsAddHaarMeasure] {y : E} (hy : y ∈ (e.symm.trans e').source) :
    hμ.chartWeight he ν y =
      |(fderiv ℝ (e' ∘ e.symm) y).det| * hμ.chartWeight he' ν (e' (e.symm y)) := by
  have hy' : y ∈ (𝓘(ℝ, E).extendCoordChange e e').source := by
    rw [ModelWithCorners.extendCoordChange_source]
    simpa only [modelWithCornersSelf_coe, image_id] using hy
  have hfun : ⇑(𝓘(ℝ, E).extendCoordChange e e') = e' ∘ e.symm := by
    ext z
    simp [ModelWithCorners.extendCoordChange]
  have h := hμ.chartWeight_changeChart he he' ν hy'
  rw [hfun, modelWithCornersSelf_coe, range_id, fderivWithin_univ] at h
  exact h

private theorem measure_eq_zero_iff_measure_extend_image_eq_zero_of_measurableSet {μ : Measure M}
    (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
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

/-- On the source of any chart of the `C¹` maximal atlas, an arbitrary (not necessarily
measurable) subset has `μ`-measure zero iff its coordinate image has additive Haar measure zero. -/
theorem IsPositiveDensityMeasure.measure_eq_zero_iff_measure_extend_image_eq_zero
    {μ : Measure M} (hμ : IsPositiveDensityMeasure I μ) {e : OpenPartialHomeomorph M H}
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

omit [IsManifold I 1 M] [FiniteDimensional ℝ E] in
/-- Every `μ`-null set of a positive continuous density measure is chartwise null. No Lindelöf
assumption on `M` is needed for this direction. -/
theorem IsPositiveDensityMeasure.isNullSet_of_measure_eq_zero
    {μ : Measure M} (hμ : IsPositiveDensityMeasure I μ) {s : Set M} (hs : μ s = 0) :
    IsNullSet I s := by
  rw [isNullSet_iff]
  intro x ν _
  exact (hμ.measure_eq_zero_iff_image_of_subset inter_subset_right ν).1
    (measure_mono_null inter_subset_left hs)

end ChartWeight

end TauCeti
