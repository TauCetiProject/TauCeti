/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.Boundary.Basic
import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null sets on manifolds

This file defines chartwise nullity for subsets of a charted manifold, without installing a
measurable structure on the manifold itself.  The definition is independent of the choice of Haar
measure on the model and has the usual subset and countable-union closure properties. On a
manifold with a finite-dimensional model a null set has empty interior, so its complement is
dense; this is how Sard's theorem produces regular values.

Nullity of an image `f '' s` under a map between manifolds can be checked on coordinate
expressions (`TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`): when the source is
Lindelöf, it suffices that every coordinate expression
`extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm` sends the chart image of the points of `s` seen by
both charts to a Haar-null set. This is how Sard-type statements about maps between normed spaces
pass to manifolds.
-/

public section

open Set
open MeasureTheory
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A set is null on a manifold when its image in every extended chart is null for every Haar
measure on the model.  This definition needs no measurable structure on the manifold itself. -/
def IsNullSet (I : ModelWithCorners ℝ E H) [MeasurableSpace E] [hE : BorelSpace E]
    (s : Set M) : Prop :=
  let _ : BorelSpace E := hE
  ∀ x : M, ∀ (μ : Measure E) [μ.IsAddHaarMeasure],
    μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0

/-- The chartwise characterization of `IsNullSet`. -/
theorem isNullSet_iff (I : ModelWithCorners ℝ E H) [MeasurableSpace E] [hE : BorelSpace E]
    (s : Set M) :
    IsNullSet I s ↔ ∀ x : M, ∀ (μ : Measure E) [μ.IsAddHaarMeasure],
      μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 := by
  rfl

/-- The chartwise nullity statement for a null set at a point and Haar measure. -/
theorem IsNullSet.chartwise {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s : Set M} (hs : IsNullSet I s) (x : M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 :=
  (isNullSet_iff I s).1 hs x μ

/-- A subset of a null set is null. -/
theorem IsNullSet.mono {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s t : Set M} (ht : IsNullSet I t) (hst : s ⊆ t) : IsNullSet I s := by
  rw [isNullSet_iff] at ht ⊢
  intro x μ hμ
  apply measure_mono_null _ (ht x μ)
  exact image_mono (inter_subset_inter_left _ hst)

/-- The union of two null sets is null. -/
theorem IsNullSet.union {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s t : Set M} (hs : IsNullSet I s) (ht : IsNullSet I t) : IsNullSet I (s ∪ t) := by
  rw [isNullSet_iff] at hs ht ⊢
  intro x μ hμ
  rw [union_inter_distrib_right, image_union]
  exact measure_union_null (hs x μ) (ht x μ)

/-- A countable union of null sets is null. -/
theorem IsNullSet.iUnion {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {ι : Sort*} [Countable ι] {s : ι → Set M} (hs : ∀ i, IsNullSet I (s i)) :
    IsNullSet I (⋃ i, s i) := by
  rw [isNullSet_iff]
  intro x μ hμ
  rw [iUnion_inter, image_iUnion]
  exact measure_iUnion_null fun i ↦ (hs i).chartwise x μ

/-- A union of null sets indexed by a countable set is null. -/
theorem IsNullSet.biUnion {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {ι : Type*} {t : Set ι} (ht : t.Countable) {s : ι → Set M}
    (hs : ∀ i ∈ t, IsNullSet I (s i)) : IsNullSet I (⋃ i ∈ t, s i) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]
  exact IsNullSet.iUnion fun i ↦ hs i i.2

/-- On a manifold with a finite-dimensional model, a null set has empty interior. -/
theorem IsNullSet.interior_eq_empty {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {s : Set M} (hs : IsNullSet I s) : interior s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  -- The chart image of `s` near `y` is a neighbourhood of the chart image of `y` in `range I`.
  have himage : extChartAt I y '' (s ∩ (extChartAt I y).source) ∈
      𝓝[range I] extChartAt I y y := by
    rw [← map_extChartAt_nhds]
    exact Filter.image_mem_map
      (Filter.inter_mem (mem_interior_iff_mem_nhds.1 hy) (extChartAt_source_mem_nhds y))
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 himage
  -- As `range I` lies in the closure of its interior, that neighbourhood contains an open set.
  obtain ⟨z, hz⟩ := mem_closure_iff_nhds.1 (I.range_subset_closure_interior (mem_range_self _))
    (interior U) (interior_mem_nhds.2 hU)
  have hpos := (isOpen_interior.inter isOpen_interior).measure_pos
    (Measure.addHaar : Measure E) ⟨z, hz⟩
  refine hpos.ne' (measure_mono_null ?_ (hs.chartwise y Measure.addHaar))
  exact fun w hw ↦ hUsub ⟨interior_subset hw.1, interior_subset hw.2⟩

/-- On a manifold with a finite-dimensional model, the complement of a null set is dense. -/
theorem IsNullSet.dense_compl {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {s : Set M} (hs : IsNullSet I s) : Dense sᶜ :=
  interior_eq_empty_iff_dense_compl.1 hs.interior_eq_empty

/-- The intrinsic boundary of any finite-dimensional real manifold is chartwise null.
No measurable structure on the manifold itself is required. -/
theorem isNullSet_boundary {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] : IsNullSet I (I.boundary M) := by
  rw [isNullSet_iff]
  intro x μ hμ
  refine measure_mono_null ?_ (I.convex_range.addHaar_frontier μ)
  rintro y ⟨z, hz, rfl⟩
  have hsource : z ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using hz.2
  exact (ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range one_ne_zero
    (IsManifold.chart_mem_maximalAtlas x) hsource).mp hz.1

section Image

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] [TopologicalSpace H'] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {f : M → N} {s : Set M}

/-- **Nullity of an image is read in coordinates.** Let `M` be Lindelöf. Suppose that for every
chart at `x₀` of `M` and every chart at `y₀` of `N`, the coordinate expression
`extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm` sends the chart image of the points of `s` lying in
both charts to a set that is null for every Haar measure. Then `f '' s` is null in `N`.

No regularity of `f` is assumed, and both manifolds may have boundary or corners. -/
theorem isNullSet_image_of_forall_addHaar_image_extChartAt [LindelofSpace M]
    (h : ∀ (x₀ : M) (y₀ : N) (μ : Measure E') [μ.IsAddHaarMeasure],
      μ ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) ''
        (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source))) = 0) :
    IsNullSet J (f '' s) := by
  obtain ⟨t, htc, -, hcover⟩ := isLindelof_univ.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have hst : s = ⋃ x ∈ t, s ∩ (chartAt H x).source := by
    rw [← inter_iUnion₂, eq_comm, inter_eq_left]
    exact (subset_univ s).trans hcover
  rw [hst, image_iUnion₂]
  refine IsNullSet.biUnion htc fun x₀ _ ↦ (isNullSet_iff J _).2 fun y₀ μ _ ↦ ?_
  convert h x₀ y₀ μ using 2
  -- On the source of the chart at `x₀`, the inverse chart undoes the chart.
  rw [extChartAt_source, ← image_inter_preimage, image_image, image_image]
  refine image_congr fun x hx ↦ ?_
  have hx' : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.1.2
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv hx']

end Image

end TauCeti
