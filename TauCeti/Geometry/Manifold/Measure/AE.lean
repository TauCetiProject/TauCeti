/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.Differentiable
public import Mathlib.Order.Filter.CountableInter
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The almost-everywhere filter on a manifold

A property holds almost everywhere on a manifold `M` when the set where it fails is chartwise null
(`TauCeti.IsNullSet`). This file packages these sets as a filter `TauCeti.Manifold.ae I M`, with
the countable intersection property. Like `TauCeti.IsNullSet`, the filter needs no metric, no
measurable structure on `M` and no choice of Haar measure on the model.

Null sets can be read in charts of the maximal atlas rather than only in the preferred charts: the
image of a null set in any chart of the `C¹` maximal atlas is null for every additive Haar measure,
and a set is null as soon as its images in the charts of a countable `C¹` atlas are null for one
additive Haar measure.

## Main definitions and results

* `TauCeti.Manifold.ae I M`: the filter of subsets of `M` with null complement.
* `TauCeti.Manifold.ae_eq_of_forall_measure_eq_zero_iff`: a measure on `M` whose null sets are the
  chartwise null sets has `TauCeti.Manifold.ae I M` as its almost-everywhere filter.
* `TauCeti.isNullSet_iff_of_isAddHaarMeasure`: one additive Haar measure on the model suffices to
  test nullity in the preferred charts.
* `TauCeti.IsNullSet.measure_extend_image_eq_zero`: the image of a null set in a chart of the
  `C¹` maximal atlas is null.
* `TauCeti.isNullSet_iff_of_iUnion_source_eq_univ`: nullity is tested in the charts of a countable
  `C¹` atlas, for one additive Haar measure.
-/

public section

open Filter Module Set
open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable (I M) in
/-- The almost-everywhere filter on a manifold: a set belongs to it when its complement is
chartwise null. It needs no measurable structure on the manifold. -/
def ae : Filter M :=
  Filter.ofCountableUnion {s | IsNullSet I s}
    (fun _ hS h ↦ by rw [sUnion_eq_biUnion]; exact IsNullSet.biUnion hS h)
    fun _ ht _ hst ↦ IsNullSet.mono ht hst

theorem mem_ae_iff {s : Set M} : s ∈ ae I M ↔ IsNullSet I sᶜ :=
  Iff.rfl

theorem ae_iff {p : M → Prop} : (∀ᶠ x in ae I M, p x) ↔ IsNullSet I {x | ¬p x} :=
  Iff.rfl

theorem compl_mem_ae_iff {s : Set M} : sᶜ ∈ ae I M ↔ IsNullSet I s := by
  rw [mem_ae_iff, compl_compl]

instance : CountableInterFilter (ae I M) :=
  Filter.countableInter_ofCountableUnion _ _ _

/-- On a nonempty manifold with a finite-dimensional model, the almost-everywhere filter is
proper: the whole manifold is not null. -/
instance [FiniteDimensional ℝ E] [Nonempty M] : (ae I M).NeBot := by
  refine ⟨fun h ↦ ?_⟩
  have hnull : IsNullSet I (univ : Set M) := by
    rw [← compl_empty, ← compl_mem_ae_iff, compl_empty, h]
    exact mem_bot
  have := hnull.interior_eq_empty
  rw [interior_univ] at this
  exact univ_nonempty.ne_empty this

/-- On a manifold with a nontrivial finite-dimensional model, almost every point differs from a
given point. -/
theorem ae_ne [FiniteDimensional ℝ E] [Nontrivial E] (x : M) : ∀ᶠ y in ae I M, y ≠ x := by
  rw [ae_iff]
  simpa using (countable_singleton x).isNullSet (I := I)

/-- A measure on `M` whose null sets are exactly the chartwise null sets has the manifold
almost-everywhere filter as its almost-everywhere filter. -/
theorem ae_eq_of_forall_measure_eq_zero_iff [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (h : ∀ s : Set M, μ s = 0 ↔ IsNullSet I s) : MeasureTheory.ae μ = ae I M :=
  Filter.ext fun _ ↦ by rw [MeasureTheory.mem_ae_iff, mem_ae_iff, h]

end Manifold

theorem IsNullSet.compl_mem_ae {s : Set M} (hs : IsNullSet I s) : sᶜ ∈ Manifold.ae I M :=
  Manifold.compl_mem_ae_iff.2 hs

section Charts

variable [FiniteDimensional ℝ E]

/-- Nullity in the preferred charts can be tested with one additive Haar measure on the model. -/
theorem isNullSet_iff_of_isAddHaarMeasure (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    {s : Set M} :
    IsNullSet I s ↔ ∀ x : M, μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 :=
  ⟨fun hs x ↦ hs.chartwise x μ, fun h ↦ (isNullSet_iff I s).2 fun x ν _ ↦
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure ν μ (h x)⟩

variable [IsManifold I 1 M] {e : OpenPartialHomeomorph M H}

/-- The image of a null set in a chart of the `C¹` maximal atlas is null for every additive Haar
measure on the model. -/
theorem IsNullSet.measure_extend_image_eq_zero [LindelofSpace M] {s : Set M} (hs : IsNullSet I s)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] : μ (e.extend I '' (s ∩ e.source)) = 0 :=
  (isNullSet_modelWithCornersSelf_iff μ).1 <| (hs.mono inter_subset_left).image_of_mdifferentiableOn
    le_rfl ((e.mdifferentiableOn_extend he).mono inter_subset_right)

/-- A subset of the source of a chart of the `C¹` maximal atlas is null when its image in the
chart is null for one additive Haar measure on the model. -/
theorem isNullSet_of_measure_extend_image_eq_zero {s : Set M} (hsub : s ⊆ e.source)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hs : μ (e.extend I '' s) = 0) : IsNullSet I s := by
  have hsub' : s ⊆ (e.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
  rw [← (e.extend I).symm_image_image_of_subset_source hsub']
  exact ((isNullSet_modelWithCornersSelf_iff μ).2 hs).image_of_mdifferentiableOn le_rfl
    ((mdifferentiableOn_extend_symm he).mono (image_subset_iff.2 fun _ hx ↦
      (e.extend I).map_source (hsub' hx)))

/-- **Nullity is read in a countable atlas.** If the sources of countably many charts of the `C¹`
maximal atlas cover `M`, a set is null exactly when its image in each of these charts is null for
one given additive Haar measure on the model. -/
theorem isNullSet_iff_of_iUnion_source_eq_univ [LindelofSpace M] {ι : Sort*} [Countable ι]
    {e : ι → OpenPartialHomeomorph M H} (he : ∀ i, e i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (e i).source = univ) (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    {s : Set M} :
    IsNullSet I s ↔ ∀ i, μ ((e i).extend I '' (s ∩ (e i).source)) = 0 := by
  refine ⟨fun hs i ↦ hs.measure_extend_image_eq_zero (he i) μ, fun h ↦ ?_⟩
  have hs : s = ⋃ i, s ∩ (e i).source := by rw [← inter_iUnion, hcover, inter_univ]
  rw [hs]
  exact IsNullSet.iUnion fun i ↦
    isNullSet_of_measure_extend_image_eq_zero inter_subset_right (he i) μ (h i)

end Charts

end TauCeti
