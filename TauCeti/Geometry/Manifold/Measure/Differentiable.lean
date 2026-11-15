/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Haar.Differentiable

/-!
# Differentiable images of null sets on manifolds

Let `M` and `N` be real manifolds, possibly with boundary or corners, modelled on
finite-dimensional spaces `E` and `F` with `finrank ℝ E ≤ finrank ℝ F`, and let `M` be Lindelöf.
A map `g : M → N` that is differentiable within a null set `A` of `M` sends it to a null set of
`N`. No measurable structure on `M` or `N` and no measurability of `A` is needed.

In charts this is `DifferentiableOn.addHaar_image_eq_zero`, and nullity of an image is read in
charts by `TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`.

A finite-dimensional real normed space, seen as a manifold modelled on itself, has as null sets
exactly the sets that are null for an additive Haar measure, since any two additive Haar measures
are mutually absolutely continuous. This lets maps from or to a normed space be treated in the same
way.

## Main results

* `TauCeti.isNullSet_modelWithCornersSelf_iff`: in a finite-dimensional real normed space, null
  sets are the Haar-null sets.
* `TauCeti.IsNullSet.image_of_mdifferentiableOn`: a map differentiable within a null set sends
  it to a null set, when the dimension of the source is at most that of the target.
* `TauCeti.IsNullSet.measure_inter_preimage_extend_symm_eq_zero`: in any `C¹` maximal-atlas chart
  `φ`, the points of `(φ.extend I).target` sent by `(φ.extend I).symm` into a null set form a
  Haar-null set (without any Lindelöf hypothesis on `M`).
-/

public section

open Filter MeasureTheory Module Set TopologicalSpace Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {g : M → N} {A : Set M}

/-- A subset of a finite-dimensional real normed space, seen as a manifold modelled on itself, is
null exactly when it is null for an additive Haar measure. -/
theorem isNullSet_modelWithCornersSelf_iff (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} :
    IsNullSet 𝓘(ℝ, E) s ↔ μ s = 0 := by
  refine ⟨fun hs ↦ by simpa [extChartAt_model_space_eq_id] using hs.chartwise 0 μ,
    fun hs ↦ (isNullSet_iff _ _).2 fun x ν _ ↦ ?_⟩
  simpa [extChartAt_model_space_eq_id] using Measure.absolutelyContinuous_isAddHaarMeasure ν μ hs

/-- **Differentiable maps preserve null sets.** Let `M` be Lindelöf, with model of dimension at
most that of the model of `N`. If `g : M → N` is differentiable within a null set `A`, then
`g '' A` is null. -/
theorem IsNullSet.image_of_mdifferentiableOn (hA : IsNullSet I A)
    (hdim : finrank ℝ E ≤ finrank ℝ F) (hg : MDifferentiableOn I J g A) :
    IsNullSet J (g '' A) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ ν _ ↦ ?_
  refine DifferentiableOn.addHaar_image_eq_zero (Basis.addHaar (finBasis ℝ E)) ν hdim ?_ ?_
  · exact ((mdifferentiableOn_iff_of_subset_source (s := A ∩ _ ∩ g ⁻¹' _) (fun _ hx ↦ hx.1.2)
      fun _ hx ↦ hx.2).1 (hg.mono fun _ hx ↦ hx.1.1)).2
  · refine measure_mono_null (image_mono ?_) (hA.chartwise x₀ (finBasis ℝ E).addHaar)
    rintro x ⟨⟨hxA, hxsrc⟩, -⟩
    exact ⟨hxA, by rwa [extChartAt_source]⟩

omit [LindelofSpace M] in
private theorem measure_preimage_extend_symm_inter_chartAt_eq_zero (hA : IsNullSet I A)
    {φ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas I 1 M)
    (x₀ : M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ {z ∈ interior (φ.extend I).target |
      (φ.extend I).symm z ∈ A ∧ (φ.extend I).symm z ∈ (chartAt H x₀).source} = 0 := by
  have hdiff : DifferentiableOn ℝ (I.extendCoordChange (chartAt H x₀) φ)
      ((extChartAt I x₀ '' (A ∩ (extChartAt I x₀).source)) ∩
        interior ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' φ.source)) :=
    ((I.contDiffOn_extendCoordChange (IsManifold.chart_mem_maximalAtlas x₀) hφ).differentiableOn
      one_ne_zero).mono (inter_subset_right.trans (by
        rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
          φ.extend_source]; exact interior_subset))
  refine measure_mono_null ?_ (hdiff.addHaar_image_eq_zero μ μ le_rfl
    (measure_mono_null inter_subset_left (hA.chartwise x₀ μ)))
  rintro z ⟨hzint, hzA, hzx₀⟩
  have hzt : z ∈ (φ.extend I).target := interior_subset hzint
  have hzxφ : (φ.extend I).symm z ∈ φ.source :=
    φ.extend_source (I := I) ▸ (φ.extend I).map_target hzt
  have hzx₀' : (φ.extend I).symm z ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  exact ⟨extChartAt I x₀ ((φ.extend I).symm z), ⟨⟨_, ⟨hzA, hzx₀'⟩, rfl⟩,
    mem_interior_iff_mem_nhds.2 (inter_mem (mem_interior_iff_mem_nhds.1
      (ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero
        hφ (IsManifold.chart_mem_maximalAtlas x₀) hzxφ hzx₀ (by rwa [(φ.extend I).right_inv hzt])))
      ((continuousAt_extChartAt_symm' hzx₀').preimage_mem_nhds
        (by rw [(extChartAt I x₀).left_inv hzx₀']; exact φ.open_source.mem_nhds hzxφ)))⟩,
    by simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply, extChartAt,
      (chartAt H x₀).extend_left_inv hzx₀, (φ.extend I).right_inv hzt]⟩

omit [LindelofSpace M] in
/-- For any `C¹` chart `φ` and null set `A`, `(φ.extend I).target ∩ (φ.extend I).symm ⁻¹' A` has
Haar measure zero (including along `∂(range I)`, without Lindelöf hypotheses on `M`). -/
theorem IsNullSet.measure_inter_preimage_extend_symm_eq_zero (hA : IsNullSet I A)
    {φ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas I 1 M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ ((φ.extend I).target ∩ (φ.extend I).symm ⁻¹' A) = 0 := by
  let U : M → Set E :=
    fun x₀ ↦ interior (φ.extend I).target ∩ (φ.extend I).symm ⁻¹' (chartAt H x₀).source
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable U fun x₀ ↦
    ((φ.continuousOn_extend_symm (I := I)).mono interior_subset).isOpen_inter_preimage
      isOpen_interior (chartAt H x₀).open_source
  have hint : μ {z ∈ interior (φ.extend I).target | (φ.extend I).symm z ∈ A} = 0 := by
    refine measure_mono_null (fun z ⟨hzint, hzA⟩ ↦ ?_) ((measure_biUnion_null_iff hTcnt).2
      fun x₀ _ ↦ measure_preimage_extend_symm_inter_chartAt_eq_zero hA hφ x₀ μ)
    have hzU : z ∈ ⋃ x₀ ∈ T, U x₀ := by
      rw [hTcov]; exact mem_iUnion.2 ⟨(φ.extend I).symm z, hzint, mem_chart_source H _⟩
    rcases mem_iUnion₂.1 hzU with ⟨x₀, hx₀T, _, hzx₀⟩
    exact mem_iUnion₂.2 ⟨x₀, hx₀T, hzint, hzA, hzx₀⟩
  have hbd := φ.measure_diff_interior_extend_eq_zero (I := I) isOpen_univ μ
  simp only [preimage_univ, inter_univ] at hbd
  exact measure_mono_null (fun z ⟨hzt, hzA⟩ ↦ (em (z ∈ interior (φ.extend I).target)).elim
    (fun hz ↦ Or.inr ⟨hz, hzA⟩) (fun hz ↦ Or.inl ⟨hzt, hz⟩)) (measure_union_null hbd hint)

end TauCeti
