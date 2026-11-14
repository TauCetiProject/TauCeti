/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.AE
public import TauCeti.Geometry.Manifold.Measure.Differentiable
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Null sets and almost everywhere in charts of the maximal atlas

Let `M` be a manifold, possibly with boundary or corners, modelled on a finite-dimensional real
normed space `E`. Null sets of `M` (`TauCeti.IsNullSet`) and the almost-everywhere filter
`TauCeti.Manifold.ae I M` can be read in charts of the maximal atlas rather than only in the
preferred charts: the image of a null set in any chart of the `C¹` maximal atlas is null for every
additive Haar measure, and a set is null as soon as its images in the charts of a countable `C¹`
atlas are null for one additive Haar measure. No Lindelöf or second countability assumption on `M`
is needed.

## Main results

* `TauCeti.isNullSet_iff_of_isAddHaarMeasure`, `TauCeti.Manifold.ae_iff_of_isAddHaarMeasure`: one
  additive Haar measure on the model suffices to test nullity, and almost everywhere, in the
  preferred charts.
* `TauCeti.IsNullSet.measure_extend_image_eq_zero`,
  `TauCeti.isNullSet_iff_measure_extend_image_eq_zero`, `TauCeti.Manifold.ae_extend_of_ae`: null
  sets, and almost everywhere, are read in a chart of the `C¹` maximal atlas.
* `TauCeti.isNullSet_iff_of_iUnion_source_eq_univ`,
  `TauCeti.Manifold.ae_iff_of_iUnion_source_eq_univ`: nullity, and almost everywhere, are tested
  in the charts of a countable `C¹` atlas, for one additive Haar measure.
* `TauCeti.Manifold.ae_modelWithCornersSelf`: on the model space itself, the almost-everywhere
  filter is that of any additive Haar measure.
-/

public section

open Filter MeasureTheory Module Set
open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Nullity in the preferred charts can be tested with one additive Haar measure on the
finite-dimensional model. -/
theorem isNullSet_iff_of_isAddHaarMeasure (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set M} :
    IsNullSet I s ↔ ∀ x : M, μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 :=
  ⟨fun hs x ↦ hs.chartwise x μ, fun h ↦ (isNullSet_iff I s).2 fun x ν _ ↦
    Measure.absolutelyContinuous_isAddHaarMeasure ν μ (h x)⟩

namespace Manifold

/-- On a finite-dimensional model space, the almost-everywhere filter of the model seen as a
manifold is the almost-everywhere filter of any additive Haar measure. -/
theorem ae_modelWithCornersSelf (μ : Measure E) [μ.IsAddHaarMeasure] :
    ae 𝓘(ℝ, E) E = MeasureTheory.ae μ :=
  (ae_eq_iff_forall_measure_eq_zero_iff.2 fun _ ↦ (isNullSet_modelWithCornersSelf_iff μ).symm).symm

/-- Almost everywhere on `M` is read in the preferred charts with one additive Haar measure on the
finite-dimensional model: a property holds almost everywhere exactly when, in each preferred chart,
it holds at the preimage of almost every point of the chart target. -/
theorem ae_iff_of_isAddHaarMeasure (μ : Measure E) [μ.IsAddHaarMeasure] {p : M → Prop} :
    (∀ᶠ x in ae I M, p x) ↔
      ∀ x₀ : M, ∀ᵐ y ∂μ, y ∈ (extChartAt I x₀).target → p ((extChartAt I x₀).symm y) := by
  refine ae_iff.trans <| (isNullSet_iff_of_isAddHaarMeasure μ).trans <| forall_congr' fun x₀ ↦ ?_
  rw [MeasureTheory.ae_iff, inter_comm, PartialEquiv.image_source_inter_eq']
  simp only [not_imp]
  rfl

end Manifold

variable [IsManifold I 1 M] {e : OpenPartialHomeomorph M H}

/-- The image of a null set in a chart of the `C¹` maximal atlas is null for every additive Haar
measure on the finite-dimensional model. -/
theorem IsNullSet.measure_extend_image_eq_zero {s : Set M} (hs : IsNullSet I s)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (e.extend I '' (s ∩ e.source)) = 0 := by
  -- The source of `e` is second countable, so countably many preferred charts cover it.
  have := I.secondCountableTopology
  have := e.secondCountableTopology_source
  obtain ⟨t, htc, -, hcover⟩ := (isLindelof_iff_lindelofSpace (s := e.source)).2 inferInstance
    |>.elim_nhds_subcover (fun x : M ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have hst : s ∩ e.source = ⋃ x ∈ t, s ∩ e.source ∩ (chartAt H x).source := by
    rw [← inter_iUnion₂, eq_comm, inter_eq_left]
    exact inter_subset_right.trans hcover
  rw [hst, image_iUnion₂]
  refine (measure_biUnion_null_iff htc).2 fun x _ ↦ ?_
  -- In the chart at `x`, the piece is the image of a null set of the model under a coordinate
  -- change.
  have hA : s ∩ e.source ∩ (chartAt H x).source ⊆ (extChartAt I x).source := by
    rw [extChartAt_source]
    exact inter_subset_right
  rw [← (extChartAt I x).symm_image_image_of_subset_source hA, image_image]
  refine (isNullSet_modelWithCornersSelf_iff μ).1 <|
    ((isNullSet_modelWithCornersSelf_iff μ).2 ?_).image_of_mdifferentiableOn le_rfl ?_
  · refine measure_mono_null (image_mono ?_) (hs.chartwise x μ)
    exact fun y hy ↦ ⟨hy.1.1, hA hy⟩
  · refine (e.mdifferentiableOn_extend he).comp ((mdifferentiableOn_extChartAt_symm (x := x)).mono
      (image_subset_iff.2 fun y hy ↦ (extChartAt I x).map_source (hA hy))) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_preimage, (extChartAt I x).left_inv (hA hy)]
    exact hy.1.2

/-- A subset of the source of a chart of the `C¹` maximal atlas is null when its image in the
chart is null for one additive Haar measure on the finite-dimensional model. -/
theorem isNullSet_of_measure_extend_image_eq_zero {s : Set M} (hsub : s ⊆ e.source)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : μ (e.extend I '' s) = 0) : IsNullSet I s := by
  have hsub' : s ⊆ (e.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
  rw [← (e.extend I).symm_image_image_of_subset_source hsub']
  exact ((isNullSet_modelWithCornersSelf_iff μ).2 hs).image_of_mdifferentiableOn le_rfl
    ((mdifferentiableOn_extend_symm he).mono (image_subset_iff.2 fun _ hx ↦
      (e.extend I).map_source (hsub' hx)))

/-- A subset of the source of a chart of the `C¹` maximal atlas is null exactly when its image in
the chart is null for one additive Haar measure on the finite-dimensional model. -/
theorem isNullSet_iff_measure_extend_image_eq_zero {s : Set M} (hsub : s ⊆ e.source)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsNullSet I s ↔ μ (e.extend I '' s) = 0 :=
  ⟨fun hs ↦ inter_eq_left.2 hsub ▸ hs.measure_extend_image_eq_zero he μ,
    isNullSet_of_measure_extend_image_eq_zero hsub he μ⟩

/-- **Nullity is read in a countable atlas.** If the sources of countably many charts of the `C¹`
maximal atlas cover `M`, a set is null exactly when its image in each of these charts is null for
one given additive Haar measure on the finite-dimensional model. -/
theorem isNullSet_iff_of_iUnion_source_eq_univ {ι : Sort*} [Countable ι]
    {e : ι → OpenPartialHomeomorph M H} (he : ∀ i, e i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (e i).source = univ) (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set M} :
    IsNullSet I s ↔ ∀ i, μ ((e i).extend I '' (s ∩ (e i).source)) = 0 := by
  refine ⟨fun hs i ↦ hs.measure_extend_image_eq_zero (he i) μ, fun h ↦ ?_⟩
  have hs : s = ⋃ i, s ∩ (e i).source := by rw [← inter_iUnion, hcover, inter_univ]
  rw [hs]
  exact IsNullSet.iUnion fun i ↦
    isNullSet_of_measure_extend_image_eq_zero inter_subset_right (he i) μ (h i)

namespace Manifold

/-- A property holding almost everywhere on `M` holds, in a chart of the `C¹` maximal atlas, at the
preimage of almost every point of the chart target, for every additive Haar measure on the
finite-dimensional model. -/
theorem ae_extend_of_ae {p : M → Prop} (hp : ∀ᶠ x in ae I M, p x)
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ y ∂μ, y ∈ (e.extend I).target → p ((e.extend I).symm y) := by
  have := (ae_iff.1 hp).measure_extend_image_eq_zero he μ
  rw [inter_comm, ← e.extend_source (I := I), PartialEquiv.image_source_inter_eq'] at this
  rw [MeasureTheory.ae_iff]
  simp only [not_imp]
  exact this

/-- **Almost everywhere is read in a countable atlas.** If the sources of countably many charts of
the `C¹` maximal atlas cover `M`, a property holds almost everywhere exactly when, in each of these
charts, it holds at the preimage of almost every point of the chart target, for one given additive
Haar measure on the finite-dimensional model. -/
theorem ae_iff_of_iUnion_source_eq_univ {ι : Sort*} [Countable ι]
    {e : ι → OpenPartialHomeomorph M H} (he : ∀ i, e i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (e i).source = univ) (μ : Measure E) [μ.IsAddHaarMeasure] {p : M → Prop} :
    (∀ᶠ x in ae I M, p x) ↔
      ∀ i, ∀ᵐ y ∂μ, y ∈ ((e i).extend I).target → p (((e i).extend I).symm y) := by
  refine ae_iff.trans <| (isNullSet_iff_of_iUnion_source_eq_univ he hcover μ).trans <|
    forall_congr' fun i ↦ ?_
  rw [MeasureTheory.ae_iff, inter_comm, ← (e i).extend_source (I := I),
    PartialEquiv.image_source_inter_eq']
  simp only [not_imp]
  rfl

end Manifold

end TauCeti
