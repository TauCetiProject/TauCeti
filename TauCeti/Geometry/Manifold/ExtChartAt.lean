/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability and precompact neighborhoods in extended manifold charts

Mathlib's extended chart at a point is a `PartialEquiv` between a manifold and its model vector
space. Its restrictions to the chart source and target are mutually continuous, hence the chart
restricted to its source is a measurable embedding for Borel measurable spaces. This is the
form used to transport measures between a manifold and coordinates.

Before choosing a measurable structure on the manifold, chart measurability expresses
measurability in each preferred chart. When the chart space `H` is locally compact, compact sets
admit finite open chart covers whose coordinate images lie in compact subsets of the chart targets,
even without Hausdorffness.

## Main results

* `TauCeti.measurableEmbedding_extChartAt_restrict`: an extended chart restricted to its source is
  a measurable embedding.
* `TauCeti.MeasurableSet.image_extChartAt`: the image of a measurable subset of a chart source is
  measurable in the model space.
* `TauCeti.IsChartMeasurable`: chartwise measurability without a measurable structure on the
  manifold.
* `TauCeti.exists_finite_precompact_chart_cover`: finite open chart covers with compact
  coordinate bounds for compact subsets of manifolds modelled on a locally compact space.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An extended chart target is measurable in the model space. -/
theorem measurableSet_extChartAt_target [MeasurableSpace E] [OpensMeasurableSpace E]
    (x : M) : MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- The coordinate image of an open subset of a chart source is measurable, without a
measurable structure on the manifold. -/
theorem _root_.IsOpen.measurableSet_image_extChartAt_source_inter
    [MeasurableSpace E] [OpensMeasurableSpace E] {u : Set M} (hu : IsOpen u) (x : M) :
    MeasurableSet ((extChartAt I x) '' ((extChartAt I x).source ∩ u)) := by
  obtain ⟨v, hv, heq⟩ := continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := I) x) u hu
  rw [(extChartAt I x).image_source_inter_eq', Set.inter_comm, heq]
  exact hv.measurableSet.inter (measurableSet_extChartAt_target (I := I) x)

/-- A set is chart measurable when its part in each preferred chart has measurable coordinate
image. This condition does not install a measurable-space structure on the manifold. -/
def IsChartMeasurable (I : ModelWithCorners 𝕜 E H) [MeasurableSpace E] (s : Set M) : Prop :=
  ∀ x : M, MeasurableSet ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)

/-- The empty set is chart measurable for any measurable structure on the model space;
no `OpensMeasurableSpace` assumption is needed. -/
@[simp]
theorem isChartMeasurable_empty [MeasurableSpace E] :
    IsChartMeasurable I (∅ : Set M) := by
  intro x
  simp only [Set.preimage_empty, Set.inter_empty, MeasurableSet.empty]

/-- The whole manifold is chart measurable when open model sets are measurable. -/
@[simp]
theorem isChartMeasurable_univ [MeasurableSpace E] [OpensMeasurableSpace E] :
    IsChartMeasurable I (Set.univ : Set M) := by
  intro x
  simpa only [Set.preimage_univ, Set.inter_univ] using measurableSet_extChartAt_target (I := I) x

/-- Chart measurability is equivalent to measurability of the source-restricted chart images. -/
theorem isChartMeasurable_iff [MeasurableSpace E] (s : Set M) :
    IsChartMeasurable I s ↔
      ∀ x : M, MeasurableSet ((extChartAt I x) '' ((extChartAt I x).source ∩ s)) := by
  simp only [IsChartMeasurable, PartialEquiv.image_source_inter_eq']

/-- Open sets are chart measurable. -/
theorem _root_.IsOpen.isChartMeasurable [MeasurableSpace E] [OpensMeasurableSpace E]
    {s : Set M} (hs : IsOpen s) : IsChartMeasurable I s := by
  rw [isChartMeasurable_iff]
  exact fun x ↦ hs.measurableSet_image_extChartAt_source_inter x

/-- Chart measurability is closed under intersections. -/
theorem IsChartMeasurable.inter [MeasurableSpace E] {s t : Set M}
    (hs : IsChartMeasurable I s) (ht : IsChartMeasurable I t) :
    IsChartMeasurable I (s ∩ t) := by
  intro x
  rw [Set.preimage_inter, Set.inter_inter_distrib_left]
  exact (hs x).inter (ht x)

/-- Chart measurability is closed under unions. -/
theorem IsChartMeasurable.union [MeasurableSpace E] {s t : Set M}
    (hs : IsChartMeasurable I s) (ht : IsChartMeasurable I t) :
    IsChartMeasurable I (s ∪ t) := by
  intro x
  rw [Set.preimage_union, Set.inter_union_distrib_left]
  exact (hs x).union (ht x)

/-- Chart measurability is closed under countable indexed unions. -/
theorem IsChartMeasurable.iUnion [MeasurableSpace E] {ι : Type*} [Countable ι]
    {s : ι → Set M} (hs : ∀ i, IsChartMeasurable I (s i)) :
    IsChartMeasurable I (⋃ i, s i) := by
  intro x
  rw [Set.preimage_iUnion, Set.inter_iUnion]
  exact MeasurableSet.iUnion fun i ↦ hs i x

/-- Chart measurability is closed under differences. -/
theorem IsChartMeasurable.diff [MeasurableSpace E] {s t : Set M}
    (hs : IsChartMeasurable I s) (ht : IsChartMeasurable I t) :
    IsChartMeasurable I (s \ t) := by
  intro x
  simpa only [Set.preimage_sdiff, Set.inter_sdiff_distrib_left] using (hs x).diff (ht x)

/-- Chart measurability is closed under complements when open model sets are measurable. -/
theorem IsChartMeasurable.compl [MeasurableSpace E] [OpensMeasurableSpace E] {s : Set M}
    (hs : IsChartMeasurable I s) : IsChartMeasurable I sᶜ := by
  simpa only [Set.compl_eq_univ_sdiff] using (isChartMeasurable_univ (I := I)).diff hs

/-- A chart-measurable set contained in a chart source has measurable coordinate image. -/
theorem IsChartMeasurable.image_extChartAt [MeasurableSpace E] {s : Set M}
    (hs : IsChartMeasurable I s) (x : M) (hsub : s ⊆ (extChartAt I x).source) :
    MeasurableSet ((extChartAt I x) '' s) := by
  rw [(extChartAt I x).image_eq_target_inter_inv_preimage hsub]
  exact hs x

/-- Every point has an open neighborhood whose extended-chart image is contained in a compact
subset of the chart target. The manifold need not be Hausdorff. -/
theorem exists_precompact_extChartAt_neighborhood [LocallyCompactSpace H] (x : M) :
    ∃ u : Set M, ∃ b : Set E, IsOpen u ∧ x ∈ u ∧ u ⊆ (extChartAt I x).source ∧
      IsCompact b ∧ b ⊆ (extChartAt I x).target ∧ (extChartAt I x) '' u ⊆ b := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨k, hk, hx, hs⟩ := exists_compact_subset (chartAt H x).open_source
    (mem_chart_source H x)
  have hsource : k ⊆ (extChartAt I x).source := by simpa only [extChartAt_source] using hs
  refine ⟨interior k, (extChartAt I x) '' k, isOpen_interior, hx,
    interior_subset.trans hsource,
    hk.image_of_continuousOn ((continuousOn_extChartAt x).mono hsource), ?_, ?_⟩
  · exact (Set.image_mono hsource).trans (extChartAt I x).image_source_eq_target.subset
  · exact Set.image_mono interior_subset

/-- A compact set has a finite open chart cover with compact coordinate bounds inside the
corresponding chart targets, without a Hausdorff assumption on the manifold. -/
theorem exists_finite_precompact_chart_cover [LocallyCompactSpace H] {s : Set M}
    (hs : IsCompact s) :
    ∃ n : ℕ, ∃ α : Fin n → M, ∃ u : Fin n → Set M, ∃ b : Fin n → Set E,
      (∀ i, IsOpen (u i) ∧ u i ⊆ (extChartAt I (α i)).source ∧ IsCompact (b i) ∧
        b i ⊆ (extChartAt I (α i)).target ∧ (extChartAt I (α i)) '' u i ⊆ b i) ∧
      s ⊆ ⋃ i, u i := by
  classical
  choose u b hu hx hsource hb htarget himage using
    (fun x : M ↦ exists_precompact_extChartAt_neighborhood (I := I) x)
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover u hu
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let α : Fin t.card → M := fun i ↦ ((t.equivFin).symm i).val
  refine ⟨t.card, α, fun i ↦ u (α i), fun i ↦ b (α i), ?_, ?_⟩
  · exact fun i ↦ ⟨hu _, hsource _, hb _, htarget _, himage _⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa [α] using hxy⟩

variable [MeasurableSpace M] [BorelSpace M]

section BorelModel

/-- The Borel measurable space on the model vector space, used in this file. -/
local instance extChartAtMeasurableSpaceE : MeasurableSpace E := borel E

/-- The model vector space's measurable space is its Borel measurable space. -/
local instance extChartAtBorelSpaceE : BorelSpace E := ⟨rfl⟩

/-- The extended chart at `x`, restricted to its source, is a measurable embedding for the Borel
measurable spaces. -/
theorem measurableEmbedding_extChartAt_restrict (x : M) :
    MeasurableEmbedding ((extChartAt I x).source.domRestrict (extChartAt I x)) := by
  -- The extended chart is continuous in both directions, so it is a partial homeomorphism onto
  -- its (not necessarily open) target. `e` is built on the very `PartialEquiv` `extChartAt I x`,
  -- so `e.isEmbedding_restrict` is a statement about the map appearing in the goal.
  let e : PartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I x
      continuousOn_toFun := continuousOn_extChartAt x
      continuousOn_invFun := continuousOn_extChartAt_symm x }
  have hrange :
      MeasurableSet (Set.range ((extChartAt I x).source.domRestrict (extChartAt I x))) := by
    rw [Set.range_domRestrict, PartialEquiv.image_source_eq_target]
    exact measurableSet_extChartAt_target x
  exact e.isEmbedding_restrict.measurableEmbedding hrange

/-- The image of a measurable subset of an extended chart's source is measurable in the model
space. -/
theorem _root_.MeasurableSet.image_extChartAt {s : Set M} (hs : MeasurableSet s) (x : M)
    (hsource : s ⊆ (extChartAt I x).source) : MeasurableSet ((extChartAt I x) '' s) := by
  rw [← Set.inter_eq_left.mpr hsource, ← Set.image_domRestrict]
  exact (measurableEmbedding_extChartAt_restrict (I := I) x).measurableSet_image.mpr
    (hs.preimage measurable_subtype_coe)

end BorelModel

/-- A Borel-measurable subset of the manifold is chart measurable whenever open model sets
are measurable. -/
theorem _root_.MeasurableSet.isChartMeasurable [MeasurableSpace E] [OpensMeasurableSpace E]
    {s : Set M} (hs : MeasurableSet s) : IsChartMeasurable I s := by
  rw [isChartMeasurable_iff]
  intro x
  exact OpensMeasurableSpace.borel_le _ <|
    ((isOpen_extChartAt_source (I := I) x).measurableSet.inter hs).image_extChartAt
      (I := I) x Set.inter_subset_left

end TauCeti
