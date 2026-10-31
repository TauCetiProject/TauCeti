/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Coordinate overlaps, measurability, precompact chart neighborhoods and transported charts

Mathlib's extended chart at a point is a `PartialEquiv` between a manifold and its model vector
space. Its restrictions to the chart source and target are mutually continuous, hence the chart
restricted to its source is a measurable embedding for Borel measurable spaces. This is the
form used to transport measures between a manifold and coordinates.

Before choosing a measurable structure on the manifold, chart measurability expresses
measurability in each preferred chart. When the chart space `H` is locally compact, compact sets
admit finite open chart covers whose coordinate images lie in compact subsets of the chart targets,
even without Hausdorffness.

Coordinate changes transport images of subsets of chart overlaps and are injective there,
without differentiability assumptions; for a boundaryless model, their domains are open. On an
open subset, extended charts are restrictions of the ambient ones, so near a chart point the
inverse charts of nested open subsets differ only by the inclusion. Over `ℝ`, every chart point has
a convex neighbourhood within the model range, inside the chart target, on which flat calculus
applies even when the manifold has boundary.

For a boundaryless model `I`, a chart `c` read in the model vector space and then moved by a
homeomorphism `Ψ` is again a chart, `OpenPartialHomeomorph.extendTrans`. When the charts lie in the
maximal atlas and `Ψ` is smooth with smooth inverse, the transition maps between such charts are
smooth.

## Main results

* `TauCeti.comp_extChartAt_symm_comp_extChartAt_eventuallyEq`: a chart representative
  composed with its chart agrees locally with the original function.
* `TauCeti.measurableEmbedding_extChartAt_restrict`: an extended chart restricted to its source is
  a measurable embedding.
* `MeasurableSet.image_extChartAt`: the image of a measurable subset of a chart source is
  measurable in the model space.
* `TauCeti.IsChartMeasurable`: chartwise measurability without a measurable structure on the
  manifold.
* `TauCeti.IsChartMeasurable.measurableSet_inter_preimage`: measurable parameter pieces for maps
  continuous only on their measurable domain.
* `TauCeti.exists_finite_precompact_chart_cover`: finite open chart covers with compact
  coordinate bounds for compact subsets of manifolds modelled on a locally compact space.
* `TauCeti.exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt`: a convex neighbourhood of the
  chart point within the model range, inside the chart target, with unique derivatives and
  interior accumulating at the chart point.
* `OpenPartialHomeomorph.extendTrans` and `OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`:
  charts read in the model vector space and moved by a homeomorphism, and their smooth transition
  maps.
-/

public section

open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Near the center of an extended chart, composing a chart representative with the chart
recovers the original function. No continuity of the function is needed. -/
theorem comp_extChartAt_symm_comp_extChartAt_eventuallyEq {α : Type*} (f : M → α) (x : M) :
    (f ∘ (extChartAt I x).symm) ∘ extChartAt I x =ᶠ[𝓝 x] f := by
  filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
  exact congrArg f ((extChartAt I x).left_inv hy)

/-- Changing extended coordinates transports the coordinate image of a subset of the overlap
onto its image in the second chart. No differentiability assumption is needed. -/
theorem extChartAt_coordChange_image (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source) :
    ((extChartAt I α).symm ≫ extChartAt I β) '' ((extChartAt I α) '' s) =
      (extChartAt I β) '' s := by
  simp only [Set.image_image]
  apply Set.image_congr
  intro x hx
  exact congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)

/-- Extended coordinate changes are injective on the coordinate image of any subset of the
chart overlap. No differentiability assumption is needed. -/
theorem injOn_extChartAt_coordChange (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source) :
    Set.InjOn ((extChartAt I α).symm ≫ extChartAt I β) ((extChartAt I α) '' s) := by
  apply ((extChartAt I α).symm ≫ extChartAt I β).injOn.mono
  rintro _ ⟨x, hx, rfl⟩
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
    Set.mem_preimage, (extChartAt I α).left_inv (hsub hx).1]
  exact ⟨(extChartAt I α).map_source (hsub hx).1, (hsub hx).2⟩

omit [ChartedSpace H M] in
/-- For a boundaryless model, the domain of the change of coordinates between two charts is
open. -/
theorem _root_.ModelWithCorners.isOpen_extendCoordChange_source [I.Boundaryless]
    {e e' : OpenPartialHomeomorph M H} : IsOpen (I.extendCoordChange e e').source :=
  (e.continuousOn_extend_symm (I := I)).isOpen_inter_preimage e.isOpen_extend_target
    e'.isOpen_extend_source

/-- The extended chart of an open subset at a point sends that point to the same coordinates as
the extended chart of a larger open subset at its image under the inclusion. -/
theorem extChartAt_inclusion_self {U V : TopologicalSpace.Opens M} (h : U ≤ V) (x : U) :
    extChartAt I (TopologicalSpace.Opens.inclusion h x) (TopologicalSpace.Opens.inclusion h x) =
      extChartAt I x x := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq]

/-- Near the chart image of a point of an open subset, the inverse extended chart of a larger
open subset is the inclusion composed with the inverse extended chart of the smaller one. -/
theorem extChartAt_inclusion_symm_eventuallyEq {U V : TopologicalSpace.Opens M} (h : U ≤ V)
    (x : U) :
    (extChartAt I (TopologicalSpace.Opens.inclusion h x)).symm =ᶠ[nhds (extChartAt I x x)]
      TopologicalSpace.Opens.inclusion h ∘ (extChartAt I x).symm := by
  have hc : Filter.Tendsto I.symm (nhds (extChartAt I x x))
      (nhds (chartAt H (TopologicalSpace.Opens.inclusion h x) (Set.inclusion h x))) := by
    simpa [extChartAt, TopologicalSpace.Opens.chartAt_eq] using
      I.continuous_symm.tendsto (extChartAt I x x)
  exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq h).comp_tendsto hc

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

/-- Chart measurability in the defining target-intersection form, without unfolding
the predicate. -/
theorem isChartMeasurable_def [MeasurableSpace E] (s : Set M) :
    IsChartMeasurable I s ↔
      ∀ x : M, MeasurableSet ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
  Iff.rfl

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

/-- Pulling a chart-measurable subset of one chart back along a map continuous on a
measurable parameter domain gives a measurable subset of that domain. No measurable structure on
the manifold or continuity outside the parameter domain is required. The parameter space only needs
open sets to be measurable. -/
theorem IsChartMeasurable.measurableSet_inter_preimage [MeasurableSpace E] [BorelSpace E]
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Q : X → M} {D : Set X} {s : Set M} (hs : IsChartMeasurable I s) (hQ : ContinuousOn Q D)
    (hD : MeasurableSet D) (α : M) (hsource : s ⊆ (extChartAt I α).source) :
    MeasurableSet (D ∩ Q ⁻¹' s) := by
  classical
  let q : D → M := fun x ↦ Q x
  have hq : Continuous q := continuousOn_iff_continuous_domRestrict.mp hQ
  let U := q ⁻¹' (extChartAt I α).source
  let Ψ := extChartAt I α ∘ q
  have hU : IsOpen U := (isOpen_extChartAt_source α).preimage hq
  have hΨ : ContinuousOn Ψ U :=
    (continuousOn_extChartAt α).comp hq.continuousOn (fun _ hx ↦ hx)
  have hm : Measurable (U.piecewise Ψ (fun _ ↦ 0)) :=
    hΨ.measurable_piecewise continuousOn_const hU.measurableSet
  have heq : Set.EqOn (U.piecewise Ψ (fun _ ↦ 0)) Ψ U :=
    fun _ hx ↦ Set.piecewise_eq_of_mem U _ _ hx
  have he : U ∩ (U.piecewise Ψ (fun _ ↦ 0)) ⁻¹' ((extChartAt I α) '' s) = q ⁻¹' s := by
    rw [heq.inter_preimage_eq]
    simpa only [U, Ψ, Set.preimage_comp, Set.preimage_inter, Set.inter_comm] using
      congrArg (Set.preimage q) ((extChartAt I α).injOn.preimage_image_inter hsource)
  have hpre : MeasurableSet (q ⁻¹' s) := by
    rw [← he]
    exact hU.measurableSet.inter ((hs.image_extChartAt α hsource).preimage hm)
  rw [← Subtype.image_preimage_coe D (Q ⁻¹' s)]
  exact hD.subtype_image hpre

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

/-- In a zero-dimensional charted manifold every preferred chart source is a singleton. -/
theorem extChartAt_source_zeroDim {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Subsingleton E] [TopologicalSpace M] [ChartedSpace E M] (x : M) :
    (extChartAt 𝓘(ℝ, E) x).source = {x} := by
  ext y
  constructor
  · intro hy
    exact (extChartAt 𝓘(ℝ, E) x).injOn hy (mem_extChartAt_source x)
      (Subsingleton.elim _ _)
  · rintro rfl
    exact mem_extChartAt_source y


/-- A neighbourhood of the chart point within the model range on which flat arguments in a
chart apply: it lies in the chart target, is convex with unique derivatives, and its interior
accumulates at the chart point. It is the intersection of a small ball with `range I`, so it
need not be open when `M` has boundary or corners. -/
theorem exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (x₀ : M) :
    ∃ s : Set E, s ⊆ (extChartAt I x₀).target ∧ UniqueDiffOn ℝ s ∧ Convex ℝ s ∧
      s ∈ 𝓝[Set.range I] extChartAt I x₀ x₀ ∧ extChartAt I x₀ x₀ ∈ s ∧
      extChartAt I x₀ x₀ ∈ closure (interior s) := by
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, Metric.ball (extChartAt I x₀ x₀) ε ∩ Set.range I ⊆
      (extChartAt I x₀).target :=
    Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin x₀)
  have hx : extChartAt I x₀ x₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)
  refine ⟨Metric.ball (extChartAt I x₀ x₀) ε ∩ Set.range I, hsub, ?_,
    (convex_ball _ _).inter I.convex_range, ?_, ⟨Metric.mem_ball_self hε, hx⟩, ?_⟩
  · rw [Set.inter_comm]
    exact I.uniqueDiffOn.inter Metric.isOpen_ball
  · rw [Set.inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  · rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact Metric.isOpen_ball.inter_closure
      ⟨Metric.mem_ball_self hε, I.range_subset_closure_interior hx⟩

end TauCeti

open scoped ContDiff

namespace OpenPartialHomeomorph

section ExtendTrans

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [TopologicalSpace H]
  [TopologicalSpace M]

/-- A chart `c` of `M`, read in the vector space `E` of a boundaryless model `I` and then moved to
`F` by a homeomorphism `Ψ`. Its coordinates are `Ψ ∘ c.extend I`. -/
noncomputable def extendTrans (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] (Ψ : E ≃ₜ F) : OpenPartialHomeomorph M F :=
  (c.trans I.toHomeomorph.toOpenPartialHomeomorph).trans Ψ.toOpenPartialHomeomorph

variable (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (Ψ : E ≃ₜ F)

/-- The source of `c.extendTrans I Ψ` is the source of `c`. -/
@[simp]
theorem extendTrans_source : (c.extendTrans I Ψ).source = c.source := by
  simp [extendTrans, mfld_simps]

/-- The target of `c.extendTrans I Ψ` is the target of `c`, read in `E` and moved by `Ψ`. -/
@[simp]
theorem extendTrans_target :
    (c.extendTrans I Ψ).target = Ψ.symm ⁻¹' (I.symm ⁻¹' c.target) := by
  ext v
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The chart `c.extendTrans I Ψ` reads a point through `c`, then `I`, then `Ψ`. -/
@[simp]
theorem extendTrans_apply (w : M) : c.extendTrans I Ψ w = Ψ (I (c w)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_apply]

/-- The inverse of `c.extendTrans I Ψ` is the inverse of `Ψ`, then of `I`, then of `c`. -/
@[simp]
theorem extendTrans_symm_apply (v : F) :
    (c.extendTrans I Ψ).symm v = c.symm (I.symm (Ψ.symm v)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The transition map between two charts `c.extendTrans I Ψ` is `C^m` when `c` runs over the
maximal atlas of `M` and `Ψ` over homeomorphisms that are `C^m` with `C^m` inverses. -/
theorem contDiffOn_extendTrans_comp_symm [NormedSpace 𝕜 F] [ChartedSpace H M] {m : ℕ∞ω}
    {c₁ c₂ : OpenPartialHomeomorph M H} (hc₁ : c₁ ∈ IsManifold.maximalAtlas I m M)
    (hc₂ : c₂ ∈ IsManifold.maximalAtlas I m M) {Ψ₁ Ψ₂ : E ≃ₜ F}
    (hΨ₁ : ContDiff 𝕜 m Ψ₁.symm) (hΨ₂ : ContDiff 𝕜 m Ψ₂) :
    ContDiffOn 𝕜 m (c₂.extendTrans I Ψ₂ ∘ (c₁.extendTrans I Ψ₁).symm)
      ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source := by
  have hmaps : Set.MapsTo Ψ₁.symm ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source
      (I.extendCoordChange c₁ c₂).source := by
    intro v hv
    simp only [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply] at hv ⊢
    exact ⟨⟨by simp [I.range_eq_univ], hv.1⟩, hv.2⟩
  refine (hΨ₂.comp_contDiffOn ((I.contDiffOn_extendCoordChange hc₁ hc₂).comp
    hΨ₁.contDiffOn hmaps)).congr fun v _ ↦ ?_
  simp [mfld_simps]

end ExtendTrans

end OpenPartialHomeomorph
