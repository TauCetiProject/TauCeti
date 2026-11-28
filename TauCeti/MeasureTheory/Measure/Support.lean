/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Topological support on discrete spaces and under sums, restriction, products, scalars and maps

This file characterizes support by singleton masses at isolated points, and identifies the support
of restriction to an open set (inside that set, and everywhere for a measure positive on nonempty
open sets), the support of a
nonzero scalar multiple of a measure, the support of a pullback along an open embedding, and the
support of a pushforward by a continuous map. It also
shows that pushing a measure forward along an inducing map with closed range, such as a closed
embedding or a homeomorphism, transports its topological support onto the image of the original
support.
Finite sums have the union of their summands' supports, and finite products have the product
of the supports of their factors. A measurable map that is
continuous at a source support point sends that point into the support of the pushforward;
global continuity is unnecessary for this inclusion.

## Main results

* `MeasureTheory.Measure.mem_support_iff_measure_singleton_pos` — at an isolated point, support
  membership is equivalent to positive singleton mass.
* `MeasureTheory.Measure.support_eq_setOf_singleton_ne_zero` — on a discrete space, the support
  consists exactly of the points with nonzero singleton mass.
* `MeasureTheory.Measure.support_smul_measure` — multiplying a measure by a nonzero scalar
  preserves its support.
* `MeasureTheory.Measure.support_restrict_of_isOpen` — restricting a measure positive on
  nonempty open sets to an open set gives support equal to that set's closure.
* `MeasureTheory.Measure.support_restrict_inter_of_isOpen` — restricting a measure to an open set
  does not change its support inside that set.
* `MeasureTheory.Measure.support_comap_of_isOpenEmbedding` — the support of a pullback along an
  open embedding is the preimage of the original support.
* `MeasureTheory.Measure.support_map_eq_closure_image` — a continuous pushforward has support
  equal to the closure of the image of the support, when the source support has full measure.
* `MeasureTheory.Measure.support_map_eq_closure_range` — a continuous image of a full-support
  measure has support equal to the closure of the map's range.
* `MeasureTheory.Measure.support_map_of_isInducing_of_isClosed_range` — the support of a
  pushforward by an inducing map with closed range, such as a closed embedding, is the image of
  the original support.
* `MeasureTheory.Measure.support_map_homeomorph` — the support of a pushforward by a homeomorphism
  is the image of the original support.
* `MeasureTheory.Measure.isProbabilityMeasure_comap_support` — in a hereditarily Lindelöf space
  with measurable open sets, pulling a probability measure back to its support gives a probability
  measure.
* `MeasureTheory.Measure.isOpenPosMeasure_comap_support` — in a hereditarily Lindelöf space with
  measurable open sets, pulling a measure back to its support yields a measure positive on nonempty
  open sets.
* `MeasureTheory.Measure.IsCompactProbabilityMeasure` — predicate for probability measures with
  compact topological support.
* `MeasureTheory.Measure.isCompact_support_map_homeomorph_iff` and
  `MeasureTheory.Measure.isCompactProbabilityMeasure_map_homeomorph_iff` — pushforward along a
  homeomorphism preserves compact support and being a compactly supported probability measure.
-/

public section

open Set Topology
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The support of a finite sum of measures is the union of their supports. -/
theorem support_finset_sum {X I : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (s : Finset I) (μ : I → Measure X) :
    (∑ i ∈ s, μ i).support = ⋃ i ∈ s, (μ i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, support_add, ih]

/-- An isolated point (one whose singleton is open), for instance any point of a discrete space,
belongs to the support exactly when its singleton has positive mass. No compatibility between the
measurable structure and topology is needed. -/
@[simp]
theorem mem_support_iff_measure_singleton_pos {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {x : X} (hx : IsOpen {x}) :
    x ∈ μ.support ↔ 0 < μ {x} := by
  rw [mem_support_iff_forall]
  exact ⟨fun h ↦ h _ (hx.mem_nhds (Set.mem_singleton x)),
    fun h _ hU ↦ h.trans_le (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))⟩

/-- On a discrete topological space, the support of a measure consists exactly of the points with
nonzero singleton mass. -/
theorem support_eq_setOf_singleton_ne_zero {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [MeasurableSpace X] (μ : Measure X) :
    μ.support = {x | μ {x} ≠ 0} :=
  Set.ext fun _ ↦
    (mem_support_iff_measure_singleton_pos (isOpen_discrete _)).trans pos_iff_ne_zero

/-- The support of a finite product of sigma-finite measures is the product of their supports.
No compatibility between the topologies and measurable structures is needed. -/
@[simp]
theorem support_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    (Measure.pi μ).support = Set.univ.pi (fun i ↦ (μ i).support) := by
  ext x
  refine ⟨fun hx i _ ↦ ?_, fun hx ↦ (mem_support_iff_forall x).2 fun U hU ↦ ?_⟩
  · -- a null neighbourhood of `x i` pulls back to a null neighbourhood of `x`
    by_contra hi
    obtain ⟨U, hU, hU0⟩ := notMem_support_iff_exists.1 hi
    exact notMem_support_iff_exists.2
      ⟨_, (continuous_apply i).continuousAt.preimage_mem_nhds hU, pi_eval_preimage_null μ hU0⟩ hx
  · -- `U` contains a box of neighbourhoods of the coordinates, which has positive mass
    rw [nhds_pi] at hU
    obtain ⟨I, _, V, hV, hsub⟩ := Filter.mem_pi.mp hU
    have hpos : 0 < Measure.pi μ (Set.univ.pi V) := by
      rw [Measure.pi_pi]
      exact pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i _ ↦
        ((mem_support_iff_forall _).1 (hx i (Set.mem_univ i)) (V i) (hV i)).ne'
    exact hpos.trans_le (measure_mono fun y hy ↦ hsub fun i _ ↦ hy i (Set.mem_univ i))

/-- A measurable map continuous at a source support point sends it into the support of the
pushforward, even if the map is discontinuous elsewhere. -/
theorem mem_support_map_of_continuousAt {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    {μ : Measure X} {f : X → Y} {x : X}
    (hf : AEMeasurable f μ) (hfx : ContinuousAt f x) (hx : x ∈ μ.support) :
    f x ∈ (μ.map f).support :=
  (mem_support_iff_forall _).2 fun U hU ↦
    ((mem_support_iff_forall x).mp hx _ (hfx hU)).trans_le (Measure.le_map_apply hf U)

/-- Multiplying a measure by a nonzero `ℝ≥0∞` scalar preserves its topological support. -/
theorem support_smul_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (c : ℝ≥0∞) (μ : Measure X) (hc : c ≠ 0) :
    (c • μ).support = μ.support :=
  smul_absolutelyContinuous.support_mono.antisymm (absolutelyContinuous_smul hc).support_mono

/-- Restricting a measure positive on nonempty open sets to an open set gives support equal
to the closure of that set. -/
@[simp]
theorem support_restrict_of_isOpen {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {s : Set X} (hs : IsOpen s) : (μ.restrict s).support = closure s := by
  refine Set.Subset.antisymm (support_restrict_subset.trans inter_subset_left) ?_
  apply closure_minimal _ isClosed_support
  simpa only [hs.interior_eq, support_eq_univ, inter_univ] using
    (interior_inter_support (μ := μ) (s := s))

/-- Restricting a measure to an open set does not change its support inside that set. -/
theorem support_restrict_inter_of_isOpen {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) {s : Set X} (hs : IsOpen s) :
    (μ.restrict s).support ∩ s = μ.support ∩ s := by
  refine subset_antisymm (fun x hx ↦ ⟨(support_restrict_subset hx.1).2, hx.2⟩)
    fun x hx ↦ ⟨interior_inter_support ⟨?_, hx.1⟩, hx.2⟩
  rw [hs.interior_eq]
  exact hx.2

/-- The support of a measure pulled back along an open embedding is the preimage of the support. -/
theorem support_comap_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : IsOpenEmbedding f) (hf' : MeasurableEmbedding f) (μ : Measure Y) :
    (μ.comap f).support = f ⁻¹' μ.support := by
  ext x
  rw [mem_preimage, mem_support_iff_forall, mem_support_iff_forall]
  constructor
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 (hf.continuous.continuousAt.preimage_mem_nhds hU)
    have := h V (hV.mem_nhds hxV)
    rw [hf'.comap_apply] at this
    exact this.trans_le (measure_mono ((image_mono hVU).trans (image_preimage_subset f U)))
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    have := h (f '' V) ((hf.isOpenMap V hV).mem_nhds (mem_image_of_mem f hxV))
    rw [← hf'.comap_apply] at this
    exact this.trans_le (measure_mono hVU)

/-- In a hereditarily Lindelöf space with measurable open sets, pulling a probability measure back
to its topological support yields a probability measure. -/
instance isProbabilityMeasure_comap_support {X : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.comap ((↑) : μ.support → X)) :=
  (MeasurableEmbedding.subtypeVal
    (Measure.isClosed_support (μ := μ)).measurableSet).isProbabilityMeasure_comap
      (by simpa using Measure.support_mem_ae (μ := μ))

/-- In a hereditarily Lindelöf space with measurable open sets, pulling a measure back to its
topological support yields a measure positive on nonempty open sets. -/
instance isOpenPosMeasure_comap_support {X : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) : (μ.comap ((↑) : μ.support → X)).IsOpenPosMeasure where
  open_pos U hU := by
    rintro ⟨x, hx⟩
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
    rw [(MeasurableEmbedding.subtypeVal
        (Measure.isClosed_support (μ := μ)).measurableSet).comap_apply,
      Subtype.image_preimage_coe, Set.inter_comm,
      measure_inter_conull (Measure.measure_compl_support (μ := μ))]
    exact ((mem_support_iff_forall (x : X)).mp x.property O (hO.mem_nhds hx)).ne'

/-- A measure on a topological measurable space is a compactly supported probability measure if it
is a probability measure and its topological support is compact. -/
abbrev IsCompactProbabilityMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The support of a continuous pushforward is the closure of the image of the support,
provided that the source support has full measure. -/
theorem support_map_eq_closure_image (μ : Measure X) (hμ : μ.support ∈ ae μ)
    {f : X → Y} (hf : Continuous f) :
    (μ.map f).support = closure (f '' μ.support) := by
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    exact (ae_map_iff hf.measurable.aemeasurable isClosed_closure.measurableSet).2 <|
      (Filter.eventually_mem_set.mpr hμ).mono fun x hx ↦ subset_closure (mem_image_of_mem f hx)
  · exact closure_minimal (image_subset_iff.2 fun x hx ↦ mem_support_map_of_continuousAt
      hf.measurable.aemeasurable hf.continuousAt hx) isClosed_support

/-- The support of the pushforward of a full-support measure by a continuous map is the closure of
the map's range. No injectivity, surjectivity, or properness hypothesis is needed. -/
theorem support_map_eq_closure_range (μ : Measure X) {f : X → Y} (hμ : μ.support = Set.univ)
    (hf : Continuous f) : (μ.map f).support = closure (Set.range f) := by
  rw [support_map_eq_closure_image μ (by simp [hμ]) hf, hμ, image_univ]

/-- An inducing map with closed range, for instance a closed embedding or a homeomorphism, carries
the support of a measure onto the support of its pushforward. Injectivity is not needed, and
neither is an assumption that the support has full measure. -/
theorem support_map_of_isInducing_of_isClosed_range (μ : Measure X) {f : X → Y}
    (hf : IsInducing f) (hr : IsClosed (range f)) :
    (μ.map f).support = f '' μ.support := by
  refine Subset.antisymm (fun y hy ↦ ?_) (image_subset_iff.2 fun x hx ↦
    mem_support_map_of_continuousAt hf.continuous.aemeasurable hf.continuous.continuousAt hx)
  -- the closed range of `f` is conull for the pushforward, so it contains the support
  obtain ⟨x, rfl⟩ := support_subset_of_isClosed hr
    (ae_map_mem_range hr.measurableSet hf.continuous.aemeasurable) hy
  -- the neighbourhoods of `x` are generated by preimages of open neighbourhoods of `f x`
  have hb := hf.nhds_eq_comap x ▸ (nhds_basis_opens (f x)).comap f
  refine ⟨x, hb.mem_measureSupport.2 fun V hV ↦ ?_, rfl⟩
  rw [← map_apply hf.continuous.measurable hV.2.measurableSet]
  exact (nhds_basis_opens (f x)).mem_measureSupport.1 hy V hV

/-- A homeomorphism carries the support of a measure onto the support of its pushforward. -/
theorem support_map_homeomorph (μ : Measure X) (e : X ≃ₜ Y) :
    (μ.map e).support = e '' μ.support :=
  support_map_of_isInducing_of_isClosed_range μ e.isInducing e.isClosedEmbedding.isClosed_range

/-- Pushing a measure forward along a homeomorphism preserves compactness of its topological
support. -/
@[simp]
theorem isCompact_support_map_homeomorph_iff (μ : Measure X) (e : X ≃ₜ Y) :
    IsCompact (μ.map e).support ↔ IsCompact μ.support := by
  rw [support_map_homeomorph, e.isCompact_image]

/-- Pushing a measure forward along a homeomorphism preserves being a compactly supported
probability measure. -/
@[simp]
theorem isCompactProbabilityMeasure_map_homeomorph_iff (μ : Measure X) (e : X ≃ₜ Y) :
    (μ.map e).IsCompactProbabilityMeasure ↔ μ.IsCompactProbabilityMeasure := by
  simp [IsCompactProbabilityMeasure, Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable]

/-- Casting a natural-valued law to the reals casts its support: the cast is a closed embedding,
so no new real limit points appear. -/
theorem support_map_natCast (μ : Measure ℕ) :
    (μ.map (Nat.cast : ℕ → ℝ)).support = (Nat.cast : ℕ → ℝ) '' μ.support :=
  support_map_of_isInducing_of_isClosed_range μ Nat.isClosedEmbedding_coe_real.isInducing
    Nat.isClosedEmbedding_coe_real.isClosed_range

end MeasureTheory.Measure
