/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Borel measurability and proper pushforwards

For an inducing map `f : α → β` between Borel spaces, the Borel σ-algebra of `α` is the
pullback of the Borel σ-algebra of `β` along `f`. Hence a map `g` into `α` is measurable exactly
when `f ∘ g` is. Unlike `MeasurableEmbedding.measurable_comp_iff`, this needs no measurability
of the range of `f`: a topological embedding with non-measurable range still detects
measurability of maps into its domain.

Pushforward along a proper map preserves finiteness on compact sets. In particular,
proper embeddings and translations can transport locally finite measures.

A local homeomorphism out of a Lindelöf space maps measurable sets to measurable sets: the image
is a countable union of images under open embeddings of chart domains.

## Main results

* `Topology.IsInducing.comap_borel`
* `Topology.IsInducing.measurable_comp_iff`
* `IsLocalHomeomorph.measurableSet_image`
* `MeasureTheory.Measure.isFiniteMeasureOnCompacts_map_of_isProperMap`
-/

public section

open MeasureTheory Topology

/-- The Borel σ-algebra of the domain of an inducing map is the pullback of the Borel σ-algebra
of its codomain. -/
theorem Topology.IsInducing.comap_borel {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsInducing f) : (borel β).comap f = borel α := by
  rw [← borel_comap, hf.eq_induced]

/-- For an inducing map `f` between Borel spaces, a map `g` into the domain of `f` is measurable
exactly when `f ∘ g` is. -/
theorem Topology.IsInducing.measurable_comp_iff {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [MeasurableSpace γ] {f : α → β} (hf : IsInducing f) {g : γ → α} :
    Measurable (f ∘ g) ↔ Measurable g := by
  rw [measurable_iff_comap_le, measurable_iff_comap_le, ← MeasurableSpace.comap_comp,
    BorelSpace.measurable_eq (α := α), BorelSpace.measurable_eq (α := β), hf.comap_borel]

/-- A local homeomorphism out of a Lindelöf space maps measurable sets to measurable sets. -/
theorem IsLocalHomeomorph.measurableSet_image {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [LindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] {f : α → β} (hf : IsLocalHomeomorph f) {s : Set α}
    (hs : MeasurableSet s) : MeasurableSet (f '' s) := by
  choose e he hfe using hf
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x ↦ (e x).source)
    fun x ↦ (e x).open_source.mem_nhds (he x)
  rw [← Set.inter_univ s, ← hcover, Set.inter_iUnion₂, Set.image_iUnion₂]
  refine .biUnion ht fun x _ ↦ ?_
  -- On the source of `e x`, the map `f` is the open embedding `(e x).source.domRestrict (e x)`.
  rw [hfe x, ← Set.image_domRestrict]
  exact (e x).isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (measurable_subtype_coe hs)

namespace MeasureTheory.Measure

/-- A proper continuous pushforward preserves finiteness on compact sets. -/
theorem isFiniteMeasureOnCompacts_map_of_isProperMap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [T2Space Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → Y} (hf : IsProperMap f) :
    IsFiniteMeasureOnCompacts (μ.map f) where
  lt_top_of_isCompact K hK := by
    by_cases hfm : AEMeasurable f μ
    · rw [Measure.map_apply_of_aemeasurable hfm hK.measurableSet]
      exact (hf.isCompact_preimage hK).measure_lt_top
    · by_cases hμ : μ = 0
      · simp [hμ]
      · rw [Measure.map_of_not_aemeasurable_of_ne_zero hfm hμ]
        exact @measure_lt_top _ _ _ isFiniteMeasure_dirac _

end MeasureTheory.Measure
