/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability through an inducing map, and pushforwards along proper maps

For an inducing map `f : α → β` between Borel spaces, the Borel σ-algebra of `α` is the
pullback of the Borel σ-algebra of `β` along `f`. Hence a map `g` into `α` is measurable exactly
when `f ∘ g` is. Unlike `MeasurableEmbedding.measurable_comp_iff`, this needs no measurability
of the range of `f`: a topological embedding with non-measurable range still detects
measurability of maps into its domain.

Pushing a measure that is finite on compact sets forward along a proper map, such as a closed
embedding, gives a measure that is finite on compact sets, because the preimage of a compact set is
compact. This generalizes Mathlib's `MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map` from
homeomorphisms to proper maps.

## Main results

* `Topology.IsInducing.comap_borel`
* `Topology.IsInducing.measurable_comp_iff`
* `IsProperMap.isFiniteMeasureOnCompacts_map`
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
  have hα : ‹MeasurableSpace α› = MeasurableSpace.comap f ‹MeasurableSpace β› := by
    rw [BorelSpace.measurable_eq (α := α), BorelSpace.measurable_eq (α := β), hf.comap_borel]
  rw [measurable_iff_comap_le, measurable_iff_comap_le, hα, MeasurableSpace.comap_comp]

/-- Pushing a measure that is finite on compact sets forward along a proper map gives a measure
that is finite on compact sets. -/
theorem IsProperMap.isFiniteMeasureOnCompacts_map {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] [T2Space β] {f : α → β} (hf : IsProperMap f) (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ.map f) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top
