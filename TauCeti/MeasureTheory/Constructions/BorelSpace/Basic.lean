/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
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

## Main results

* `Topology.IsInducing.comap_borel`
* `Topology.IsInducing.measurable_comp_iff`
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

namespace MeasureTheory.Measure

/-- A proper continuous pushforward preserves finiteness on compact sets. -/
theorem isFiniteMeasureOnCompacts_map_of_isProperMap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → Y} (hf : IsProperMap f) :
    IsFiniteMeasureOnCompacts (μ.map f) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top

end MeasureTheory.Measure
