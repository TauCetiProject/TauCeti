/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# σ-finiteness of restrictions to σ-compact sets

A measure that is finite on compact sets is σ-finite on a σ-compact space
(`MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts`). This file records the relative
version: such a measure has σ-finite restriction to every σ-compact set, even when the measure
itself is not σ-finite. For instance, a Haar measure on a locally compact group that is not
σ-compact is not σ-finite, but its restriction to a σ-compact open subgroup is, so Fubini's
theorem applies there. No separation or measurability assumptions on the space are needed:
compact sets are replaced by their measurable envelopes.

## Main results

* `IsSigmaCompact.sigmaFinite_restrict`: a measure that is finite on compact sets has σ-finite
  restriction to every σ-compact set.
-/

public section

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

/-- A measure that is finite on compact sets has σ-finite restriction to every σ-compact set. -/
theorem IsSigmaCompact.sigmaFinite_restrict [IsFiniteMeasureOnCompacts μ] {s : Set α}
    (hs : IsSigmaCompact s) : SigmaFinite (μ.restrict s) := by
  obtain ⟨K, hK, rfl⟩ := hs
  -- Compact sets need not be measurable, so cover by their measurable envelopes `T n`.
  set T := fun n ↦ toMeasurable μ (K n)
  have hKT : ⋃ n, K n ⊆ ⋃ n, T n := iUnion_mono fun n ↦ subset_toMeasurable μ (K n)
  -- The sets `T n ∪ (⋃ n, T n)ᶜ` cover the space, and each has finite measure for the
  -- restriction, since its trace on `⋃ n, K n` lies in `T n`.
  refine ⟨⟨⟨fun n ↦ T n ∪ (⋃ n, T n)ᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · have hmeas : MeasurableSet (T n ∪ (⋃ n, T n)ᶜ) :=
      (measurableSet_toMeasurable μ _).union (MeasurableSet.iUnion fun n ↦
        measurableSet_toMeasurable μ _).compl
    rw [Measure.restrict_apply hmeas, union_inter_distrib_right,
      (disjoint_compl_left.mono_right hKT).inter_eq, union_empty]
    exact (measure_mono inter_subset_left).trans_lt
      ((measure_toMeasurable (K n)).trans_lt (hK n).measure_lt_top)
  · rw [← iUnion_union, union_compl_self]
