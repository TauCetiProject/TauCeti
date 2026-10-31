/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# σ-finiteness of restrictions to σ-compact sets

A measure that is finite on compact sets is σ-finite on a σ-compact space
(`MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts`). This file records the relative
version: on a Hausdorff space with measurable open sets, such a measure has σ-finite restriction to
every σ-compact set, even when the measure itself is not σ-finite. For instance, a Haar measure on
a locally compact group that is not σ-compact is not σ-finite, but its restriction to a σ-compact
open subgroup is, so Fubini's theorem applies there.

## Main results

* `IsSigmaCompact.sigmaFinite_restrict`: a measure that is finite on compact sets has σ-finite
  restriction to every σ-compact set.
-/

public section

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [T2Space α] {μ : Measure α}

/-- A measure that is finite on compact sets has σ-finite restriction to every σ-compact set. -/
theorem IsSigmaCompact.sigmaFinite_restrict [IsFiniteMeasureOnCompacts μ] {s : Set α}
    (hs : IsSigmaCompact s) : SigmaFinite (μ.restrict s) := by
  obtain ⟨K, hK, rfl⟩ := hs
  have hmeas : MeasurableSet (⋃ n, K n) := .iUnion fun n ↦ (hK n).measurableSet
  -- The sets `K n ∪ sᶜ` cover the space, and each has finite measure for `μ.restrict s`.
  refine ⟨⟨⟨fun n ↦ K n ∪ (⋃ n, K n)ᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply' hmeas, union_inter_distrib_right, compl_inter_self, union_empty]
    exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
  · rw [← iUnion_union, union_compl_self]
