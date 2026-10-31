/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# σ-finiteness of a measure finite on compacts on a σ-compact set

A measure that is finite on compact sets need not be σ-finite, for instance a Haar measure on a
group that is not σ-compact. Its restriction to a σ-compact set is σ-finite, since that set is
covered by countably many compact sets of finite measure.

## Main results

* `IsSigmaCompact.sigmaFinite_restrict`
-/

public section

open Set

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [T2Space α] {s : Set α}

/-- The restriction of a measure that is finite on compact sets to a σ-compact set is
σ-finite. -/
theorem IsSigmaCompact.sigmaFinite_restrict (hs : IsSigmaCompact s) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] : MeasureTheory.SigmaFinite (μ.restrict s) := by
  have hsm := hs.measurableSet
  obtain ⟨K, hK, hKs⟩ := hs
  -- `α` is covered by the compact sets `K n` together with the null set `sᶜ`.
  refine MeasureTheory.Measure.sigmaFinite_of_countable (S := insert sᶜ (range K))
    ((countable_range K).insert _) ?_ ?_
  · rintro _ (rfl | ⟨n, rfl⟩)
    · simp [MeasureTheory.Measure.restrict_apply' hsm]
    · exact (MeasureTheory.Measure.restrict_apply_le _ _).trans_lt (hK n).measure_lt_top
  · rw [sUnion_insert, sUnion_range, hKs, compl_union_self]
