/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Counting measure and `Set.ncard`

Basic cardinality identities relating `MeasureTheory.Measure.count` to `Set.ncard` without requiring
`[DecidableEq]`.

## Main results

* `MeasureTheory.Measure.count_apply_eq_ncard`: on a measurable space with measurable singletons,
  the counting measure of a finite set `s : Set X` equals `(s.ncard : ℝ≥0∞)`.
-/

public section

namespace MeasureTheory.Measure

/-- Counting measure of any finite set `s : Set X` with measurable singletons equals `s.ncard`. -/
theorem count_apply_eq_ncard {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {s : Set X} (hs : s.Finite) : count s = s.ncard := by
  rw [count_apply_finite s hs, Set.ncard_eq_toFinset_card s hs]

end MeasureTheory.Measure
