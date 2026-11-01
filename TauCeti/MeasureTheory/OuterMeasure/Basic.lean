/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Proportions of sets in outer measure

The proportion `μ (s ∩ t) / μ t` of a set `s` in a set `t` is at most one. This uses only
monotonicity, so it is stated for `OuterMeasureClass`, which covers both outer measures and
measures without requiring a measurable space.

## Main results

* `MeasureTheory.measure_inter_div_le_one`
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F}

/-- The proportion `μ (s ∩ t) / μ t` of a set `s` in a set `t` is at most one. -/
theorem measure_inter_div_le_one (s t : Set α) : μ (s ∩ t) / μ t ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

end MeasureTheory
