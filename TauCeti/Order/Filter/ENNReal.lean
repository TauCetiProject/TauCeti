/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ENNReal

/-!
# Subadditivity of the upper limit in `ℝ≥0∞`

Mathlib's `ENNReal.limsup_add_le` asks the filter to be closed under countable intersections, a
hypothesis its proof uses but the statement does not need: the upper limit of a sum of
`ℝ≥0∞`-valued functions is at most the sum of their upper limits along every filter
(`ENNReal.limsup_add_le'`). Neighbourhood filters, along which difference quotients are taken, are
not closed under countable intersections.
-/

public section

open Filter
open scoped ENNReal NNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

/-- The upper limit of a sum of `ℝ≥0∞`-valued functions is at most the sum of their upper limits,
along any filter. -/
theorem limsup_add_le' (u v : α → ℝ≥0∞) : f.limsup (u + v) ≤ f.limsup u + f.limsup v := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hε2 : ((ε / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
  have hu := eventually_lt_of_limsup_lt (ENNReal.lt_add_right (lt_top_iff_ne_top.1 <|
    (le_self_add.trans_lt hlt)) hε2)
  have hv := eventually_lt_of_limsup_lt (ENNReal.lt_add_right (lt_top_iff_ne_top.1 <|
    (le_add_self.trans_lt hlt)) hε2)
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hu, hv] with a hua hva
  calc (u + v) a ≤ (f.limsup u + (ε / 2 : ℝ≥0)) + (f.limsup v + (ε / 2 : ℝ≥0)) :=
        add_le_add hua.le hva.le
    _ = f.limsup u + f.limsup v + ε := by
        rw [add_add_add_comm, ← ENNReal.coe_add, add_halves]

end ENNReal
