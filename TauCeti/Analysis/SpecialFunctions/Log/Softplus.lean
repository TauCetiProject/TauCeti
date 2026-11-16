/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential-sum reformulation of the softplus epigraph

The scalar softplus epigraph inequality `log (1 + exp x) ≤ t` is equivalent to the shifted
exponential-sum bound `exp (x - t) + exp (-t) ≤ 1`. Multiplying `1 + exp x ≤ exp t` by the
positive factor `exp (-t)` gives an equivalent convex inequality in two exponential terms, which
directly feeds the two-cone representation of softplus and its positive-scale perspective.

## Main results

* `Real.log_one_add_exp_le_iff`: `log (1 + exp x) ≤ t ↔ exp (x - t) + exp (-t) ≤ 1`.
-/

public section

namespace Real

/-- The softplus epigraph inequality `log (1 + exp x) ≤ t` is equivalent to the shifted
exponential-sum bound `exp (x - t) + exp (-t) ≤ 1`. -/
theorem log_one_add_exp_le_iff {x t : ℝ} :
    log (1 + exp x) ≤ t ↔ exp (x - t) + exp (-t) ≤ 1 := by
  rw [log_le_iff_le_exp (add_pos zero_lt_one (exp_pos x))]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (exp_nonneg (-t))
    rw [add_mul, one_mul, ← exp_add, ← exp_add, add_neg_cancel, exp_zero, ← sub_eq_add_neg,
      add_comm] at hmul
    exact hmul
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (exp_nonneg t)
    rw [add_mul, one_mul, ← exp_add, ← exp_add, sub_add_cancel, neg_add_cancel, exp_zero,
      add_comm] at hmul
    exact hmul

end Real
