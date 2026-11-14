/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A centered exponential bound

A quadratic upper bound for `exp (-t) / (1 - t)` near zero.
-/

public section

namespace Real

/-- A centered exponential quotient is bounded quadratically near zero. -/
theorem exp_neg_div_one_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    exp (-t) / (1 - t) ≤ exp (2 * t ^ 2) := by
  have hpos : 0 < 1 - t := by
    have := (abs_le.mp ht).2
    linarith
  have hlog := abs_log_sub_add_sum_range_le (ht.trans_lt (by norm_num)) 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one] at hlog
  have hden : 0 < 1 - |t| := by linarith
  have hdiv : |t| ^ 2 / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hden]
    rw [sq_abs]
    nlinarith [sq_nonneg t]
  have hbound : -t - log (1 - t) ≤ 2 * t ^ 2 := by
    have := neg_le_of_abs_le hlog
    linarith
  calc
    exp (-t) / (1 - t) = exp (-t - log (1 - t)) := by
      rw [exp_sub, exp_log hpos]
    _ ≤ exp (2 * t ^ 2) := exp_le_exp.mpr hbound

end Real
