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

/-- A centered exponential quotient is bounded quadratically for `t ≤ 1/2`. -/
theorem exp_neg_div_one_sub_le {t : ℝ} (ht : t ≤ 1 / 2) :
    exp (-t) / (1 - t) ≤ exp (2 * t ^ 2) := by
  have hpos : 0 < 1 - t := by
    linarith
  have hlog := log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [log_inv] at hlog
  have hrem : -log (1 - t) - t ≤ t ^ 2 / (1 - t) := by
    calc
      _ ≤ (1 - t)⁻¹ - 1 - t := by linarith
      _ = _ := by field_simp; ring
  have hbound : -t - log (1 - t) ≤ 2 * t ^ 2 := by
    have hsq : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
      rw [div_le_iff₀ hpos]
      have hhalf : 0 ≤ 1 - 2 * t := by linarith
      nlinarith [mul_nonneg (sq_nonneg t) hhalf]
    linarith
  calc
    exp (-t) / (1 - t) = exp (-t - log (1 - t)) := by
      rw [exp_sub, exp_log hpos]
    _ ≤ exp (2 * t ^ 2) := exp_le_exp.mpr hbound

end Real
