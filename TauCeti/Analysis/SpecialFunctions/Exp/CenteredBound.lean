/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

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
  have hcast : -Complex.log (1 - (t : ℂ)) - (t : ℂ) =
      ((-log (1 - t) - t : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hpos.le]
    push_cast
    ring
  have hlog := Complex.norm_neg_log_one_sub_sub_le (z := (t : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using ht)
  rw [hcast, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
    at hlog
  have hbound : -t - log (1 - t) ≤ 2 * t ^ 2 := by
    have := le_abs_self (-log (1 - t) - t)
    nlinarith [sq_nonneg t]
  calc
    exp (-t) / (1 - t) = exp (-t - log (1 - t)) := by
      rw [exp_sub, exp_log hpos]
    _ ≤ exp (2 * t ^ 2) := exp_le_exp.mpr hbound

end Real
