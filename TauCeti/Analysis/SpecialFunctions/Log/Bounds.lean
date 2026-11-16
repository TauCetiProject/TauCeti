/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary numerical bounds on the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums.

This file also records a numerical enclosure `-0.366513 ≤ log (log 2) ≤ -0.366512` for the
iterated logarithm at `2`, used to enclose the logarithmic integral at `2`.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.le_log_log_two` and `Real.log_log_two_le`: `-0.366513 ≤ log (log 2) ≤ -0.366512`.
-/

public section

namespace Real

/-- The natural logarithm of `4` is at most `2`. -/
theorem log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, log_pow]
  norm_num
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- For every nonnegative real `x`, `log x / x ≤ 1 / 2` (holding at `x = 0` via `0 / 0 = 0`). -/
theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := log_le_sub_one_of_pos (half_pos hx)
  rw [log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- Lower bound `-0.366513 ≤ log (log 2)`. -/
theorem le_log_log_two : (-0.366513 : ℝ) ≤ log (log 2) := by
  rw [le_log_iff_exp_le (log_pos one_lt_two)]
  have he := sum_le_exp_of_nonneg (x := (366513 / 1000000 : ℝ)) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at he
  norm_num at he
  have hmul : exp (-(366513 / 1000000 : ℝ)) * exp (366513 / 1000000) = 1 := by
    rw [← exp_add]; norm_num
  have hlt : exp (-(366513 / 1000000 : ℝ)) ≤ 6931471803 / 10000000000 := by nlinarith
  have hlt' : exp (-0.366513) ≤ 0.6931471803 := by norm_num at hlt ⊢; exact hlt
  exact hlt'.trans log_two_gt_d9.le

/-- Upper bound `log (log 2) ≤ -0.366512`. -/
theorem log_log_two_le : log (log 2) ≤ -0.366512 := by
  rw [log_le_iff_le_exp (log_pos one_lt_two)]
  have hb := exp_bound' (x := (22907 / 62500 : ℝ)) (by norm_num) (by norm_num)
    (n := 8) (by decide)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
  norm_num at hb
  have hmul : exp (-(22907 / 62500 : ℝ)) * exp (22907 / 62500) = 1 := by
    rw [← exp_add]; norm_num
  have hle : (6931471808 / 10000000000 : ℝ) ≤ exp (-(22907 / 62500 : ℝ)) := by
    nlinarith [exp_pos (-(22907 / 62500 : ℝ)), exp_pos (22907 / 62500 : ℝ)]
  have hle' : (0.6931471808 : ℝ) ≤ exp (-0.366512) := by norm_num at hle ⊢; exact hle
  exact log_two_lt_d9.le.trans hle'

end Real
