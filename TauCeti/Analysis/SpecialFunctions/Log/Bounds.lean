/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary numerical bounds on the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2`, `x / 2`, and
`η * x`, one obtains `log 4 = 2 log 2 ≤ 2`, `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`), and the scaled tangent-line bound `log x ≤ η * x - log η - 1` for every
`x > 0` and slope `η > 0`. The first compares explicit prime-counting constants involving `log 4`
with rational constants, the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums, and the third bounds
logarithmic growth linearly with arbitrarily small slope `η`.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.log_le_mul_sub_log_sub_one`: `log x ≤ η * x - log η - 1` for `x > 0` and `η > 0`.
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

/-- For `x > 0` and any positive slope `η > 0`, `log x ≤ η * x - log η - 1`. This is the
tangent-line inequality `log (η * x) ≤ η * x - 1` rearranged for `log x`. -/
theorem log_le_mul_sub_log_sub_one {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    log x ≤ η * x - log η - 1 := by
  have h := log_le_sub_one_of_pos (mul_pos hη hx)
  rw [log_mul hη.ne' hx.ne'] at h
  linarith

end Real
