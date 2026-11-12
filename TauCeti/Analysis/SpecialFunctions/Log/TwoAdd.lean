/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lower bounds for the growth scale `(1 + r) log (2 + r)`

For `r ≥ 0`, both `log (2 + r)` and `(1 + r) log (2 + r)` are at least `1 / 2`. These lower
bounds let a constant be absorbed into a multiple of the scale `(1 + r) log (2 + r)` that
measures order-one growth of entire functions.

## Main results

* `Real.one_half_le_log_two_add`: `1 / 2 ≤ log (2 + r)` for `0 ≤ r`.
* `Real.one_half_le_one_add_mul_log_two_add`: `1 / 2 ≤ (1 + r) * log (2 + r)` for `0 ≤ r`.
-/

public section

namespace Real

/-- For nonnegative `r`, the logarithm `log (2 + r)` is at least `1 / 2`. -/
theorem one_half_le_log_two_add {r : ℝ} (hr : 0 ≤ r) : (1 / 2 : ℝ) ≤ log (2 + r) := by
  have h2 : (1 / 2 : ℝ) ≤ log 2 := by
    convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  exact h2.trans (log_le_log (by norm_num) (by linarith))

/-- For nonnegative `r`, the growth scale `(1 + r) * log (2 + r)` is at least `1 / 2`. -/
theorem one_half_le_one_add_mul_log_two_add {r : ℝ} (hr : 0 ≤ r) :
    (1 / 2 : ℝ) ≤ (1 + r) * log (2 + r) := by
  have hL := one_half_le_log_two_add hr
  nlinarith

end Real
