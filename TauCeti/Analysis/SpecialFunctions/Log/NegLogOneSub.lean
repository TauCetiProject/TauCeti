/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary bounds on `-log (1 - x)`

For a real `x < 1`, the quantity `-log (1 - x)` is at least `x`; for `0 ≤ x ≤ 1/2`
it is also at most `x + 2 x ^ 2`. These are the two sides of the comparison of the logarithm of an
Euler factor `(1 - x)⁻¹` with its local ratio `x`.

## Main results

* `Real.le_neg_log_one_sub`: `x ≤ -log (1 - x)` for `x < 1`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: `-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.
-/

public section

namespace Real

/-- For `x < 1`, `x ≤ -log (1 - x)`. -/
theorem le_neg_log_one_sub {x : ℝ} (hx1 : x < 1) : x ≤ -log (1 - x) := by
  have h : 0 < 1 - x := by linarith
  linarith [log_le_sub_one_of_pos h]

/-- For `0 ≤ x ≤ 1/2`, `-log (1 - x) ≤ x + 2 x ^ 2`. -/
theorem neg_log_one_sub_le_add_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -log (1 - x) ≤ x + 2 * x ^ 2 := by
  -- The first-order Taylor estimate `|x + log (1 - x)| ≤ x ^ 2 / (1 - x)`.
  have h := abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    abs_of_nonneg hx0] at h
  have h' : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  linarith [(abs_le.mp h).1]

end Real
