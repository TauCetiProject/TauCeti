/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Power comparisons as bounds on `Real.logb` for a base below one

For a base `b ∈ (0, 1)`, a positive real `x` and natural numbers `m` and `n` with `0 < n`, the
comparison of `x ^ n` with `b ^ m` is a comparison of `Real.logb b x` with the ratio `m / n`. The
inequalities reverse because `Real.logb b` is antitone for such a base.

## Main results

* `Real.pow_le_pow_iff_div_le_logb_of_base_lt_one`: `x ^ n ≤ b ^ m ↔ m / n ≤ logb b x`.
* `Real.pow_le_pow_iff_logb_le_div_of_base_lt_one`: `b ^ m ≤ x ^ n ↔ logb b x ≤ m / n`.
-/

public section

namespace Real

variable {b x : ℝ} {m n : ℕ}

/-- For a base `b ∈ (0, 1)` and `0 < x`, the power comparison `x ^ n ≤ b ^ m` is the lower bound
`m / n ≤ logb b x`. -/
theorem pow_le_pow_iff_div_le_logb_of_base_lt_one (b_pos : 0 < b) (b_lt_one : b < 1)
    (hx : 0 < x) (hn : 0 < n) : x ^ n ≤ b ^ m ↔ (m : ℝ) / n ≤ logb b x := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hn), mul_comm, ← logb_pow,
    le_logb_iff_rpow_le_of_base_lt_one b_pos b_lt_one (pow_pos hx n), rpow_natCast]

/-- For a base `b ∈ (0, 1)` and `0 < x`, the power comparison `b ^ m ≤ x ^ n` is the upper bound
`logb b x ≤ m / n`. -/
theorem pow_le_pow_iff_logb_le_div_of_base_lt_one (b_pos : 0 < b) (b_lt_one : b < 1)
    (hx : 0 < x) (hn : 0 < n) : b ^ m ≤ x ^ n ↔ logb b x ≤ (m : ℝ) / n := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr hn), mul_comm, ← logb_pow,
    logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one (pow_pos hx n), rpow_natCast]

end Real
