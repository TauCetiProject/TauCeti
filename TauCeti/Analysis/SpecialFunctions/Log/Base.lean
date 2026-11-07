/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Comparisons of powers and logarithms

For a base `b ∈ (0, 1)`, a positive real `x` and natural numbers `m` and `n` with `0 < n`, the
comparison of `x ^ n` with `b ^ m` is a comparison of `Real.logb b x` with the ratio `m / n`. The
inequalities reverse because `Real.logb b` is antitone for such a base. In the same way, the
integer floor `⌊logb b x⌋` is the largest integer `n` with `x ≤ b ^ n`.

For a base greater than one, the natural floor of the logarithm locates a real number at least
one between two consecutive powers. These intervals support dyadic decompositions and
convergence estimates.

## Main results

* `Real.pow_le_pow_iff_div_le_logb_of_base_lt_one`: `x ^ n ≤ b ^ m ↔ m / n ≤ logb b x`.
* `Real.pow_le_pow_iff_logb_le_div_of_base_lt_one`: `b ^ m ≤ x ^ n ↔ logb b x ≤ m / n`.
* `Real.le_floor_logb_iff_zpow_le_of_base_lt_one`: `n ≤ ⌊logb b x⌋ ↔ x ≤ b ^ n` for `n : ℤ`.
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

/-- For a base `b ∈ (0, 1)` and `0 < x`, the floor `⌊logb b x⌋` is the largest integer `n` with
`x ≤ b ^ n`. -/
theorem le_floor_logb_iff_zpow_le_of_base_lt_one (b_pos : 0 < b) (b_lt_one : b < 1)
    (hx : 0 < x) (n : ℤ) : n ≤ ⌊logb b x⌋ ↔ x ≤ b ^ n := by
  rw [Int.le_floor, le_logb_iff_rpow_le_of_base_lt_one b_pos b_lt_one hx, rpow_intCast]

/-- For `b > 1` and `x ≥ 1`, the natural floor of `logb b x` locates `x` between two
consecutive natural powers of `b`. -/
theorem pow_nat_floor_logb_bounds (hb : 1 < b) (hx : 1 ≤ x) :
    b ^ ⌊logb b x⌋₊ ≤ x ∧ x < b ^ (⌊logb b x⌋₊ + 1) := by
  have h0 : 0 < x := zero_lt_one.trans_le hx
  have hl : 0 ≤ logb b x := logb_nonneg hb hx
  constructor
  · simpa only [rpow_natCast] using
      (le_logb_iff_rpow_le hb h0).mp (Nat.floor_le hl)
  · rw [← rpow_natCast]
    apply (logb_lt_iff_lt_rpow hb h0).mp
    push_cast
    exact Nat.lt_floor_add_one (logb b x)

end Real
