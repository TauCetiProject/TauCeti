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
* `Real.logb_zpow_self`: `logb b (b ^ n) = n` for `n : ℤ` and a base `b > 0`, `b ≠ 1`.
* `Real.le_natFloor_logb_iff_pow_le`: `n ≤ ⌊logb b x⌋₊ ↔ b ^ n ≤ x` for `1 < b` and `1 ≤ x`.
* `Real.pow_natFloor_logb_le_self`: `b ^ ⌊logb b x⌋₊ ≤ x` for `1 < b` and `1 ≤ x`.
* `Real.lt_pow_natFloor_logb_add_one`: `x < b ^ (⌊logb b x⌋₊ + 1)` for `1 < b` and `0 < x`.
* `Real.natFloor_logb_eq_natLog_natFloor`: `⌊logb b x⌋₊ = Nat.log b ⌊x⌋₊` for `b : ℕ` and
  `0 ≤ x`.
* `Real.natLog_natFloor_exp`: `Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊` for `b : ℕ` and `t : ℝ`.
-/

public section

namespace Real

variable {b x : ℝ} {m n : ℕ}

/-- A nontrivial positive base `b` has `logb b (b ^ n) = n` for an integer `n`. -/
@[simp]
theorem logb_zpow_self (b_pos : 0 < b) (b_ne_one : b ≠ 1) (n : ℤ) : logb b (b ^ n) = n := by
  rw [← rpow_intCast, logb_rpow b_pos b_ne_one]

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

/-- For `b > 1` and `x ≥ 1`, the floor `⌊logb b x⌋₊` is the largest natural number `n` with
`b ^ n ≤ x`. -/
theorem le_natFloor_logb_iff_pow_le (hb : 1 < b) (hx : 1 ≤ x) (n : ℕ) :
    n ≤ ⌊logb b x⌋₊ ↔ b ^ n ≤ x := by
  rw [Nat.le_floor_iff (logb_nonneg hb hx), le_logb_iff_rpow_le hb (zero_lt_one.trans_le hx),
    rpow_natCast]

/-- For `b > 1` and `x ≥ 1`, the power of `b` at the natural floor of `logb b x` is at most
`x`. -/
theorem pow_natFloor_logb_le_self (hb : 1 < b) (hx : 1 ≤ x) : b ^ ⌊logb b x⌋₊ ≤ x := by
  simpa only [rpow_natCast] using
    (le_logb_iff_rpow_le hb (zero_lt_one.trans_le hx)).mp (Nat.floor_le (logb_nonneg hb hx))

/-- For `b > 1` and `0 < x`, `x` is less than the power of `b` one past the natural floor of
`logb b x`. -/
theorem lt_pow_natFloor_logb_add_one (hb : 1 < b) (hx : 0 < x) :
    x < b ^ (⌊logb b x⌋₊ + 1) := by
  rw [← rpow_natCast]
  apply (logb_lt_iff_lt_rpow hb hx).mp
  push_cast
  exact Nat.lt_floor_add_one (logb b x)

/-- For a natural base `b` and `0 ≤ x`, the natural floor of `logb b x` equals `Nat.log b ⌊x⌋₊`.
This extends `Real.natFloor_logb_natCast` from natural numbers to nonnegative reals. -/
theorem natFloor_logb_eq_natLog_natFloor (b : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ⌊logb b x⌋₊ = Nat.log b ⌊x⌋₊ := by
  rw [← Int.floor_toNat, floor_logb_natCast hx]
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [Int.log_of_one_le_right b hx1, Int.toNat_natCast]
  · rw [Int.log_of_right_le_one b hx1.le, Int.toNat_of_nonpos (by simp),
      Nat.floor_eq_zero.mpr hx1, Nat.log_zero_right]

/-- For a natural base `b` and any real `t`, `Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊`. -/
theorem natLog_natFloor_exp (b : ℕ) (t : ℝ) : Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊ := by
  rw [← natFloor_logb_eq_natLog_natFloor b (exp_nonneg t), logb, log_exp]

end Real
