/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.

A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`, which turns a degree
bound with a real factor `δ` into a bound by an `r`-th power.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.pow_le_rpow_pow_of_le_mul`: `b ^ n ≤ (b ^ δ) ^ r` when `1 ≤ b` and `n ≤ δ r`.
-/

public section

namespace Real

/-- The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`, for
every real `x`. -/
theorem inv_sqrt_eq_rpow (x : ℝ) : (√x)⁻¹ = x ^ (-2⁻¹ : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [sqrt_eq_rpow, rpow_neg hx, one_div]
  · rw [sqrt_eq_zero'.mpr hx.le, inv_zero, rpow_def_of_neg hx, neg_mul, cos_neg, inv_mul_eq_div,
      cos_pi_div_two, mul_zero]

/-- A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`. This converts a
degree bound `n ≤ δ r` with a real factor `δ` into a bound by an `r`-th power. -/
theorem pow_le_rpow_pow_of_le_mul {b δ : ℝ} (hb : 1 ≤ b) {n r : ℕ} (hn : (n : ℝ) ≤ δ * r) :
    b ^ n ≤ (b ^ δ) ^ r := by
  rw [← rpow_mul_natCast (by linarith), ← rpow_natCast]
  exact rpow_le_rpow_of_exponent_le hb hn

end Real
