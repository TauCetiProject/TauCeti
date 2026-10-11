/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic comparisons of powers

These lemmas translate comparisons between natural-number powers of positive real numbers into
comparisons of their logarithms. The ratio forms apply when the denominator base is below `1`, so
its logarithm is negative.

## Main results

* `Real.pow_le_pow_iff_log_mul`: a power comparison as a comparison of logarithmic products.
* `Real.pow_le_pow_iff_log_ratio`: the lower ratio bound when the denominator base is below `1`.
* `Real.pow_ge_pow_iff_log_ratio`: the upper ratio bound when the denominator base is below `1`.
-/

public section

namespace Real

/-- For positive real bases, comparing natural-number powers is equivalent to comparing the
corresponding products with their logarithms. -/
theorem pow_le_pow_iff_log_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (a b : ℕ) :
    x ^ b ≤ y ^ a ↔ (b : ℝ) * Real.log x ≤ (a : ℝ) * Real.log y := by
  rw [← Real.log_le_log_iff (pow_pos hx _) (pow_pos hy _), Real.log_pow, Real.log_pow]

/-- If the denominator base is in `(0, 1)`, comparing powers is equivalent to a lower bound on
the ratio of logarithms. -/
theorem pow_le_pow_iff_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hy1 : y < 1) (a b : ℕ) (hb : 0 < b) :
    x ^ b ≤ y ^ a ↔ (a : ℝ) / b ≤ Real.log x / Real.log y := by
  rw [pow_le_pow_iff_log_mul hx hy]
  rw [le_div_iff_of_neg (Real.log_neg hy hy1), div_mul_eq_mul_div,
    le_div_iff₀ (Nat.cast_pos.mpr hb)]
  simp [mul_comm]

/-- If the denominator base is in `(0, 1)`, the reverse power comparison is equivalent to an
upper bound on the ratio of logarithms. -/
theorem pow_ge_pow_iff_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hy1 : y < 1) (a b : ℕ) (hb : 0 < b) :
    y ^ a ≤ x ^ b ↔ Real.log x / Real.log y ≤ (a : ℝ) / b := by
  rw [pow_le_pow_iff_log_mul hy hx]
  rw [le_div_iff₀ (Nat.cast_pos.mpr hb), div_mul_eq_mul_div,
    div_le_iff_of_neg (Real.log_neg hy hy1)]
  simp [mul_comm]

end Real
