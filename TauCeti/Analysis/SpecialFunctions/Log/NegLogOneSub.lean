/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.

## Main results

* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `0 ≤ x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

public section

namespace Real

/-- The quadratic remainder of `-log (1 - x)` is nonnegative for `x < 1`. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -log (1 - x) - x := by
  linarith [log_le_sub_one_of_pos (sub_pos.mpr hx1)]

/-- The quadratic remainder of `-log (1 - x)` is at most `x² / (2 (1 - x))` for
`0 ≤ x < 1`. This is Mathlib's complex logarithm bound read along the reals. -/
theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hnx : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, norm_of_nonneg hx0]
  have hz : ‖(x : ℂ)‖ < 1 := by rw [hnx]; exact hx1
  -- `1 - x` is a positive real, so the whole real-to-complex passage is the single conditional
  -- rewrite `Complex.ofReal_log`; `push_cast` and `ring` absorb the remaining coercions, so the
  -- step does not depend on the order in which the casts are unfolded.
  have hcast : Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ) = ((-log (1 - x) - x : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      ← Complex.ofReal_log (inv_pos.mpr hpos).le]
    push_cast [log_inv]
    ring
  calc
    -log (1 - x) - x ≤ |(-log (1 - x) - x)| := le_abs_self _
    _ = ‖Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ)‖ := by
      rw [hcast, Complex.norm_real, norm_eq_abs]
    _ ≤ ‖(x : ℂ)‖ ^ 2 * (1 - ‖(x : ℂ)‖)⁻¹ / 2 :=
      Complex.norm_log_one_sub_inv_sub_self_le hz
    _ = x ^ 2 / (2 * (1 - x)) := by rw [hnx]; field_simp

/-- For `1 < y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is
nonnegative. -/
theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 1 < y) (hs : 0 < s) :
    0 ≤ -log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (rpow_lt_one_of_one_lt_of_neg hy (by linarith))

/-- For `2 ≤ y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is bounded by
`y ^ (-2s) / (2 (1 - 2 ^ (-s)))`. -/
theorem neg_log_one_sub_rpow_sub_le_div {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤
      y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxle : y ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    rpow_le_rpow_of_nonpos two_pos hy (by linarith)
  have h2lt : (2 : ℝ) ^ (-s) < 1 :=
    rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤
        (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (hxle.trans_lt h2lt)
    _ ≤ (y ^ (-s)) ^ 2 / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      gcongr
    _ = y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]

/-- For `2 ≤ y` and `1 ≤ s`, the quadratic remainder of `-log (1 - y ^ (-s))` is at most
`y⁻²`. -/
theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (by linarith)
    _ ≤ (y ^ (-s)) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    _ = y ^ (-(2 * s)) := by rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]
    _ ≤ y ^ (-(2 : ℝ)) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

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
