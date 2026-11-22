/-
Copyright (c) 2026 Matteo Cipollina, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary bounds for the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums.

This file also records a numerical enclosure `-0.366513 ≤ log (log 2) ≤ -0.366512` for the
iterated logarithm at `2`, used to enclose the logarithmic integral at `2`.

Near `1` from below, `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`
(`Real.abs_log_le_two_mul_one_sub`), which turns exponential decay of `1 - x` into exponential
decay of `log x`, as for the modulus `|α|²` of a section tending to one.

`Real.neg_log_le_sqrt_two_div` bounds `-log x` by `sqrt (2 / x)` for every `x ≥ 0`,
including the totalized value at zero. `Real.posLog_le_sqrt_two_mul_abs` bounds
`posLog x` by `sqrt (2 * |x|)` for every real `x`.
Applied to reciprocal distances, these inequalities dominate logarithmic singularities by
inverse-square-root kernels. Their integrals control dyadic averages and the choice of circles
in Hadamard minimum-modulus estimates.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.le_log_log_two` and `Real.log_log_two_le`: `-0.366513 ≤ log (log 2) ≤ -0.366512`.
* `Real.abs_log_le_two_mul_one_sub`: `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`.
* `Real.neg_log_le_sqrt_two_div`: `-log x ≤ sqrt (2 / x)` for every nonnegative real `x`.
* `Real.posLog_le_sqrt_two_mul_abs`: `posLog x ≤ sqrt (2 * |x|)` for every real `x`.
* `Real.mul_log_natCast_div_le_log_of_pow_le_mul_pow`: a logarithmic bound from a
  cross-multiplied comparison of natural powers.
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

/-- Near `1` from below the logarithm is controlled by the distance to `1`: for `1 / 2 ≤ x ≤ 1`,
`|log x| ≤ 2 (1 - x)`. -/
theorem abs_log_le_two_mul_one_sub {x : ℝ} (hx : 1 / 2 ≤ x) (hx₁ : x ≤ 1) :
    |log x| ≤ 2 * (1 - x) := by
  have hx₀ : 0 < x := by linarith
  -- `-log x = log x⁻¹ ≤ x⁻¹ - 1 = (1 - x) / x ≤ 2 (1 - x)`.
  have h := log_le_sub_one_of_pos (inv_pos.mpr hx₀)
  rw [log_inv, inv_eq_one_div, div_sub_one hx₀.ne', le_div_iff₀ hx₀] at h
  rw [abs_of_nonpos (log_nonpos hx₀.le hx₁)]
  nlinarith

/-- The negative logarithm is bounded by an inverse-square-root majorant on the nonnegative
half-line, including its totalized value at zero. -/
theorem neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 ≤ x) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  by_cases ht : 0 ≤ -Real.log x
  · have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := by
      simpa using Real.pow_div_factorial_le_exp (-Real.log x) ht 2
    have hexp : Real.exp (-Real.log x) = x⁻¹ := by
      simp [Real.exp_neg, Real.exp_log hx]
    have hsq : (-Real.log x) ^ 2 ≤ 2 / x := by
      rw [hexp] at hmain
      rw [div_eq_mul_inv]
      nlinarith [hmain]
    exact (Real.le_sqrt ht (div_nonneg (by norm_num) hx.le)).2 hsq
  · exact (lt_of_not_ge ht).le.trans (Real.sqrt_nonneg _)

/-- The positive logarithm is bounded by a square-root majorant, including zero. -/
theorem posLog_le_sqrt_two_mul_abs (x : ℝ) : Real.posLog x ≤ Real.sqrt (2 * |x|) := by
  rw [Real.posLog_apply]
  refine max_le (Real.sqrt_nonneg _) ?_
  simpa only [Real.log_inv, neg_neg, div_inv_eq_mul, Real.log_abs] using
    (neg_log_le_sqrt_two_div (inv_nonneg.mpr (abs_nonneg x)))

/-- An upper bound on a power of a ratio of natural numbers gives a logarithmic bound
with any nonnegative coefficient at most the exponent, including when the ratio is zero. -/
theorem mul_log_natCast_div_le_log_of_pow_le_mul_pow {p q m N : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (ham : a ≤ m) (hpow : p ^ m ≤ N * q ^ m) :
    a * log ((p : ℝ) / q) ≤ log N := by
  by_cases hq : q = 0
  · simpa [hq] using log_natCast_nonneg N
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)
  by_cases h : 1 ≤ (p : ℝ) / q
  · have hratio : ((p : ℝ) / q) ^ m ≤ N := by
      rw [div_pow, div_le_iff₀ (pow_pos hq' _)]
      exact_mod_cast hpow
    calc
      _ ≤ (m : ℝ) * log ((p : ℝ) / q) := mul_le_mul_of_nonneg_right ham (log_nonneg h)
      _ = log (((p : ℝ) / q) ^ m) := (log_pow _ _).symm
      _ ≤ _ := log_le_log (pow_pos (zero_lt_one.trans_le h) _) hratio
  · exact (mul_nonpos_of_nonneg_of_nonpos ha
      (log_nonpos (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)) (le_of_not_ge h))).trans
      (log_natCast_nonneg N)

end Real
