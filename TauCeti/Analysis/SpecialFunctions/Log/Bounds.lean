/-
Copyright (c) 2026 Matteo Cipollina, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary bounds for the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums. From `e² < (3 / 2) ^ 5`
(Mathlib's `Real.exp_one_lt_d9`) one obtains `log (3 / 2) > 2 / 5`
(`Real.two_fifths_lt_log_three_halves`), which locates the zero of the unoffset logarithmic
integral below `3 / 2`.

Near `1` from below, `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`
(`Real.abs_log_le_two_mul_one_sub`), which turns exponential decay of `1 - x` into exponential
decay of `log x`, as for the modulus `|α|²` of a section tending to one.

`Real.neg_log_le_sqrt_two_div` bounds `-log x` by `sqrt (2 / x)` for every `x ≥ 0`,
including the totalized value at zero. `Real.posLog_le_sqrt_two_mul_abs` bounds
`posLog x` by `sqrt (2 * |x|)` for every real `x`.
Applied to reciprocal distances, these inequalities dominate logarithmic singularities by
inverse-square-root kernels. Their integrals control dyadic averages and the choice of circles
in Hadamard minimum-modulus estimates.

`Real.sq_log_mul_exp_one_le_sixteen_mul_sqrt` squares `e y ≤ exp y` (`Real.exp_one_mul_le_exp`)
at `y = log x / 4`: since `L² e^{−L/2}` peaks at `L = 4` with value `16 / e²`, the square of the
logarithm is at most `16 √x / e²` for `x ≥ 1`. This bounds the prime powers that are not primes
in explicit prime-counting estimates.

In the other direction, a small logarithm bounds a power from above: if `log z ≤ L` and
`n L ≤ ε` with `0 ≤ ε ≤ 1 / 2`, then `z^n ≤ 1 + 2 ε` for every real `z`
(`TauCeti.pow_le_one_add_two_mul_of_log_le`), since `z^n ≤ |z^n| ≤ exp (n log z)`
(`Real.abs_rpow_le_exp_log_mul`) and `exp ε ≤ 1 / (1 - ε) ≤ 1 + 2 ε`. This bounds the powers
`ζ(s)^n` of a zeta function whose logarithm is bounded by an exponentially decaying function of
`s`.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.two_fifths_lt_log_three_halves`: `2 / 5 < log (3 / 2)`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.abs_log_le_two_mul_one_sub`: `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`.
* `Real.neg_log_le_sqrt_two_div`: `-log x ≤ sqrt (2 / x)` for every nonnegative real `x`.
* `Real.posLog_le_sqrt_two_mul_abs`: `posLog x ≤ sqrt (2 * |x|)` for every real `x`.
* `Real.sq_log_mul_exp_one_le_sixteen_mul_sqrt`: `(log x · e)² ≤ 16 √x` for `x ≥ 1`.
* `Real.mul_log_natCast_div_le_log_of_pow_le_mul_pow`: a logarithmic bound from a
  cross-multiplied comparison of natural powers.
* `TauCeti.pow_le_one_add_two_mul_of_log_le`: `z^n ≤ 1 + 2 ε` when `log z ≤ L`, `n L ≤ ε` and
  `0 ≤ ε ≤ 1 / 2`.
* `Real.log_sub_one_div_le_log`: `log a - 1 / m ≤ log m` for `0 ≤ m` and `0 ≤ a ≤ m + 1`.
-/

public section

namespace Real

/-- The natural logarithm of `4` is at most `2`. -/
theorem log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, log_pow]
  norm_num
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- `2 / 5 < log (3 / 2)`, from `e² < (3 / 2) ^ 5` and `e < 2.7182818286`. -/
theorem two_fifths_lt_log_three_halves : (2 / 5 : ℝ) < log (3 / 2) := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  refine (pow_lt_pow_iff_left₀ (exp_pos _).le (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).1 ?_
  rw [← exp_natCast_mul, show ((5 : ℕ) : ℝ) * (2 / 5) = (2 : ℕ) * 1 by norm_num, exp_natCast_mul]
  have h := exp_one_lt_d9
  have h0 := (exp_pos 1).le
  nlinarith

/-- For every nonnegative real `x`, `log x / x ≤ 1 / 2` (holding at `x = 0` via `0 / 0 = 0`). -/
theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := log_le_sub_one_of_pos (half_pos hx)
  rw [log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith [log_le_sub_one_of_pos zero_lt_two]

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

/-- For `x ≥ 1`, `(log x · e)² ≤ 16 √x`: the maximum of `L² e^{−L/2}` is `16/e²`, at `L = 4`. -/
theorem sq_log_mul_exp_one_le_sixteen_mul_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (log x * exp 1) ^ 2 ≤ 16 * √x := by
  have hsqrt : √x = exp (log x / 4) ^ 2 := by
    rw [sqrt_eq_iff_mul_self_eq_of_pos (by positivity), ← pow_add, ← exp_natCast_mul,
      show ((2 + 2 : ℕ) : ℝ) * (log x / 4) = log x by push_cast; ring, exp_log (by linarith)]
  have h := pow_le_pow_left₀ (by have := log_nonneg hx; positivity)
    (exp_one_mul_le_exp (x := log x / 4)) 2
  rw [hsqrt]
  nlinarith

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

/-- The logarithm grows by at most `1 / m` over a step of length one: for `0 ≤ m` and
`0 ≤ a ≤ m + 1`, `log a - 1 / m ≤ log m`. At `m = 0` this reads `log a ≤ 0`. -/
theorem log_sub_one_div_le_log {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (h : a ≤ m + 1) :
    log a - 1 / m ≤ log m := by
  rcases hm.eq_or_lt with rfl | hm
  · simpa using log_nonpos ha (by linarith)
  rcases ha.eq_or_lt with rfl | ha
  · have h1 := one_sub_inv_le_log_of_pos hm
    rw [log_zero, one_div]
    linarith [inv_pos.2 hm]
  have h1 := log_le_sub_one_of_pos (div_pos ha hm)
  rw [log_div ha.ne' hm.ne'] at h1
  have h2 : a / m - 1 ≤ 1 / m := by
    rw [div_sub_one hm.ne', div_le_div_iff_of_pos_right hm]
    linarith
  linarith

end Real

namespace TauCeti

open Real

/-- **A power with a small logarithm is at most `1 + 2 ε`.** For every real `z`, if `log z ≤ L`
and `n L ≤ ε` with `0 ≤ ε ≤ 1 / 2`, then `z^n ≤ 1 + 2 ε`. -/
theorem pow_le_one_add_two_mul_of_log_le {z L ε : ℝ} {n : ℕ} (hzL : log z ≤ L) (hL : n * L ≤ ε)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) : z ^ n ≤ 1 + 2 * ε := by
  have h := abs_rpow_le_exp_log_mul z n
  rw [rpow_natCast, mul_comm] at h
  -- `z ^ n ≤ |z ^ n| ≤ exp (n log z) ≤ exp ε ≤ 1 / (1 - ε) ≤ 1 + 2 ε`.
  calc z ^ n ≤ exp (n * log z) := (le_abs_self _).trans h
    _ ≤ exp ε := exp_le_exp.2 ((mul_le_mul_of_nonneg_left hzL (Nat.cast_nonneg n)).trans hL)
    _ ≤ 1 / (1 - ε) := exp_bound_div_one_sub_of_interval hε0 (by linarith)
    _ ≤ 1 + 2 * ε := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]

end TauCeti
