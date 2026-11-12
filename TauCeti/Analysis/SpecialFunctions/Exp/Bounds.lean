/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary bounds for the real exponential

Every affine function `A x + B` is eventually smaller than `exp (a x)` when `0 < a`. For `0 < x`
the function `x / (exp x - 1)`, the generating function of the Bernoulli numbers, lies between
`exp (-x)` and `1`. With `q = exp (-x)` it is `x q / (1 - q)`, the rescaled mean of the geometric
weights `(1 - q) q ^ k`, so these bounds control geometric averages as `q ↑ 1`.

Comparing a real power `y ^ ε` with an exponential level `exp (-t)` amounts to comparing `y`
with the rescaled level `exp (-(t / ε))`.

## Main results

* `TauCeti.eventually_mul_add_lt_exp_mul`: `A x + B < exp (a x)` eventually, for `0 < a`.
* `TauCeti.exp_neg_le_div_exp_sub_one`: `exp (-x) ≤ x / (exp x - 1)` for `0 < x`.
* `TauCeti.div_exp_sub_one_le_one`: `x / (exp x - 1) ≤ 1` for `0 ≤ x`.
* `TauCeti.exp_neg_le_rpow_iff`: `exp (-t) ≤ y ^ ε ↔ exp (-(t / ε)) ≤ y` for `0 ≤ y`, `0 < ε`.
* `TauCeti.abs_exp_sub_one_le_mul_exp_abs`: `|exp t - 1| ≤ |t| exp |t|` for every real `t`.
* `TauCeti.exp_sub_one_sq_le_two_mul_sq_mul_cosh`: `(exp t - 1)² ≤ 2 t² cosh (2t)` for every real
  `t`.
-/

public section

open Filter Real

namespace TauCeti

/-- An affine function of `x` is eventually smaller than `exp (a x)` when `0 < a`. -/
theorem eventually_mul_add_lt_exp_mul {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    ∀ᶠ x in atTop, A * x + B < exp (a * x) := by
  filter_upwards [(tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_gt_atTop (|A| + |B|),
    eventually_ge_atTop 1] with x hx hx1
  rw [rpow_one, lt_div_iff₀ (by linarith)] at hx
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self A)) (by linarith : (0 : ℝ) ≤ x),
    mul_nonneg (abs_nonneg B) (by linarith : (0 : ℝ) ≤ x - 1), le_abs_self B]

/-- For `0 < x`, `exp (-x) ≤ x / (exp x - 1)`. -/
theorem exp_neg_le_div_exp_sub_one {x : ℝ} (hx : 0 < x) : exp (-x) ≤ x / (exp x - 1) := by
  rw [le_div_iff₀ (sub_pos.2 (one_lt_exp_iff.2 hx)), mul_sub, ← exp_add, neg_add_cancel,
    exp_zero, mul_one]
  linarith [add_one_le_exp (-x)]

/-- For `0 ≤ x`, `x / (exp x - 1) ≤ 1`. -/
theorem div_exp_sub_one_le_one {x : ℝ} (hx : 0 ≤ x) : x / (exp x - 1) ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [div_le_one (sub_pos.2 (one_lt_exp_iff.2 hx))]
  linarith [add_one_le_exp x]

/-- For `0 ≤ y` and `0 < ε`, the power `y ^ ε` reaches the level `exp (-t)` exactly when `y`
reaches the level `exp (-(t / ε))`. -/
theorem exp_neg_le_rpow_iff {y ε t : ℝ} (hy : 0 ≤ y) (hε : 0 < ε) :
    exp (-t) ≤ y ^ ε ↔ exp (-(t / ε)) ≤ y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [zero_rpow hε.ne', (exp_pos _).not_ge]
  rw [← le_log_iff_exp_le hy, ← le_log_iff_exp_le (rpow_pos_of_pos hy ε), log_rpow hy,
    ← neg_div, div_le_iff₀ hε, mul_comm]

/-- `|exp t - 1| ≤ |t| exp |t|` for every real `t`, a global form of the mean value inequality for
the exponential. -/
theorem abs_exp_sub_one_le_mul_exp_abs (t : ℝ) : |exp t - 1| ≤ |t| * exp |t| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (t : ℂ) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  rwa [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- `(exp t - 1)² ≤ 2 t² cosh (2t)` for every real `t`. The right-hand side is the power series
`∑ 2 · 4ⁿ t ^ (2n + 2) / (2n)!`, so this bounds `(exp t - 1)²` by a series of even powers. -/
theorem exp_sub_one_sq_le_two_mul_sq_mul_cosh (t : ℝ) :
    (exp t - 1) ^ 2 ≤ 2 * t ^ 2 * cosh (2 * t) := by
  have h1 := abs_exp_sub_one_le_mul_exp_abs t
  have h2 : exp (2 * |t|) ≤ 2 * cosh (2 * t) := by
    have h := exp_abs_le (2 * t)
    rw [abs_mul, abs_two] at h
    rw [cosh_eq]
    linarith
  calc (exp t - 1) ^ 2 = |exp t - 1| ^ 2 := (sq_abs _).symm
    _ ≤ (|t| * exp |t|) ^ 2 := by gcongr
    _ = t ^ 2 * exp (2 * |t|) := by
        rw [mul_pow, sq_abs, ← exp_nat_mul]; push_cast; ring_nf
    _ ≤ t ^ 2 * (2 * cosh (2 * t)) := by gcongr
    _ = 2 * t ^ 2 * cosh (2 * t) := by ring

end TauCeti
