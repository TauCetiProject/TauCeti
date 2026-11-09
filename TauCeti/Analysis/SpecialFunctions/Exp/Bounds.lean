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

end TauCeti
