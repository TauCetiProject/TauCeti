/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Exp.Half

/-!
# Decimal bounds on the constants of the standard Gaussian density

The standard Gaussian density `φ(t) = (2π)^{-1/2} e^{-t²/2}` has `φ(0) = (2π)^{-1/2}` and
`φ(1) = (2π)^{-1/2} e^{-1/2}`. This file bounds `(2π)^{-1/2}` and `e^{-1/2}` to eight decimal
places, in the style of Mathlib's `Real.pi_gt_d20` and `Real.exp_neg_one_gt_d9`. Both are bounded
through their squares `(2π)⁻¹` and `e^{-1}`, from those Mathlib bounds on `π` and on `e^{-1}`.

## Main results

* `Real.inv_sqrt_two_mul_pi_gt_d8`, `Real.inv_sqrt_two_mul_pi_lt_d8`:
  `0.39894228 < (√(2π))⁻¹ < 0.39894229`.
* `Real.exp_neg_half_gt_d8`, `Real.exp_neg_half_lt_d8`: `0.60653065 < e^{-1/2} < 0.60653067`.
-/

public section

namespace Real

private theorem inv_sqrt_two_mul_pi_sq : (√(2 * π))⁻¹ ^ 2 = (2 * π)⁻¹ := by
  rw [inv_pow, sq_sqrt (by positivity)]

/-- `(2π)^{-1/2}` is greater than `0.39894228`. -/
theorem inv_sqrt_two_mul_pi_gt_d8 : 0.39894228 < (√(2 * π))⁻¹ := by
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [inv_sqrt_two_mul_pi_sq, lt_inv_comm₀ (by norm_num) (by positivity)]
  nlinarith [pi_lt_d20]

/-- `(2π)^{-1/2}` is less than `0.39894229`. -/
theorem inv_sqrt_two_mul_pi_lt_d8 : (√(2 * π))⁻¹ < 0.39894229 := by
  refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
  rw [inv_sqrt_two_mul_pi_sq, inv_lt_comm₀ (by positivity) (by norm_num)]
  nlinarith [pi_gt_d20]

/-- `e^{-1/2}` is greater than `0.60653065`. -/
theorem exp_neg_half_gt_d8 : 0.60653065 < exp (-(1 / 2)) := by
  refine lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le ?_
  rw [sq (exp _), exp_neg_half_mul_exp_neg_half]
  linarith [exp_neg_one_gt_d9]

/-- `e^{-1/2}` is less than `0.60653067`. -/
theorem exp_neg_half_lt_d8 : exp (-(1 / 2)) < 0.60653067 := by
  refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
  rw [sq (exp _), exp_neg_half_mul_exp_neg_half]
  linarith [exp_neg_one_lt_d9]

end Real
