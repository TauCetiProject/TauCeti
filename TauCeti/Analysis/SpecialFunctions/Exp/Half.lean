/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Products of real exponentials at half arguments

Mathlib records `Real.exp_half : exp (x / 2) = √(exp x)`, but not the product forms of the
half-argument identities that arise when computing with the diagonal matrix
`!![exp (r / 2), 0; 0, exp (-(r / 2))]`, or with the exponential time change `e^{-t/2} X (e^t - 1)`
and its inverse `√(1 + s) Y (log (1 + s))`. This file supplies them, together with the fact that
the time `e^t - 1` of a nonnegative `t` survives the round trip through `ℝ≥0`.

## Main declarations

* `Real.exp_half_mul_exp_half`, `Real.exp_neg_half_mul_exp_neg_half`,
  `Real.exp_half_mul_exp_neg_half`: the products of `exp (± r / 2)`.
* `Real.exp_neg_half_mul_exp`: `exp (-(r / 2)) * exp r = exp (r / 2)`.
* `Real.sqrt_mul_exp_neg_half_log`: `√x * exp (-(log x / 2)) = 1` for `0 < x`.
* `Real.coe_toNNReal_exp_sub_one`: `((exp u - 1).toNNReal : ℝ) = exp u - 1` for `0 ≤ u`.
-/

public section

namespace Real

/-- `exp (r / 2) * exp (r / 2) = exp r`. -/
theorem exp_half_mul_exp_half (r : ℝ) : exp (r / 2) * exp (r / 2) = exp r := by
  rw [← exp_add, add_halves]

/-- `exp (-(r / 2)) * exp (-(r / 2)) = exp (-r)`. -/
theorem exp_neg_half_mul_exp_neg_half (r : ℝ) :
    exp (-(r / 2)) * exp (-(r / 2)) = exp (-r) := by
  rw [← exp_add, ← neg_add, add_halves]

/-- `exp (r / 2) * exp (-(r / 2)) = 1`. -/
theorem exp_half_mul_exp_neg_half (r : ℝ) : exp (r / 2) * exp (-(r / 2)) = 1 := by
  rw [← exp_add, add_neg_cancel, exp_zero]

/-- `exp (-(r / 2)) * exp r = exp (r / 2)`. -/
theorem exp_neg_half_mul_exp (r : ℝ) : exp (-(r / 2)) * exp r = exp (r / 2) := by
  rw [← exp_add, neg_add_eq_sub, sub_half]

/-- `√x * exp (-(log x / 2)) = 1` for `0 < x`: the half-exponent `exp (log x / 2)` is `√x`. -/
theorem sqrt_mul_exp_neg_half_log {x : ℝ} (hx : 0 < x) : √x * exp (-(log x / 2)) = 1 := by
  rw [exp_neg, exp_half, exp_log hx, mul_inv_cancel₀ (sqrt_pos.2 hx).ne']

/-- The exponential time `e^u - 1` of a nonnegative `u` is nonnegative, so it survives the round
trip through `ℝ≥0`. -/
theorem coe_toNNReal_exp_sub_one {u : ℝ} (hu : 0 ≤ u) :
    ((exp u - 1).toNNReal : ℝ) = exp u - 1 :=
  coe_toNNReal _ (sub_nonneg.2 (one_le_exp hu))

end Real
