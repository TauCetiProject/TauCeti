/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# Products of real exponentials at half arguments

Mathlib records `Real.exp_half : exp (x / 2) = √(exp x)`, but not the product forms of the
half-argument identities that arise when computing with the diagonal matrix
`!![exp (r / 2), 0; 0, exp (-(r / 2))]`. This file supplies them.

## Main declarations

* `Real.exp_half_mul_exp_half`, `Real.exp_neg_half_mul_exp_neg_half`,
  `Real.exp_half_mul_exp_neg_half`: the products of `exp (± r / 2)`.
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

end Real
