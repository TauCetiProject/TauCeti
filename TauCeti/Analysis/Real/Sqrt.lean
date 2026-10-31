/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Rescaling by a square root

For `0 ≤ a`, multiplying by `(√a)⁻¹` and squaring divides the square by `a`:
`((√a)⁻¹ * x) ^ 2 = x ^ 2 / a`. This is the change of variables `x ↦ (√a)⁻¹ * x` that turns the
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`. A square factor comes out of a square root as its
absolute value: `√(x ^ 2 * y) = |x| * √y`. Doubling the argument does not decrease the square
root, with no sign hypothesis since `√x = 0` for `x ≤ 0`.

## Main results

* `Real.inv_sqrt_mul_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
* `Real.sqrt_sq_mul`: `√(x ^ 2 * y) = |x| * √y`.
* `Real.sqrt_le_sqrt_two_mul`: `√x ≤ √(2 * x)`.
-/

public section

namespace Real

/-- Multiplying by `(√a)⁻¹` and squaring divides the square by `a`. -/
@[simp]
theorem inv_sqrt_mul_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ((√a)⁻¹ * x) ^ 2 = x ^ 2 / a := by
  rw [mul_pow, inv_pow, Real.sq_sqrt ha, inv_mul_eq_div]

/-- A square factor comes out of a square root as its absolute value. -/
theorem sqrt_sq_mul (x y : ℝ) : √(x ^ 2 * y) = |x| * √y := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Doubling the argument does not decrease the square root. There is no sign hypothesis: both
sides vanish when `x ≤ 0`. -/
theorem sqrt_le_sqrt_two_mul (x : ℝ) : √x ≤ √(2 * x) := by
  rcases le_total 0 x with h | h
  · exact Real.sqrt_le_sqrt (by linarith)
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    positivity

end Real
