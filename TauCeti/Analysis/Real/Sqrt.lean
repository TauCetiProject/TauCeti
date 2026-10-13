/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Elementary estimates for the real square root

For `0 ≤ a`, multiplying by `(√a)⁻¹` and squaring divides the square by `a`:
`((√a)⁻¹ * x) ^ 2 = x ^ 2 / a`. This is the change of variables `x ↦ (√a)⁻¹ * x` that turns the
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`.

The quotient `r / √(1 + r ^ 2)` is always less than `1`. It is the sine of the angle whose
tangent is `r`, and appears for instance as the gap between a subspace and a graph subspace over
it.

## Main results

* `Real.inv_sqrt_mul_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
* `Real.div_sqrt_one_add_sq_lt_one`: `r / √(1 + r ^ 2) < 1`.
-/

public section

namespace Real

/-- Multiplying by `(√a)⁻¹` and squaring divides the square by `a`. -/
@[simp]
theorem inv_sqrt_mul_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ((√a)⁻¹ * x) ^ 2 = x ^ 2 / a := by
  rw [mul_pow, inv_pow, Real.sq_sqrt ha, inv_mul_eq_div]

/-- The quotient `r / √(1 + r ^ 2)` is always less than `1`. -/
theorem div_sqrt_one_add_sq_lt_one (r : ℝ) : r / √(1 + r ^ 2) < 1 :=
  (div_lt_one (Real.sqrt_pos.2 (by positivity))).2 <| (le_abs_self r).trans_lt <|
    (Real.lt_sqrt (abs_nonneg r)).2 (by rw [sq_abs]; linarith)

end Real
