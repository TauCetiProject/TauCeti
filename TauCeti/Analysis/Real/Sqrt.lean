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
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`.

## Main results

* `Real.inv_sqrt_mul_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
-/

public section

namespace Real

/-- Multiplying by `(√a)⁻¹` and squaring divides the square by `a`. -/
@[simp]
theorem inv_sqrt_mul_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ((√a)⁻¹ * x) ^ 2 = x ^ 2 / a := by
  rw [mul_pow, inv_pow, Real.sq_sqrt ha, inv_mul_eq_div]

end Real
