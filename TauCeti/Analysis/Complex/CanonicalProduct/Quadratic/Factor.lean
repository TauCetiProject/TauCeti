/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Algebraic normal form of paired quadratic factors

This lightweight module provides the algebraic rewrite for paired quadratic canonical-product
factors `1 + z ^ 2 / (y : ℂ) ^ 2 = 1 + ((y⁻¹ ^ 2 : ℝ) : ℂ) * z ^ 2` (valid for all `y : ℝ`,
including `y = 0` under totalized division), shared between the convergence development in
`TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic` and the finite polynomial API in
`TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Polynomial`.

## Main results

* `TauCeti.one_add_div_sq_eq_one_add_inv_sq_mul`: algebraic normal form of the paired quadratic
  factor.
-/

public section

namespace TauCeti

/-- Under totalized division, `1 + z ^ 2 / (y : ℂ) ^ 2` equals `1 + ((y⁻¹ ^ 2 : ℝ) : ℂ) * z ^ 2`
for every `y : ℝ` (including `y = 0`). -/
theorem one_add_div_sq_eq_one_add_inv_sq_mul (y : ℝ) (z : ℂ) :
    1 + z ^ 2 / (y : ℂ) ^ 2 = 1 + (((y⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2 := by
  push_cast
  rw [div_eq_inv_mul, inv_pow, mul_comm]

end TauCeti
