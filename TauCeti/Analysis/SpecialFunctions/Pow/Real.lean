/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square roots as real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.

The square root of a natural power of a nonnegative real is the real power with half the exponent:
`√(x ^ n) = x ^ (n / 2)`. This is the form in which a determinant `det (c • G) = c ^ n det G` of
an `n × n` matrix contributes to a volume density `√(det G)`.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.sqrt_pow_eq_rpow`: `√(x ^ n) = x ^ (n / 2)` for `0 ≤ x`.
-/

public section

namespace Real

/-- The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`, for
every real `x`. -/
theorem inv_sqrt_eq_rpow (x : ℝ) : (√x)⁻¹ = x ^ (-2⁻¹ : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [sqrt_eq_rpow, rpow_neg hx, one_div]
  · rw [sqrt_eq_zero'.mpr hx.le, inv_zero, rpow_def_of_neg hx, neg_mul, cos_neg, inv_mul_eq_div,
      cos_pi_div_two, mul_zero]

/-- The square root of a natural power of a nonnegative real is the real power with half the
exponent: `√(x ^ n) = x ^ (n / 2)`. -/
theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hx, mul_one_div]

end Real
