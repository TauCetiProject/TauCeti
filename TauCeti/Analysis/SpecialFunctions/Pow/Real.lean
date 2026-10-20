/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.

Eventually along a filter on which `x` is positive, the power `x ^ q` is `exp (q * log x)`. This is
the form in which power weights `x ^ q` are compared with exponential tilting weights.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.rpow_eventuallyEq_exp_mul_log`: `x ^ q = exp (q * log x)` eventually along a filter on
  which `x` is eventually positive.
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

/-- Along a filter on which `x` is eventually positive, `x ^ q` is eventually `exp (q * log x)`. -/
theorem rpow_eventuallyEq_exp_mul_log {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (q : ℝ) :
    (fun x => x ^ q) =ᶠ[l] fun x => exp (q * log x) :=
  hpos.mono fun _ hx => (rpow_def_of_pos hx q).trans (congrArg exp (mul_comm _ _))

end Real
