/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex expressions with real coefficients

The imaginary part of a complex affine expression with real coefficients factors
as a real coefficient times the imaginary part of its argument. This reduces imaginary-part
estimates at division points to real inequalities.

For real `t`, the complex number `1 + t ^ 2` is nonzero (`Complex.one_add_ofReal_sq_ne_zero`), as
needed to clear the denominator of kernels such as `t / (1 + t ^ 2)`.

Even natural powers of `I` simplify via `Complex.I_pow_two_mul`: `I ^ (2 * k) = (-1 : ℂ) ^ k`, and
the imaginary part of `I ^ n * w` is given by `Complex.im_I_pow_two_mul_mul` (even `n`) and
`Complex.im_I_pow_two_mul_add_one_mul` (odd `n`).
-/

public section

namespace Complex

/-- The imaginary part of `(a z + b) / d - c z` is `(a / d - c) Im z` for real `a b d c`. -/
lemma im_ofReal_mul_add_ofReal_div_sub_ofReal_mul (a b d c : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / d - c * z).im = (a / d - c) * z.im := by
  simp only [sub_im, div_ofReal_im, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  ring

/-- For real `t`, the complex number `1 + t ^ 2` is nonzero. -/
theorem one_add_ofReal_sq_ne_zero (t : ℝ) : 1 + (t : ℂ) ^ 2 ≠ 0 := by
  exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)

/-- Even natural powers of `I` satisfy `I ^ (2 * k) = (-1 : ℂ) ^ k`. -/
@[simp]
theorem I_pow_two_mul (k : ℕ) : I ^ (2 * k) = (-1 : ℂ) ^ k := by
  rw [pow_mul, I_sq]

/-- The imaginary part of `I ^ (2 * k) * w` is `(-1 : ℝ) ^ k * w.im`. -/
theorem im_I_pow_two_mul_mul (k : ℕ) (w : ℂ) :
    (I ^ (2 * k) * w).im = (-1 : ℝ) ^ k * w.im := by
  rw [I_pow_two_mul k, ← ofReal_one, ← ofReal_neg, ← ofReal_pow, mul_im,
    ofReal_re, ofReal_im, zero_mul, add_zero]

/-- The imaginary part of `I ^ (2 * k + 1) * w` is `(-1 : ℝ) ^ k * w.re`. -/
theorem im_I_pow_two_mul_add_one_mul (k : ℕ) (w : ℂ) :
    (I ^ (2 * k + 1) * w).im = (-1 : ℝ) ^ k * w.re := by
  rw [pow_succ, I_pow_two_mul k, ← ofReal_one, ← ofReal_neg, ← ofReal_pow,
    mul_assoc, mul_im, ofReal_re, ofReal_im, I_mul_im, I_mul_re]
  ring

end Complex
