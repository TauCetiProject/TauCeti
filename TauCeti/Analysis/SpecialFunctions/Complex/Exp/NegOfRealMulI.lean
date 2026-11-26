/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The complex exponential `exp (−(x i))` of a negative real multiple of `i`

Mathlib computes the real part, imaginary part and norm of `exp (x i)` for real `x`
(`Complex.exp_ofReal_mul_I_re`, `Complex.exp_ofReal_mul_I_im`, `Complex.norm_exp_ofReal_mul_I`).
The simp normal form of `exp ((−x) i)` is `exp (−(x i))`, which those lemmas do not match. This
file records the same three facts for `exp (−(x i))`, as simp lemmas.

## Main results

* `Complex.exp_neg_ofReal_mul_I`: `exp (−(x i)) = exp ((−x) i)`, with `−x` real.
* `Complex.exp_neg_ofReal_mul_I_re`: `re (exp (−(x i))) = cos x`.
* `Complex.exp_neg_ofReal_mul_I_im`: `im (exp (−(x i))) = −sin x`.
* `Complex.norm_exp_neg_ofReal_mul_I`: `‖exp (−(x i))‖ = 1`.
-/

public section

namespace Complex

/-- `exp (−(x i)) = exp ((−x) i)`, with the negation taken in `ℝ`. -/
theorem exp_neg_ofReal_mul_I (x : ℝ) : exp (-(x * I)) = exp ((-x : ℝ) * I) := by
  rw [ofReal_neg, neg_mul]

/-- The real part of `exp (−(x i))` is `cos x`. -/
@[simp]
theorem exp_neg_ofReal_mul_I_re (x : ℝ) : (exp (-(x * I))).re = Real.cos x := by
  rw [exp_neg_ofReal_mul_I, exp_ofReal_mul_I_re, Real.cos_neg]

/-- The imaginary part of `exp (−(x i))` is `−sin x`. -/
@[simp]
theorem exp_neg_ofReal_mul_I_im (x : ℝ) : (exp (-(x * I))).im = -Real.sin x := by
  rw [exp_neg_ofReal_mul_I, exp_ofReal_mul_I_im, Real.sin_neg]

/-- `exp (−(x i))` has norm `1`. -/
@[simp]
theorem norm_exp_neg_ofReal_mul_I (x : ℝ) : ‖exp (-(x * I))‖ = 1 := by
  rw [exp_neg_ofReal_mul_I, norm_exp_ofReal_mul_I]

end Complex
