/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Imaginary parts of complex affine expressions

The imaginary part of a complex affine expression with real coefficients factors
as a real coefficient times the imaginary part of its argument. This reduces imaginary-part
estimates at division points to real inequalities.
-/

public section

namespace Complex

/-- The imaginary part of `(a z + b) / d - c z` is `(a / d - c) Im z` for real `a b d c`. -/
lemma im_ofReal_mul_add_ofReal_div_sub_ofReal_mul (a b d c : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / d - c * z).im = (a / d - c) * z.im := by
  simp only [sub_im, div_ofReal_im, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  ring

end Complex
