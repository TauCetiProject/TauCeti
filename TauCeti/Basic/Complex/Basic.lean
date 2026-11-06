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

The imaginary part of a complex affine expression with natural and integer coefficients factors
as a real coefficient times the imaginary part of its argument. This reduces imaginary-part
estimates at division points to real inequalities.
-/

public section

namespace Complex

/-- The imaginary part of `(b₀ z + b₁) / M - m z` is `(b₀ / M - m) Im z`. -/
lemma im_div_natCast_sub_intCast_mul (b₀ b₁ M : ℕ) (m : ℤ) (z : ℂ) :
    ((b₀ * z + b₁) / M - m * z).im = ((b₀ : ℝ) / M - m) * z.im := by
  simp only [sub_im, div_natCast_im, add_im, mul_im, natCast_re, natCast_im,
    intCast_re, intCast_im, zero_mul, add_zero]
  ring

end Complex
