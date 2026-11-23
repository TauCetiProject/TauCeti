/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Squared norm formulas for `1 + exp z`

This file records the real-imaginary decomposition of `1 + exp z` (`Complex.one_add_exp_eq`) and
its squared modulus in trigonometric and hyperbolic-trigonometric forms
(`Complex.normSq_one_add_exp`, `Complex.normSq_one_add_exp_eq_two_mul_cosh_add_cos`).
-/

public section

namespace Complex

/-- Real and imaginary parts of `1 + exp z`. -/
theorem one_add_exp_eq (z : ℂ) :
    1 + exp z = ((1 + Real.exp z.re * Real.cos z.im : ℝ) : ℂ) +
      ((Real.exp z.re * Real.sin z.im : ℝ) : ℂ) * I := by
  conv_lhs => rw [← re_add_im z, exp_add_mul_I, ← ofReal_exp, ← ofReal_cos, ← ofReal_sin]
  push_cast; ring

/-- Squared modulus of `1 + exp z` in terms of `exp z.re`, `cos z.im`, and `sin z.im`. -/
theorem normSq_one_add_exp (z : ℂ) :
    normSq (1 + exp z) = (Real.exp z.re + Real.cos z.im) ^ 2 + Real.sin z.im ^ 2 := by
  rw [one_add_exp_eq, normSq_add_mul_I, mul_pow, Real.sin_sq]; ring

/-- Hyperbolic-trigonometric formula `‖1 + exp z‖² = 2 exp (re z) (cosh (re z) + cos (im z))`. -/
theorem normSq_one_add_exp_eq_two_mul_cosh_add_cos (z : ℂ) :
    normSq (1 + exp z) = 2 * Real.exp z.re * (Real.cosh z.re + Real.cos z.im) := by
  rw [normSq_one_add_exp, Real.cosh_eq, Real.sin_sq]
  have hexp : Real.exp z.re * Real.exp (-z.re) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (Real.exp z.re + Real.cos z.im) ^ 2 + (1 - Real.cos z.im ^ 2)
      = Real.exp z.re ^ 2 + Real.exp z.re * Real.exp (-z.re) +
          2 * Real.exp z.re * Real.cos z.im := by rw [hexp]; ring
    _ = 2 * Real.exp z.re * ((Real.exp z.re + Real.exp (-z.re)) / 2 + Real.cos z.im) := by ring

end Complex
