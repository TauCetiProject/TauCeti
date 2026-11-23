/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Squared norm formulas for `1 + exp z`

This file records the squared modulus of `1 + exp z` in trigonometric and
hyperbolic-trigonometric forms (`Complex.normSq_one_add_exp`,
`Complex.normSq_one_add_exp_eq_two_mul_cosh_add_cos`).
-/

public section

namespace Complex

/-- Squared modulus of `1 + exp z` in terms of `exp z.re`, `cos z.im`, and `sin z.im`. -/
theorem normSq_one_add_exp (z : ℂ) :
    normSq (1 + exp z) = (Real.exp z.re + Real.cos z.im) ^ 2 + Real.sin z.im ^ 2 := by
  rw [normSq_apply, add_re, add_im, one_re, one_im, zero_add, exp_re, exp_im]
  have hcs := Real.cos_sq_add_sin_sq z.im
  calc (1 + Real.exp z.re * Real.cos z.im) * (1 + Real.exp z.re * Real.cos z.im) +
        Real.exp z.re * Real.sin z.im * (Real.exp z.re * Real.sin z.im)
      = 1 + 2 * Real.exp z.re * Real.cos z.im +
          Real.exp z.re ^ 2 * (Real.cos z.im ^ 2 + Real.sin z.im ^ 2) := by ring
    _ = Real.exp z.re ^ 2 + 2 * Real.exp z.re * Real.cos z.im +
          (Real.cos z.im ^ 2 + Real.sin z.im ^ 2) := by rw [hcs]; ring
    _ = (Real.exp z.re + Real.cos z.im) ^ 2 + Real.sin z.im ^ 2 := by ring

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
