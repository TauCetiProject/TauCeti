/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The principal square root and the slit plane

The principal square root has nonnegative real part, and its real part is strictly positive
exactly on the slit plane. These facts control the branches in algebraic transformations
involving sums of principal roots.
-/

public section

namespace Complex

/-- The square of the principal square root is the original complex number. -/
@[simp]
theorem sq_sqrt (z : ℂ) : sqrt z ^ 2 = z :=
  cpow_ofNat_inv_pow z 2

/-- The principal square root has nonnegative real part. -/
@[simp]
theorem sqrt_re_nonneg (z : ℂ) : 0 ≤ (sqrt z).re := by
  rw [sqrt, cpow_inv_two_re]
  positivity

/-- The principal square root has nonnegative imaginary part when the input does. -/
theorem sqrt_im_nonneg {z : ℂ} (h : 0 ≤ z.im) : 0 ≤ (sqrt z).im := by
  rw [sqrt, cpow_inv_two_im_eq_sqrt h]
  exact Real.sqrt_nonneg _

/-- The principal square root has positive real part exactly on the slit plane. -/
@[simp]
theorem sqrt_re_pos_iff (z : ℂ) : 0 < (sqrt z).re ↔ z ∈ slitPlane := by
  rw [sqrt, cpow_inv_two_re, Real.sqrt_pos, div_pos_iff_of_pos_right (by norm_num),
    mem_slitPlane_iff_not_le_zero, ← neg_re_eq_norm]
  have h := (neg_le_abs z.re).trans (abs_re_le_norm z)
  constructor
  · intro hz heq
    linarith
  · intro hz
    have hlt := lt_of_le_of_ne h hz
    linarith

/-- A sum of principal square roots has positive real part exactly when at least one
input lies in the slit plane. -/
@[simp]
theorem sqrt_add_sqrt_re_pos_iff (x y : ℂ) :
    0 < (sqrt x).re + (sqrt y).re ↔ x ∈ slitPlane ∨ y ∈ slitPlane := by
  rw [← sqrt_re_pos_iff x, ← sqrt_re_pos_iff y]
  have hx := sqrt_re_nonneg x
  have hy := sqrt_re_nonneg y
  constructor
  · intro h
    by_contra! hn
    linarith
  · rintro (h | h) <;> linarith

end Complex
