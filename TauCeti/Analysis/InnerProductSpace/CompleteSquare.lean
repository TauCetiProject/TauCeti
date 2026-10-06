/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Completing the square for a weighted sum of squared distances

In a real inner product space, a weighted sum `a ‖y‖² + b ‖x - y‖²` of the squared distances from
`y` to the two points `0` and `x` is, as a function of `y`, a multiple of the squared distance
from `y` to the weighted centre `(b / (a + b)) • x`, plus a constant:

`a ‖y‖² + b ‖x - y‖² = (a + b) ‖y - (b / (a + b)) • x‖² + (a b / (a + b)) ‖x‖²`

whenever `a + b ≠ 0`. This is the identity behind products of Gaussians being Gaussians.

## Main declarations

* `TauCeti.mul_norm_sq_add_mul_norm_sub_sq`: the completed-square identity above.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Completing the square** for a weighted sum of squared distances: if `a + b ≠ 0`, then
`a ‖y‖² + b ‖x - y‖² = (a + b) ‖y - (b / (a + b)) • x‖² + (a b / (a + b)) ‖x‖²`. -/
theorem mul_norm_sq_add_mul_norm_sub_sq {a b : ℝ} (hab : a + b ≠ 0) (x y : F) :
    a * ‖y‖ ^ 2 + b * ‖x - y‖ ^ 2 =
      (a + b) * ‖y - (b / (a + b)) • x‖ ^ 2 + a * b / (a + b) * ‖x‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm]
  field_simp
  ring

end TauCeti
