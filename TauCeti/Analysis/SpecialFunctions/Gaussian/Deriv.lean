/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Complex derivatives of translated Gaussians

This file records the complex derivatives of two translated Gaussian kernels, as elementary
chain-rule computations with no measure theory: the kernel `z ↦ exp (-(c (t - z))²)` of scale `c`
and centre `t`, and the unit-variance kernel `w ↦ exp (-(z + w)² / 2)` translated by `z`.

## Main statements

* `Complex.hasDerivAt_cexp_neg_mul_sub_sq`: the complex derivative of
  `z ↦ exp (-(c (t - z))²)`, for complex `c` and `t`.
* `Complex.hasDerivAt_cexp_neg_add_sq_div_two`: the complex derivative of
  `w ↦ exp (-(z + w)² / 2)`.
-/

public section

namespace Complex

/-- The complex derivative of the translated Gaussian `z ↦ exp (-(c (t - z))²)`, for complex
scale `c` and centre `t`. -/
theorem hasDerivAt_cexp_neg_mul_sub_sq (c t z : ℂ) :
    HasDerivAt (fun z : ℂ => cexp (-(c * (t - z)) ^ 2))
      (cexp (-(c * (t - z)) ^ 2) * (2 * c ^ 2 * (t - z))) z := by
  have h := (((hasDerivAt_id' z).const_sub t).const_mul c).fun_pow 2 |>.fun_neg.cexp
  convert h using 1
  ring

/-- The complex derivative of the translated Gaussian `w ↦ exp (-(z + w)² / 2)` is
`-(z + w) exp (-(z + w)² / 2)`. -/
theorem hasDerivAt_cexp_neg_add_sq_div_two (z w : ℂ) :
    HasDerivAt (fun v : ℂ => cexp (-((z + v) ^ 2) / 2)) (cexp (-((z + w) ^ 2) / 2) * -(z + w))
      w := by
  have h := ((((hasDerivAt_id' w).const_add z).fun_pow 2).fun_neg.div_const 2).cexp
  convert h using 1
  ring

end Complex
