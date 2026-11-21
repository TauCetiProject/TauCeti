/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Complex derivative of translated Gaussians

This file records the complex derivative of the translated quadratic exponential
`w ↦ exp (a (w - b)²)`, for complex `a` and `b`, as an elementary chain-rule computation with no
measure theory. Gaussian kernels such as `z ↦ exp (-(c (t - z))²)` and `w ↦ exp (-(z + w)² / 2)`
are the cases `a = -c²`, `b = t` and `a = -1/2`, `b = -z`.

## Main statements

* `Complex.hasDerivAt_cexp_mul_sub_sq`: the complex derivative of `w ↦ exp (a (w - b)²)`.
-/

public section

namespace Complex

/-- The complex derivative of the translated quadratic exponential `w ↦ exp (a (w - b)²)` is
`exp (a (w - b)²) · 2a (w - b)`, for complex `a` and `b`. -/
theorem hasDerivAt_cexp_mul_sub_sq (a b w : ℂ) :
    HasDerivAt (fun w : ℂ => cexp (a * (w - b) ^ 2)) (cexp (a * (w - b) ^ 2) * (2 * a * (w - b)))
      w := by
  have h := (((hasDerivAt_id' w).sub_const b).fun_pow 2).const_mul a |>.cexp
  convert h using 1
  ring

end Complex
