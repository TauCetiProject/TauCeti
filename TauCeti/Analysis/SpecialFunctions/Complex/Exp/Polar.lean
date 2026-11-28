/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# The polar form of a complex exponential

Splitting `w = Re w + i Im w` writes `exp w` in polar form with modulus `‖exp w‖ = e^{Re w}`
and argument `Im w`: `exp w = ‖exp w‖ e^{i Im w}`. Unlike Mathlib's
`Complex.norm_mul_exp_arg_mul_I`, the angle here is `Im w`, which need not lie in `(-π, π]`;
this is the form in which a continuous logarithm `L` of a function gives a continuous argument
`Im L`.

## Main results

* `Complex.norm_exp_mul_exp_im_mul_I`: `‖exp w‖ * exp (Im w * I) = exp w`.
-/

public section

namespace Complex

/-- **Polar form of `exp w` with angle `Im w`.** `‖exp w‖ e^{i Im w} = exp w`. -/
theorem norm_exp_mul_exp_im_mul_I (w : ℂ) : ‖exp w‖ * exp (w.im * I) = exp w := by
  rw [norm_exp, ofReal_exp, ← exp_add, re_add_im]

end Complex
