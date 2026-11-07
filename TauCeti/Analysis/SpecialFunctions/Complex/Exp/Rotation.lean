/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The height of a rotated real number

Rotating a real number `d` by the angle `φ` gives a complex number of height `d * sin φ`.

## Main results

* `TauCeti.im_exp_ofReal_mul_I_mul_ofReal`: `(exp (φ * I) * d).im = d * sin φ`.
-/

public section

namespace TauCeti

/-- Rotating a real number `d` by the angle `φ` gives imaginary part `d * sin φ`. -/
lemma im_exp_ofReal_mul_I_mul_ofReal (φ d : ℝ) :
    (Complex.exp (φ * Complex.I) * (d : ℂ)).im = d * Real.sin φ := by
  rw [mul_comm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im]

end TauCeti
