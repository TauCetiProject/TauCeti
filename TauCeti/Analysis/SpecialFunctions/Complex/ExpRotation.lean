/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The height of a rotated real number

Rotating a real number `d` by the angle `-θ` gives a complex number of height `d * sin (-θ)`.

## Main results

* `TauCeti.im_exp_neg_mul_ofReal`: `(exp (-θ * I) * d).im = d * sin (-θ)`.
-/

public section

namespace TauCeti

/-- Rotating a real number by `-θ` gives imaginary part `d * sin (-θ)`. -/
lemma im_exp_neg_mul_ofReal (θ d : ℝ) :
    (Complex.exp (-θ * Complex.I) * (d : ℂ)).im = d * Real.sin (-θ) := by
  have hexp : -((θ : ℂ)) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, mul_comm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im]

end TauCeti
