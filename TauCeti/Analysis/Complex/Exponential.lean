/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# Splitting a real multiple of a complex exponent into modulus and phase

For real `c`, `a` and `t`, the exponential `exp (c (a + t i))` factors as the positive real
modulus `exp (c a)` times the unit phase `exp ((c t) i)`. This is the form in which scaled
exponentials such as `z ↦ exp (-2πz)` trace circles: the real part of `z` fixes the radius and
the imaginary part the angle.

## Main results

* `Complex.exp_ofReal_mul_ofReal_add_ofReal_mul_I`: `exp (c (a + t i)) = exp (c a) exp ((c t) i)`.
-/

public section

namespace Complex

/-- For real `c`, `a` and `t`, `exp (c (a + t i))` is the real exponential `exp (c a)` times the
unit complex number `exp ((c t) i)`. -/
theorem exp_ofReal_mul_ofReal_add_ofReal_mul_I (c a t : ℝ) :
    exp (c * (a + t * I)) = Real.exp (c * a) * exp (↑(c * t) * I) := by
  rw [ofReal_exp, ← exp_add]
  push_cast
  ring_nf

end Complex
