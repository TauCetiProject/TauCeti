/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# An oscillation times a real exponential

The product of an oscillation `exp (b x i)` and a real exponential `exp (c x)` is the single
complex exponential `exp ((c + b i) x)`.

## Main declarations

* `TauCeti.exp_mul_I_mul_ofReal_exp_mul`: `exp (b x i) * exp (c x) = exp ((c + b i) x)`.
-/

public section

namespace TauCeti

/-- `exp (b x i) * exp (c x) = exp ((c + b i) x)`: an oscillation times a real exponential is a
single complex exponential. -/
theorem exp_mul_I_mul_ofReal_exp_mul (b c x : ℝ) :
    Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ)
      = Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end TauCeti

end
