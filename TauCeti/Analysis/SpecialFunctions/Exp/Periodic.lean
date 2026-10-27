/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The period `2` of `exp (π i ·)`

Mathlib characterises equality of complex exponentials by `Complex.exp_eq_exp_iff_exists_int`:
`exp x = exp y` if and only if `x - y ∈ 2 π i ℤ`. This file records the form of the sufficient
condition used for the factors `exp (π i x)` of theta series and modular forms, where the
period is `2` in the variable `x`.

## Main declarations

* `Complex.exp_pi_mul_I_mul_eq_of_sub_eq`: `exp (π i a) = exp (π i b)` whenever `a - b` is an
  even integer.
-/

public section

open Real

namespace Complex

/-- `exp (π i a) = exp (π i b)` whenever `a - b` is an even integer. -/
theorem exp_pi_mul_I_mul_eq_of_sub_eq {a b : ℂ} {m : ℤ} (h : a - b = 2 * m) :
    cexp (π * I * a) = cexp (π * I * b) :=
  exp_eq_exp_iff_exists_int.mpr ⟨m, by linear_combination (π * I) * h⟩

end Complex
