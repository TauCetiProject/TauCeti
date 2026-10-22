/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Integer powers of `-1` as complex exponentials

Complements `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`, where `e^{π i} = -1` is
`Complex.exp_pi_mul_I`.

## Main results

* `Complex.neg_one_zpow_eq_exp`: `(-1)ⁿ = e^{-π i n}` for an integer `n`.
-/

public section

open scoped Real

namespace Complex

/-- `(-1)ⁿ = e^{-π i n}` for an integer `n`. -/
theorem neg_one_zpow_eq_exp (n : ℤ) : (-1 : ℂ) ^ n = exp (n * -(π * I)) := by
  rw [exp_int_mul, exp_neg, exp_pi_mul_I, inv_neg, inv_one]

end Complex
