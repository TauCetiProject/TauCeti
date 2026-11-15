/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# The complex arctangent of a real number

Mathlib defines the complex arctangent through the Cayley transform `(1 + i z) / (1 - i z)`, as
`arctan z = -i / 2 * log ((1 + i z) / (1 - i z))`, and shows it agrees with the real arctangent on
real numbers (`Complex.ofReal_arctan`). Exponentiating gives the Cayley transform of a real number
`x` as a point of the unit circle, `(1 + i x) / (1 - i x) = e^{2 i arctan x}`.

## Main results

* `Complex.one_add_mul_I_div_one_sub_mul_I_eq_exp`: `(1 + i x) / (1 - i x) = e^{2 i arctan x}` for
  real `x`.
-/

public section

namespace Complex

/-- **The Cayley transform of a real number** is a point of the unit circle:
`(1 + i x) / (1 - i x) = e^{2 i arctan x}`. This is the defining formula of the complex arctangent
`Complex.arctan`, which agrees with the real one on real numbers. -/
theorem one_add_mul_I_div_one_sub_mul_I_eq_exp (x : ℝ) :
    (1 + x * I) / (1 - x * I) = exp (↑(2 * Real.arctan x) * I) := by
  have hne (s : ℝ) : 1 + s * x * I ≠ 0 := fun h => by simpa using congrArg re h
  have h₁ : 1 + (x : ℂ) * I ≠ 0 := by simpa using hne 1
  have h₂ : 1 - (x : ℂ) * I ≠ 0 := by simpa [sub_eq_add_neg] using hne (-1)
  -- Unfolding `arctan`, the exponent is `2 * (-i / 2 * log w) * i = -i² log w = log w`.
  have harg : (↑(2 * Real.arctan x) * I : ℂ) = log ((1 + x * I) / (1 - x * I)) := by
    rw [ofReal_mul, ofReal_arctan, arctan]
    push_cast
    linear_combination -log ((1 + x * I) / (1 - x * I)) * I_sq
  rw [harg, exp_log (div_ne_zero h₁ h₂)]

end Complex
