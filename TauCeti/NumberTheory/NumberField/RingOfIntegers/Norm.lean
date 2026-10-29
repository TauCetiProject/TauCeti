/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Norm

/-!
# Lower bound for the norm of a nonzero algebraic integer

The norm `N(α) = Algebra.norm ℚ α` of a nonzero algebraic integer `α` is a nonzero integer, so
`1 ≤ |N(α)|`.

## Main results

* `NumberField.RingOfIntegers.one_le_abs_norm`: `1 ≤ |N(α)|` for every nonzero `α : 𝓞 K`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of the norm of a nonzero algebraic integer is at least one. -/
theorem one_le_abs_norm {α : 𝓞 K} (hα : α ≠ 0) :
    (1 : ℝ) ≤ |(Algebra.norm ℚ (α : K) : ℝ)| := by
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hα)

end NumberField.RingOfIntegers
