/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.LinearCombination

/-!
# Basic facts about the Hamilton quaternions

This file collects elementary facts about the Hamilton quaternions `ℍ[R]` over a commutative ring
`R` that depend on nothing beyond Mathlib's `Mathlib.Algebra.Quaternion`.

## Main results

* `Quaternion.isLeftRegular_two`: if `ℍ[R]` has no zero divisors then `2` is left regular in `R`,
  because the quaternion `r + r i` squares to `2 r² i`.
-/

public section

open scoped Quaternion

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- If `ℍ[R]` has no zero divisors then `2` is left regular in `R`: for `2 * r = 0` the quaternion
`r + r i` squares to `2 r² i = 0`. -/
theorem isLeftRegular_two [NoZeroDivisors ℍ[R]] : IsLeftRegular (2 : R) := by
  intro a b (h : 2 * a = 2 * b)
  have hsq : (⟨a - b, a - b, 0, 0⟩ : ℍ[R]) * ⟨a - b, a - b, 0, 0⟩ = 0 := by
    ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_zero, imI_zero, imJ_zero, imK_zero]
    · ring
    · linear_combination (a - b) * h
    all_goals ring
  exact sub_eq_zero.mp (congrArg QuaternionAlgebra.re (mul_self_eq_zero.mp hsq))

end Quaternion
