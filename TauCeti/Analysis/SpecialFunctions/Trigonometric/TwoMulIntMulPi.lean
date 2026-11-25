/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `sin` and `cos` at `2kπ ± x`

Mathlib's `Real.cos_eq_cos_iff` describes the solutions of `cos x = cos y` in the form
`y = 2 k π + x` or `y = 2 k π − x` with `k : ℤ`, while its periodicity lemmas
(`Real.sin_add_int_mul_two_pi`, `Real.sin_int_mul_two_pi_sub`, …) are stated for `k (2π)`.
This file records `sin` and `cos` at `2 k π ± x` in the former shape, as simp lemmas.

## Main results

* `Real.sin_two_mul_int_mul_pi_add`: `sin (2 k π + x) = sin x`.
* `Real.sin_two_mul_int_mul_pi_sub`: `sin (2 k π − x) = −sin x`.
* `Real.cos_two_mul_int_mul_pi_add`: `cos (2 k π + x) = cos x`.
* `Real.cos_two_mul_int_mul_pi_sub`: `cos (2 k π − x) = cos x`.
-/

public section

namespace Real

/-- `sin (2 k π + x) = sin x` for an integer `k`. -/
@[simp]
theorem sin_two_mul_int_mul_pi_add (k : ℤ) (x : ℝ) : sin (2 * k * π + x) = sin x := by
  rw [show 2 * k * π + x = x + k * (2 * π) by ring, sin_add_int_mul_two_pi]

/-- `sin (2 k π − x) = −sin x` for an integer `k`. -/
@[simp]
theorem sin_two_mul_int_mul_pi_sub (k : ℤ) (x : ℝ) : sin (2 * k * π - x) = -sin x := by
  rw [show 2 * k * π - x = k * (2 * π) - x by ring, sin_int_mul_two_pi_sub]

/-- `cos (2 k π + x) = cos x` for an integer `k`. -/
@[simp]
theorem cos_two_mul_int_mul_pi_add (k : ℤ) (x : ℝ) : cos (2 * k * π + x) = cos x := by
  rw [show 2 * k * π + x = x + k * (2 * π) by ring, cos_add_int_mul_two_pi]

/-- `cos (2 k π − x) = cos x` for an integer `k`. -/
@[simp]
theorem cos_two_mul_int_mul_pi_sub (k : ℤ) (x : ℝ) : cos (2 * k * π - x) = cos x := by
  rw [show 2 * k * π - x = k * (2 * π) - x by ring, cos_int_mul_two_pi_sub]

end Real
