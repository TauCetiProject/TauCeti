/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Complementary arctangents at the corners of a rectangle

Mathlib's `Real.arctan_inv_of_pos` gives `arctan x⁻¹ = π / 2 - arctan x`; the quotient form
`arctan (u / v) + arctan (v / u) = π / 2` that occurs when the two legs of a right angle are named
separately is not stated there.

## Main results

* `Real.arctan_div_add_arctan_div`: the quotient form of the complementary-angle law.
* `TauCeti.arctan_corner_sum_eq_two_mul_pi_mul_I`: the four corner angles of a rectangle straddling
  the imaginary axis sum to a full turn.
-/

public section

open Complex

open scoped Real

namespace Real

/-- **Complementary angles, in quotient form.**  For positive `u` and `v` the angles
`arctan (u / v)` and `arctan (v / u)` are complementary. -/
theorem arctan_div_add_arctan_div {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    arctan (u / v) + arctan (v / u) = π / 2 := by
  rw [← inv_div u v, Real.arctan_inv_of_pos (by positivity)]
  ring

end Real

namespace TauCeti

/-- **The corner angles of a rectangle sum to a full turn.**  For a rectangle with vertical sides at
`-B < 0 < c` and horizontal sides at heights `±T`, the four angles subtended at the origin combine
to `2π i`. -/
theorem arctan_corner_sum_eq_two_mul_pi_mul_I {c B T : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hT : 0 < T) :
    2 * I * ((Real.arctan (c / T) : ℂ) - (Real.arctan (-B / T) : ℂ))
      + I * (2 * (Real.arctan (T / c) : ℂ)) - I * (2 * (Real.arctan (T / -B) : ℂ))
      = 2 * π * I := by
  have hA : ((Real.arctan (c / T) : ℝ) : ℂ) + ((Real.arctan (T / c) : ℝ) : ℂ) = (π : ℂ) / 2 := by
    rw [← Complex.ofReal_add, Real.arctan_div_add_arctan_div hc hT]
    push_cast
    ring
  have hB' : ((Real.arctan (B / T) : ℝ) : ℂ) + ((Real.arctan (T / B) : ℝ) : ℂ) = (π : ℂ) / 2 := by
    rw [← Complex.ofReal_add, Real.arctan_div_add_arctan_div hB hT]
    push_cast
    ring
  rw [neg_div, Real.arctan_neg, div_neg, Real.arctan_neg]
  push_cast
  linear_combination (2 * I) * hA + (2 * I) * hB'

end TauCeti
