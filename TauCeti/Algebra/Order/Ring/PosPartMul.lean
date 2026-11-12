/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Products of positive parts and minima

A mixed product with a minimum is the difference of the products of the matching
positive and negative parts.
-/

public section

namespace Int

/-- Express a mixed positive-part and minimum product using positive and negative parts. -/
theorem posPart_mul_add_neg_mul_min_zero (c b : ℤ) :
    b⁺ * c + (-b) * min c 0 = c⁺ * b⁺ - c⁻ * b⁻ := by
  by_cases hc : 0 ≤ c
  · simp only [posPart_def, negPart_def, max_eq_left hc,
      max_eq_right (neg_nonpos.mpr hc), min_eq_right hc, mul_zero]
    ring
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have hb := posPart_sub_negPart b
    simp only [posPart_def, negPart_def] at hb
    simp only [posPart_def, negPart_def, max_eq_right hc',
      max_eq_left (neg_nonneg.mpr hc'), min_eq_left hc', zero_mul, zero_sub]
    nlinarith

end Int
