/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Inequalities for the gap between two radii

For `0 ≤ r < R` in a linearly ordered commutative ring, the difference of squares `R ^ 2 - r ^ 2`
is positive, and for `0 ≤ r ≤ R` it is at least `(R - r) ^ 2` (`TauCeti.sub_sq_le_sq_sub_sq`).
In a linearly ordered field, dividing by it compares with the gap
`R - r`: `R / (R ^ 2 - r ^ 2) ≤ 1 / (R - r)` (`TauCeti.div_sq_sub_sq_le_one_div_sub`) and
`R ^ 2 / (R ^ 2 - r ^ 2) ^ 2 ≤ 1 / (R - r) ^ 2` (`TauCeti.sq_div_sq_sub_sq_sq_le_one_div_sub_sq`).
These are the estimates behind the derivative bounds for radial cutoffs between two concentric
balls.
-/

public section

namespace TauCeti

section Ring

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] {r R : α}

/-- For `0 ≤ r < R`, the difference of squares `R ^ 2 - r ^ 2` is positive. -/
theorem sq_sub_sq_pos_of_lt (hr : 0 ≤ r) (hrR : r < R) : 0 < R ^ 2 - r ^ 2 := by
  nlinarith

/-- For `0 ≤ r ≤ R`, the squared gap `(R - r) ^ 2` is at most `R ^ 2 - r ^ 2`. -/
theorem sub_sq_le_sq_sub_sq (hr : 0 ≤ r) (hrR : r ≤ R) : (R - r) ^ 2 ≤ R ^ 2 - r ^ 2 := by
  nlinarith

end Ring

section Field

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {r R : α}

/-- For `0 ≤ r < R`, one has `R / (R ^ 2 - r ^ 2) ≤ 1 / (R - r)`. -/
theorem div_sq_sub_sq_le_one_div_sub (hr : 0 ≤ r) (hrR : r < R) :
    R / (R ^ 2 - r ^ 2) ≤ 1 / (R - r) := by
  have hRr : 0 < R - r := sub_pos.2 hrR
  rw [div_le_div_iff₀ (sq_sub_sq_pos_of_lt hr hrR) hRr]
  nlinarith

/-- For `0 ≤ r < R`, one has `R ^ 2 / (R ^ 2 - r ^ 2) ^ 2 ≤ 1 / (R - r) ^ 2`. -/
theorem sq_div_sq_sub_sq_sq_le_one_div_sub_sq (hr : 0 ≤ r) (hrR : r < R) :
    R ^ 2 / (R ^ 2 - r ^ 2) ^ 2 ≤ 1 / (R - r) ^ 2 := by
  have hR : 0 < R := hr.trans_lt hrR
  have hD0 := sq_sub_sq_pos_of_lt hr hrR
  rw [← div_pow, one_div, ← inv_pow, ← one_div]
  exact pow_le_pow_left₀ (by positivity) (div_sq_sub_sq_le_one_div_sub hr hrR) 2

end Field

end TauCeti
