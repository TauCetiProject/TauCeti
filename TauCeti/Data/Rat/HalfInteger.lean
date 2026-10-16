/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Squares of rational half-integers

An integer translated by one half has square at least one quarter. This bound applies
coordinatewise to rational vectors whose coordinates are half-integers.
-/

public section

namespace TauCeti

/-- The square of an integer translated by one half is at least one quarter. -/
theorem quarter_le_sq_add_half (z : ℤ) : (1 / 4 : ℚ) ≤ ((z : ℚ) + 1 / 2) ^ 2 := by
  have hz : z ≤ -1 ∨ 0 ≤ z := by omega
  rcases hz with hz | hz
  · have hq : (z : ℚ) ≤ -1 := by exact_mod_cast hz
    nlinarith
  · have hq : (0 : ℚ) ≤ z := by exact_mod_cast hz
    nlinarith

end TauCeti
