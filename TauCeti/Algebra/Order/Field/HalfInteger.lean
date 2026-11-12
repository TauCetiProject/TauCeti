/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Tactic.Linarith

/-!
# Squares of half-integers in ordered fields

An integer cast into a linearly ordered field and translated by one half has square at least
one quarter. This bound applies coordinatewise to vectors whose coordinates are half-integers.
-/

public section

namespace Int

/-- The square of an integer translated by one half is at least one quarter. -/
theorem quarter_le_cast_add_half_sq {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (z : ℤ) : (1 / 4 : K) ≤ ((z : K) + 1 / 2) ^ 2 := by
  have hz : z ≤ -1 ∨ 0 ≤ z := by omega
  rcases hz with hz | hz
  · have hq : (z : K) ≤ -1 := by exact_mod_cast hz
    nlinarith
  · have hq : (0 : K) ≤ z := by exact_mod_cast hz
    nlinarith

end Int
