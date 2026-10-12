/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-! # Nonnegative square roots of square elements

A square in a linearly ordered ring has a nonnegative square root, by taking the absolute
value of any square root. Only compatibility of the order with addition is needed.
-/

public section

/-- A square in a linearly ordered ring has a nonnegative square root. -/
theorem IsSquare.exists_nonneg_sq {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedAddMonoid R] {a : R} (ha : IsSquare a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, hr⟩ := ha.exists_sq
  exact ⟨|r|, abs_nonneg r, by simpa using hr.symm⟩
