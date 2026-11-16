/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Cast.Basic

/-!
# Differences of natural casts

The difference of two opposite truncated natural differences is the difference of the original
natural casts, in any additive group with one.
-/

public section

namespace Nat

/-- Opposite truncated differences recover the difference after casting to an additive group
with one. -/
@[simp]
theorem cast_sub_sub_cast_sub {R : Type*} [AddGroupWithOne R] (a b : ℕ) :
    ((a - b : ℕ) : R) - ((b - a : ℕ) : R) = (a : R) - b := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, Nat.cast_sub h, zero_sub, neg_sub]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_zero, Nat.cast_sub h]

end Nat
