/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Cast.Basic

/-!
# Identities and inequalities in additive groups with one

The difference of two opposite truncated natural differences is the difference of the original
natural casts, in any additive group with one. If `2 ≠ 0`, then `-1 ≠ 1`.

## Main results

* `Nat.cast_sub_sub_cast_sub`: opposite truncated differences recover the difference after
  casting to an additive group with one.
* `TauCeti.neg_one_ne_one_of_neZero_two`: `-1 ≠ 1` in an additive group with one where `2 ≠ 0`.
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

namespace TauCeti

/-- In an additive group with one where `2 ≠ 0`, negative one is distinct from one. -/
theorem neg_one_ne_one_of_neZero_two {R : Type*} [AddGroupWithOne R] [NeZero (2 : R)] :
    (-1 : R) ≠ 1 := by
  exact Ne.symm (by
    simpa [eq_neg_iff_add_eq_zero, one_add_one_eq_two] using (NeZero.ne (2 : R)))

end TauCeti
