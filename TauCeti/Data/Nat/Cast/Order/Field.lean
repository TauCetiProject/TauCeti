/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Bounds on natural casts and reciprocals in ordered fields

A nonzero natural number whose reciprocal, cast into a preordered division semiring, is less than
one is at least two. This converts the reciprocal-sum hypothesis for a hyperbolic triangle group
into the parameter bounds needed for its trigonometric matrix representation.

A natural number `b < M`, cast into a linearly ordered field, satisfies
`b / M ≤ 1 - 1 / M`.
-/

public section

namespace TauCeti

/-- A nonzero natural number whose reciprocal is less than one is at least two. -/
theorem two_le_of_cast_inv_lt_one {α : Type*} [DivisionSemiring α] [Preorder α]
    {p : ℕ} (hp : p ≠ 0) (h : (p : α)⁻¹ < 1) : 2 ≤ p := by
  refine (Nat.two_le_iff p).2 ⟨hp, ?_⟩
  rintro rfl
  simp at h

end TauCeti

namespace Nat

/-- A natural number `b` below `M` satisfies `b / M ≤ 1 - 1 / M` in a linearly ordered field. -/
lemma cast_div_le_one_sub_inv {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {b M : ℕ} (hb : b < M) : (b : α) / M ≤ 1 - 1 / M := by
  rw [le_sub_iff_add_le, ← add_div, div_le_one (by exact_mod_cast (Nat.zero_le _).trans_lt hb)]
  exact_mod_cast hb

end Nat
