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
`b / M ≤ 1 - 1 / M`, and for any `N, d : ℕ` the fractional part `(N : α) / d - (N / d : ℕ)` is at
most `1`.
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

/-- Complementary upper bound to `Nat.cast_div_le`: in a linearly ordered field, the fractional part
`(N : α) / d - (N / d : ℕ)` is at most `1` for all `N, d : ℕ` (including `d = 0`, where both terms
vanish). -/
theorem div_sub_cast_div_le_one {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (N d : ℕ) : (N : α) / d - ((N / d : ℕ) : α) ≤ 1 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd_pos : (0 : α) < d := cast_pos.mpr (pos_of_ne_zero hd)
  have hlt : (N : α) < (((N / d : ℕ) : α) + 1) * d := by
    exact_mod_cast (lt_div_mul_add (a := N) (pos_of_ne_zero hd)).trans_eq
      (Nat.succ_mul (N / d) d).symm
  exact sub_le_iff_le_add'.mpr ((div_le_iff₀ hd_pos).mpr hlt.le)

end Nat
