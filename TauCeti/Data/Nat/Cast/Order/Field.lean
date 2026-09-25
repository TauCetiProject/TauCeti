/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# A lower bound from a natural reciprocal below one

A nonzero natural number whose reciprocal, cast into a linearly ordered semifield, is less than
one is at least two. This converts the reciprocal-sum hypothesis for a hyperbolic triangle group
into the parameter bounds needed for its trigonometric matrix representation.
-/

public section

namespace TauCeti

/-- A nonzero natural number whose reciprocal is less than one is at least two. -/
theorem two_le_of_cast_inv_lt_one {α : Type*} [Semifield α] [LinearOrder α]
    [IsStrictOrderedRing α] {p : ℕ} (hp : p ≠ 0) (h : (p : α)⁻¹ < 1) : 2 ≤ p :=
  Nat.one_lt_cast.1 <| (inv_lt_one₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp))).1 h

end TauCeti
