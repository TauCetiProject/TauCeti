/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# A lower bound from a natural reciprocal below one

A nonzero natural number whose reciprocal, cast into a preordered division semiring, is less than
one is at least two. This converts the reciprocal-sum hypothesis for a hyperbolic triangle group
into the parameter bounds needed for its trigonometric matrix representation.
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
