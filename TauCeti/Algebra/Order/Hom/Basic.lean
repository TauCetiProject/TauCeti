/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Order.Group.Defs

/-!
# Positive values of additive homomorphisms

A nonzero additive homomorphism from a group to a linearly ordered additive group
has a positive value. This supplies positive-period exponents without imposing an
order on the source group.
-/

public section

/-- A nonzero homomorphism from an additive group to a linearly ordered additive group
has a positive value. -/
theorem AddMonoidHom.exists_pos_of_ne_zero {H G : Type*} [AddGroup H] [AddCommGroup G]
    [LinearOrder G] [IsOrderedAddMonoid G] (N : H →+ G) (hN : N ≠ 0) :
    ∃ g, 0 < N g := by
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hN
  simp only [AddMonoidHom.zero_apply] at hg
  rcases hg.lt_or_gt with hg | hg
  · exact ⟨-g, by simpa using hg⟩
  · exact ⟨g, hg⟩
