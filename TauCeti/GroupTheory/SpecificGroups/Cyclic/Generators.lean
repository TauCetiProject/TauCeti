/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Comparing generators of a finite cyclic group

Two generators of a finite cyclic group differ by an exponent coprime to its order.
The additive form is useful for comparing generating cohomology classes before lifting
maps of group extensions.
-/

public section

namespace TauCeti

/-- Two generators of a finite cyclic group differ by a power coprime to the group order. -/
@[to_additive /-- Two generators of a finite cyclic additive group differ by a multiple coprime
to the group order. -/]
theorem exists_coprime_pow_eq_of_zpowers_eq_top {G : Type*} [Group G] [Finite G]
    {x y : G} (hx : Subgroup.zpowers x = ⊤) (hy : Subgroup.zpowers y = ⊤) :
    ∃ n : ℕ, (Nat.card G).Coprime n ∧ x ^ n = y := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y x).mp <|
    mem_powers_iff_mem_zpowers.mpr (hx.symm ▸ Subgroup.mem_top y)
  have horder := orderOf_eq_card_of_zpowers_eq_top hy
  rw [← hn, orderOf_pow, orderOf_eq_card_of_zpowers_eq_top hx,
    Nat.div_eq_self] at horder
  exact ⟨n, horder.resolve_left Nat.card_pos.ne', hn⟩

end TauCeti
