/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Basic facts about multiplicative characters

To show that a multiplicative character takes values in a subset containing zero, it suffices
to check the values on units. This applies, for example, to subfields and subrings containing
the character values on units, since a multiplicative character vanishes on nonunits.

The trivial character takes only the values `0` and `1`, on nonunits and units respectively, so
it is unchanged by transport along an isomorphism of the domain and a homomorphism of the
coefficients (`MulChar.map_one_apply`).
-/

public section

namespace MulChar

/-- A multiplicative character takes values in a subset containing `0` whenever all its values
on units lie there. -/
theorem apply_mem_of_forall_unit {R R' S : Type*} [CommMonoid R]
    [CommMonoidWithZero R'] [SetLike S R'] [ZeroMemClass S R'] (χ : MulChar R R') (s : S)
    (hχ : ∀ u : Rˣ, χ (u : R) ∈ s) (a : R) : χ a ∈ s := by
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec]
    exact hχ _
  · rw [MulChar.map_nonunit _ ha]
    exact zero_mem s

/-- The trivial character commutes with transport along a multiplicative isomorphism `e` of the
domain and a homomorphism `f` of the coefficients: both sides are `1` on units and `0` on
nonunits. -/
theorem map_one_apply {R S R' R'' F G : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero R'] [CommMonoidWithZero R''] [FunLike F R' R'']
    [MonoidWithZeroHomClass F R' R''] [EquivLike G R S] [MulEquivClass G R S] (f : F) (e : G)
    (a : R) : f ((1 : MulChar R R') a) = (1 : MulChar S R'') (e a) := by
  by_cases ha : IsUnit a
  · rw [one_apply ha, one_apply (ha.map e), map_one]
  · rw [map_nonunit _ ha, map_nonunit _ (by rwa [isUnit_map_iff]), map_zero]

end MulChar
