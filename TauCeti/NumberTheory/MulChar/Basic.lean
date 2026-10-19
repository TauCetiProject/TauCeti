/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Ranges of multiplicative characters

To show that a multiplicative character takes values in a subset containing zero, it suffices
to check the values on units. This applies, for example, to subfields and subrings containing
the character values on units, since a multiplicative character vanishes on nonunits.
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

end MulChar
