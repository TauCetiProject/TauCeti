/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# Elementary abelian groups of order `4`

An additive commutative group of cardinality four that is a `ZMod 2`-module is a Klein four-group.

A commutative group of order `4` whose maximal elementary-2 quotient `G / G²` has `2`-rank `2` is
as large as that quotient, so every element squares to one
(`TauCeti.sq_eq_one_of_card_elementaryTwoQuotient_eq_card`) and `G` is a Klein four-group.

## Main results

* `TauCeti.isAddKleinFour_of_natCard_eq_four`: a `ZMod 2`-module of cardinality four is a
  Klein four-group.
* `TauCeti.isKleinFour_of_card_eq_four_of_twoRank_eq_two`: such a group is a Klein four-group.
-/

public section

namespace TauCeti

/-- An additive commutative group of cardinality four that is a `ZMod 2`-module is a Klein
four-group. -/
theorem isAddKleinFour_of_natCard_eq_four {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (hcard : Nat.card A = 4) : IsAddKleinFour A := by
  let _ : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hcard, (AddMonoid.exponent_eq_prime_iff Nat.prime_two).mpr fun a ha ↦
    addOrderOf_eq_prime (ZModModule.char_nsmul_eq_zero 2 a) ha⟩

variable {G : Type*} [CommGroup G]

/-- **A commutative group of order `4` and `2`-rank `2` is a Klein four-group.** Its maximal
elementary-2 quotient has `2 ^ 2 = 4` elements, as many as `G`, so `G` has exponent `2`. -/
theorem isKleinFour_of_card_eq_four_of_twoRank_eq_two (hcard : Nat.card G = 4)
    (hrank : twoRank G = 2) : IsKleinFour G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hsq := sq_eq_one_of_card_elementaryTwoQuotient_eq_card (G := G) <| by
    rw [card_elementaryTwoQuotient_eq_two_pow_twoRank, hrank, hcard]; norm_num
  refine ⟨hcard, le_antisymm ?_ Monoid.one_lt_exponent⟩
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one hsq)

end TauCeti
