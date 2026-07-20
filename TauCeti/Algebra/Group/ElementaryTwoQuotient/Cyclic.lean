/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The maximal elementary-2 quotient of a finite cyclic group

For a finite cyclic group `G`, the maximal elementary-2 quotient `G / G²` of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic` has cardinality `gcd |G| 2`: two elements when
`|G|` is even and one when `|G|` is odd. Correspondingly the 2-rank of a finite cyclic group is
`1` or `0` according to the parity of its order.

These are the cyclic building blocks promised by the product lemmas of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Prod`: a finite abelian group is a product of cyclic
groups, and combining that decomposition with this file reads off its 2-rank as the number of
even-order cyclic factors. The multiquadratic roadmap consumes the even case through the torsion
subgroup of a number field's unit group, which is finite cyclic of even order.

The computation itself is Mathlib's `IsCyclic.index_powMonoidHom_range` (the subgroup of `d`-th
powers of a finite cyclic group has index `gcd |G| d`) read through the identification of `G²`
with the range of the squaring homomorphism.

## Main results

* `TauCeti.card_elementaryTwoQuotient_of_isCyclic`: `|G/G²| = gcd |G| 2` for `G` finite cyclic.
* `TauCeti.card_elementaryTwoQuotient_of_isCyclic_of_even` and
  `TauCeti.card_elementaryTwoQuotient_of_isCyclic_of_odd`: the two parity readings, `2` and `1`.
* `TauCeti.twoRank_of_isCyclic_of_even` and `TauCeti.twoRank_of_isCyclic_of_odd`: the 2-rank of a
  finite cyclic group is `1` for even order and `0` for odd order.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] [IsCyclic G] [Finite G]

/-- **The elementary-2 quotient of a finite cyclic group has `gcd |G| 2` elements.** This is
Mathlib's index computation for the subgroup of `d`-th powers of a cyclic group, specialized to
`d = 2` and read through `G² = range (powMonoidHom 2)`. -/
theorem card_elementaryTwoQuotient_of_isCyclic :
    Nat.card (ElementaryTwoQuotient G) = (Nat.card G).gcd 2 := by
  rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range,
    IsCyclic.index_powMonoidHom_range]

/-- A finite cyclic group of even order has exactly two square classes. -/
theorem card_elementaryTwoQuotient_of_isCyclic_of_even (h : Even (Nat.card G)) :
    Nat.card (ElementaryTwoQuotient G) = 2 := by
  rw [card_elementaryTwoQuotient_of_isCyclic, Nat.gcd_comm]
  exact Nat.gcd_eq_left h.two_dvd

/-- In a finite cyclic group of odd order every element is a square: there is exactly one square
class. -/
theorem card_elementaryTwoQuotient_of_isCyclic_of_odd (h : Odd (Nat.card G)) :
    Nat.card (ElementaryTwoQuotient G) = 1 := by
  rw [card_elementaryTwoQuotient_of_isCyclic]
  exact h.coprime_two_right

/-- A finite cyclic group of even order has 2-rank one. -/
theorem twoRank_of_isCyclic_of_even (h : Even (Nat.card G)) : twoRank G = 1 := by
  have hcard := card_elementaryTwoQuotient_of_isCyclic_of_even G h
  rw [card_elementaryTwoQuotient_eq_two_pow_twoRank, ← pow_one 2] at hcard
  exact Nat.pow_right_injective le_rfl hcard

/-- A finite cyclic group of odd order has 2-rank zero. -/
theorem twoRank_of_isCyclic_of_odd (h : Odd (Nat.card G)) : twoRank G = 0 := by
  have hcard := card_elementaryTwoQuotient_of_isCyclic_of_odd G h
  rw [card_elementaryTwoQuotient_eq_two_pow_twoRank, ← pow_zero 2] at hcard
  exact Nat.pow_right_injective le_rfl hcard

end TauCeti
