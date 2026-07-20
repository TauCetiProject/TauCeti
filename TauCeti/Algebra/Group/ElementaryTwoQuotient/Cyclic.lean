/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.FreeModule
public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The maximal elementary-2 quotient of a cyclic group of even order

For a cyclic group `G` of even order, the maximal elementary-2 quotient `G / G²` of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic` has exactly two elements, so its 2-rank is
`1`. "Even order" is read via `Nat.card`: a finite cyclic group of even order and an infinite
cyclic group (where `Nat.card G = 0`, also even) both have two square classes — for the finite
case `G²` has index `gcd |G| 2 = 2`, and for the infinite case `G ≃* Multiplicative ℤ` has
`G / G² ≃ ℤ/2ℤ`.

These are the cyclic building blocks promised by the product lemmas of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Prod`: a finite abelian group is a product of cyclic
groups, and combining that decomposition with this file reads off its 2-rank as the number of
even-order cyclic factors. The multiquadratic roadmap consumes the even case through the torsion
subgroup of a number field's unit group, which is finite cyclic of even order.

The odd-order case needs no cyclicity — it holds for any commutative group of odd order — so it
lives in `Basic` as `TauCeti.card_elementaryTwoQuotient_of_odd_card`, not here.

## Main results

* `TauCeti.card_elementaryTwoQuotient_of_isCyclic_of_even`: `|G/G²| = 2` for cyclic `G` of even
  order.
* `TauCeti.twoRank_of_isCyclic_of_even`: such a `G` has 2-rank `1`.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] [IsCyclic G]

/-- **A cyclic group of even order has exactly two square classes.** For the finite case the
subgroup of squares has index `gcd |G| 2 = 2` (Mathlib's `IsCyclic.index_powMonoidHom_range`,
read through `G² = range (powMonoidHom 2)`); the infinite case is `G ≃* Multiplicative ℤ`, whose
elementary-2 quotient is `2 ^ finrank ℤ ℤ = 2`. -/
theorem card_elementaryTwoQuotient_of_isCyclic_of_even (h : Even (Nat.card G)) :
    Nat.card (ElementaryTwoQuotient G) = 2 := by
  rcases finite_or_infinite G with hfin | hinf
  · rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range,
      IsCyclic.index_powMonoidHom_range, Nat.gcd_comm]
    exact Nat.gcd_eq_left h.two_dvd
  · rw [Nat.card_congr
        (elementaryTwoQuotientCongr (intCyclicMulEquiv (G := G)).symm).toEquiv,
      card_elementaryTwoQuotient_multiplicative, Module.finrank_self, pow_one]

/-- A cyclic group of even order has 2-rank one. -/
theorem twoRank_of_isCyclic_of_even (h : Even (Nat.card G)) : twoRank G = 1 :=
  twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow G
    ((card_elementaryTwoQuotient_of_isCyclic_of_even G h).trans (pow_one 2).symm)

end TauCeti
