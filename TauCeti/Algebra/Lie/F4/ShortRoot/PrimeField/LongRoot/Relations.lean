/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.F4.ShortRoot.LongRoot.Relations

/-!
# Long-root nested commutators in the characteristic-two F₄ carrier

The positive and negative nested Chevalley commutator identities at the two long simple nodes
hold in the short-root carrier generated over `𝔽₂`, over every commutative `𝔽₂`-algebra.
They follow from the integral identities by the existing matrix comparison of the numbered
root points, without identifying this generated group scheme with the specialization of the
integral toral closure. No independently pinned simply connected group scheme is identified
with this carrier; transfer to such a group requires a separate identification.

## Main results

The theorems `commutatorElement_commutatorElement_rootSubgroupPoints_inl_of_lt_two` and
`commutatorElement_commutatorElement_rootSubgroupPoints_inr_of_lt_two` in
`TauCeti.F4ShortRoot.PrimeField` give the two sign orders.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* The integral relations in `TauCeti.Algebra.Lie.F4.ShortRoot.LongRoot.Relations`.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open scoped commutatorElement

universe u

/-- The positive nested commutator relation at the distinct long simple nodes of the
carrier generated over `𝔽₂`, for arbitrary commutative coefficient algebras. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl_of_lt_two {i j : Fin 4}
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  apply (points A).subtype_injective
  simpa only [map_commutatorElement, Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    congrArg (F4ShortRoot.points A).subtype
      (F4ShortRoot.commutatorElement_commutatorElement_rootSubgroupPoints_inl_of_lt_two
        hi hj hij A t s r)

/-- The negative nested commutator relation at the distinct long simple nodes of the
carrier generated over `𝔽₂`, for arbitrary commutative coefficient algebras. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr_of_lt_two {i j : Fin 4}
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  apply (points A).subtype_injective
  simpa only [map_commutatorElement, Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    congrArg (F4ShortRoot.points A).subtype
      (F4ShortRoot.commutatorElement_commutatorElement_rootSubgroupPoints_inr_of_lt_two
        hi hj hij A t s r)

end TauCeti.F4ShortRoot.PrimeField
