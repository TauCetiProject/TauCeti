/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.Short

/-!
# The adjacent short-root relation in the characteristic-two F₄ carrier

The two adjacent short simple-root subgroups of the carrier generated over `𝔽₂` have
commutator equal to the Weyl-transported sum-root point with parameter `a * b`. Both orders
have the same parameter in characteristic two. The statements hold over every commutative
`𝔽₂`-algebra, including nonreduced algebras.

The relations follow from the integral matrix calculation in
`TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.Short` through the existing root-point
comparisons. They do not identify the generated carrier with a specialization of the integral
closure, or with an independently constructed pinned group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped commutatorElement

namespace TauCeti.F4ShortRoot.PrimeField

universe v

/-- The adjacent short-root commutator has sum-root parameter `a * b`. -/
theorem commutatorElement_rootSubgroupPoints_inl_two_three
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 3) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [2] 3 A (Multiplicative.ofAdd (a * b)) := by
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints, coe_weylRootSubgroupPoints] using
    congrArg Subtype.val
      (F4ShortRoot.commutatorElement_rootSubgroupPoints_inl_two_three A a b)

/-- In characteristic two, reversing the adjacent short roots preserves the sum-root parameter. -/
theorem commutatorElement_rootSubgroupPoints_inl_three_two
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 3) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 3 A (Multiplicative.ofAdd (a * b)) := by
  have h := congrArg Subtype.val
    (F4ShortRoot.commutatorElement_rootSubgroupPoints_inl_three_two A a b)
  have hneg_one : (-1 : A) = 1 := by
    simpa only [map_neg, map_one] using
      congrArg (algebraMap (ZMod 2) A) (CharTwo.neg_eq (1 : ZMod 2))
  have hneg : -(a * b) = a * b := by
    rw [← neg_one_mul (a * b), hneg_one, one_mul]
  rw [hneg] at h
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints, coe_weylRootSubgroupPoints] using h

end TauCeti.F4ShortRoot.PrimeField
