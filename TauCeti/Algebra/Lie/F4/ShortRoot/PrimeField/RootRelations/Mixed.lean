/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.Mixed
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup

/-!
# The long–short F₄ commutator over characteristic-two algebras

The nonzero commutator at Bourbaki nodes 2 and 3 (indices 1 and 2) is a product
of two existing Weyl-transported root points. Their parameters are `a * b` and
`a * b²`: the integral minus sign disappears in characteristic two. Both orders
of the simple-root commutator are recorded, retaining the order of the two factors.

The identities hold over arbitrary commutative 𝔽₂-algebras, including nonreduced
ones. They follow from the integral identities in
`TauCeti.F4ShortRoot.commutatorElement_rootSubgroupPoints_long_short` through the
faithful matrix inclusion. No equality with the specialization of the integral
carrier is used. The carrier is not identified with the pinned simply connected
F₄ group scheme; transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open scoped commutatorElement

universe v

/-- The long–short simple-root commutator in the characteristic-two carrier is the
product of its short and long transported root points, with parameters `a * b`
and `a * b²`. -/
theorem commutatorElement_rootSubgroupPoints_long_short (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
        rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) := by
  have hsign₂ : -(1 : ZMod 2) = 1 := by decide
  have hsign : -(1 : A) = 1 := by
    simpa only [map_neg, map_one] using congrArg (algebraMap (ZMod 2) A) hsign₂
  have hparam : -(a * b ^ 2) = a * b ^ 2 := by rw [← neg_one_mul, hsign, one_mul]
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.subtype_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_rootSubgroupPoints, coe_weylRootSubgroupPoints, hparam] using
    congrArg (F4ShortRoot.points A).subtype
      (F4ShortRoot.commutatorElement_rootSubgroupPoints_long_short A a b)

/-- In the reverse simple-root order the transported long factor precedes the short
factor; their parameters are unchanged in characteristic two. -/
theorem commutatorElement_rootSubgroupPoints_short_long (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b),
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) *
        weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) := by
  have hsign₂ : -(1 : ZMod 2) = 1 := by decide
  have hsign : -(1 : A) = 1 := by
    simpa only [map_neg, map_one] using congrArg (algebraMap (ZMod 2) A) hsign₂
  have hparam : -(a * b) = a * b := by rw [← neg_one_mul, hsign, one_mul]
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.subtype_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_rootSubgroupPoints, coe_weylRootSubgroupPoints, hparam] using
    congrArg (F4ShortRoot.points A).subtype
      (F4ShortRoot.commutatorElement_rootSubgroupPoints_short_long A a b)

end TauCeti.F4ShortRoot.PrimeField
