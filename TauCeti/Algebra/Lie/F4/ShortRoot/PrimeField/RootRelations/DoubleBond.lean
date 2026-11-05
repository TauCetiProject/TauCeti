/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.DoubleBond
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# The double-bond relation in the characteristic-two short-root F₄ carrier

The two adjacent simple roots of different lengths have a commutator with two root
factors. Here the factors use the Weyl presentations `[1], 2` and `[2], 1`, and their
parameters are `a * b` and `a * b²`. The integral relation fixes both normalizations;
characteristic two removes its minus sign, not its quadratic parameter.

The matrix comparison with the integral toral closure transfers the relation to the
carrier generated over `𝔽₂`. No equality of these two carriers is assumed. The result
holds over arbitrary commutative `𝔽₂`-algebras, including nonreduced algebras.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped commutatorElement

namespace TauCeti.F4ShortRoot.PrimeField

universe v

/-- The double-bond Chevalley relation in characteristic two, with both root
factors normalized by the numbered Weyl representatives. -/
theorem commutatorElement_rootSubgroupPoints_one_two
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) := by
  nontriviality A
  let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) A).injective 2
  apply (points A).subtype_injective
  have h := congrArg (F4ShortRoot.points A).subtype
    (F4ShortRoot.commutatorElement_rootSubgroupPoints_one_two A a b)
  simpa only [map_commutatorElement, map_mul, Subgroup.subtype_apply,
    coe_rootSubgroupPoints, coe_weylRootSubgroupPoints, CharTwo.neg_eq] using h

/-- The reverse double-bond commutator, with the highest-root factor first. -/
theorem commutatorElement_rootSubgroupPoints_two_one
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) *
        weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) := by
  nontriviality A
  let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) A).injective 2
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_one_two, mul_inv_rev]
  simp only [← map_inv, ← ofAdd_neg, CharTwo.neg_eq]

end TauCeti.F4ShortRoot.PrimeField
