/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.NegativeDoubleBond
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup

/-!
# The negative double-bond relation in the short-root F₄ carrier over 𝔽₂

The negative long-short simple-root commutator factors into the Weyl-transported root
subgroups at -α₂ - α₃ and -α₂ - 2α₃, with parameters `ab` and `ab²`. Both commutator
orders are computed in the subgroup scheme generated over 𝔽₂, over arbitrary commutative
value algebras, including nonreduced algebras. No comparison of this generated scheme with
the specialization of the integral closure is needed or asserted.

The proof transports the integral relation from
`TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.NegativeDoubleBond` by the existing matrix
comparisons. See Carter, *Simple Groups of Lie Type*, Theorem 5.2.2, and Steinberg,
*Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open scoped commutatorElement

universe v

/-- The negative long-short double-bond Chevalley relation in characteristic two. The square
on the short-root parameter is retained over arbitrary value algebras. -/
theorem commutatorElement_rootSubgroupPoints_negative_doubleBond (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inr 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1, 2] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2, 1] 1 A (Multiplicative.ofAdd (a * b ^ 2)) := by
  have h := F4ShortRoot.commutatorElement_rootSubgroupPoints_negative_doubleBond A a b
  apply (points A).subtype_injective
  simpa only [map_commutatorElement, map_mul, Subgroup.subtype_apply,
    coe_rootSubgroupPoints, coe_weylRootSubgroupPoints] using
      congrArg (F4ShortRoot.points A).subtype h

/-- Reversing the negative double-bond commutator reverses the factor order, with unchanged
parameters in characteristic two. -/
theorem commutatorElement_rootSubgroupPoints_negative_doubleBond_reverse (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inr 2) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2, 1] 1 A (Multiplicative.ofAdd (a * b ^ 2)) *
        weylRootSubgroupPoints [1, 2] 2 A (Multiplicative.ofAdd (a * b)) := by
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_negative_doubleBond]
  simp only [mul_inv_rev, ← map_inv, ← ofAdd_neg, ZModModule.neg_eq_self]

end TauCeti.F4ShortRoot.PrimeField
