/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Root.Relations.LongPair
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Weyl

/-!
# The long-root A₂ commutator in the characteristic-three G₂ carrier

The three positive long-root parametrizations, normalized by pinned rank-one words,
satisfy the A₂ commutator relation in the short-root carrier generated over `𝔽₃`.
The parameter is the product `ab`, with no restriction on the commutative value algebra.

The proof transfers the integral matrix identity through the faithful matrix inclusion.
It uses only the existing agreement of the numbered root matrices; it does not identify
this generated carrier with the specialization of the integral toral closure or with an
independently constructed pinned simply connected group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped commutatorElement

namespace TauCeti.G2ShortRoot.PrimeField

universe v

/-- The long-root A₂ Chevalley commutator in the carrier generated over `𝔽₃`, with its
nonsimple root parametrizations normalized by the numbered rank-one words. -/
theorem commutatorElement_rootSubgroupPoints_simpleWeylPoint_conj_rootSubgroupPoints
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
      simpleWeylPoint 0 A * rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b) *
        (simpleWeylPoint 0 A)⁻¹⁆ =
      (simpleWeylPoint 1 A * simpleWeylPoint 0 A) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * b)) *
        (simpleWeylPoint 1 A * simpleWeylPoint 0 A)⁻¹ := by
  apply Subtype.ext
  have h := congrArg Subtype.val <|
  IntegralToralClosure.commutatorElement_rootSubgroupPoints_simpleWeylPoint_conj_rootSubgroupPoints
    A a b
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints, coe_simpleWeylPoint] using h

end TauCeti.G2ShortRoot.PrimeField
