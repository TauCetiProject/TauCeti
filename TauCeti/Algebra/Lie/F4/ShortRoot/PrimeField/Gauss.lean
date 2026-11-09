/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
import TauCeti.Algebra.Lie.F4.ShortRoot.Gauss

/-!
# Opposite short-root multiplication over the prime field

The short-root Gauss relations hold in the type-F₄ carrier generated over `𝔽₂`, over every
commutative value algebra, including nonreduced ones. The positive-negative and negative-positive
products have their standard three-factor decompositions whenever `1 + a * b` is a unit.

These are the integral identities of `TauCeti.Algebra.Lie.F4.ShortRoot.Gauss`, transported by the
root and torus matrix comparisons in `PrimeField.PointsFunctor`. No equality between the
prime-field generated carrier and the reduction of the integral closure is needed or asserted.
Nor is the carrier identified with an independently pinned simply connected group.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6 (rank-one relations).
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

/-- The positive-negative short-root Gauss relation in the carrier generated over `𝔽₂`.
The index is a short Bourbaki node, and `c` is the unit `1 + a * b`. -/
theorem rootSubgroupPoints_inl_mul_inr {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (i : Fin 4) (hi : 2 ≤ i.val) (a b : A) (c : Aˣ) (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg Subtype.val (F4ShortRoot.rootSubgroupPoints_inl_mul_inr i hi a b c hc)

/-- The negative-positive short-root Gauss relation in the carrier generated over `𝔽₂`.
Its torus factor has simple-coroot parameter `c⁻¹`, for the unit `c = 1 + a * b`. -/
theorem rootSubgroupPoints_inr_mul_inl {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (i : Fin 4) (hi : 2 ≤ i.val) (a b : A) (c : Aˣ) (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg Subtype.val (F4ShortRoot.rootSubgroupPoints_inr_mul_inl i hi a b c hc)

end TauCeti.F4ShortRoot.PrimeField
