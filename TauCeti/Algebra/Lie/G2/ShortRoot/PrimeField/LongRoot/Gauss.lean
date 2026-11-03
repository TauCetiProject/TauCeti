/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.LongRoot.Gauss
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Opposite long-root factorization in the characteristic-three G₂ carrier

The long simple-root points of the carrier generated over `𝔽₃` satisfy the rank-one
Gauss relations in both orders. The formulas hold over every commutative `𝔽₃`-algebra,
including nonreduced algebras: only `1 + a * b` must be a unit.

The relations are transported from the integral seven-dimensional matrices through
`PrimeField.coe_rootSubgroupPoints` and `PrimeField.coe_weightTorusPoints`. This uses
neither flatness nor equality of the generated carrier with the specialization of the
integral toral closure. The carrier is not identified here with an independently pinned
simply connected G₂ group scheme; transfer to that model requires such an identification.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.rootSubgroupPoints_long_mul_opposite`:
  positive times negative, collected in negative–torus–positive order.
* `TauCeti.G2ShortRoot.PrimeField.rootSubgroupPoints_opposite_mul_long`:
  the reverse order, with the inverse simple-coroot torus factor.

## References

R. W. Carter, *Simple Groups of Lie Type*, §6.1, for the rank-one relations.
The formal inputs are the integral relations in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.LongRoot.Gauss`
and the generator comparison in `PrimeField.PointsFunctor`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe v

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

/-- Gauss factorization at the long simple root of the characteristic-three carrier.
The unit `u = 1 + a * b` gives the long simple-coroot torus factor `![1, u]`. -/
theorem rootSubgroupPoints_long_mul_opposite (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A ![1, u] *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg Subtype.val (IntegralToralClosure.rootSubgroupPoints_long_mul_opposite a b u hu)

/-- Reverse-order Gauss factorization at the long simple root of the characteristic-three
carrier. The torus factor is the long simple coroot at `u⁻¹`, for `u = 1 + a * b`. -/
theorem rootSubgroupPoints_opposite_mul_long (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        weightTorusPoints A ![1, u⁻¹] *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg Subtype.val (IntegralToralClosure.rootSubgroupPoints_opposite_mul_long a b u hu)

end TauCeti.G2ShortRoot.PrimeField
