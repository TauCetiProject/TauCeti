/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.ChevalleyRelations

/-!
# Mixed-sign simple-root relations in the characteristic-three G₂ carrier

The positive and negative numbered simple-root subgroups of the carrier generated over 𝔽₃
commute at distinct nodes, over every commutative 𝔽₃-algebra. The characteristic matrix
comparison with the integral root subgroups transfers the relations without identifying the
prime-field generated carrier with the specialization of the integral toral closure.

The carrier is not identified with the pinned simply connected group scheme of type G₂.
These relations transfer to that group scheme only along such an identification.

## Main results

* `commute_rootSubgroupPoints_inl_inr`: the positive-negative relation at distinct nodes.
* `commute_rootSubgroupPoints_inr_inl`: the negative-positive relation at distinct nodes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe u

/-- Positive and negative numbered simple-root subgroups at distinct nodes commute over every
commutative 𝔽₃-algebra, including nonreduced algebras. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 2} (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 3) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints] using
    congrArg Subtype.val
      (IntegralToralClosure.commute_rootSubgroupPoints_inl_inr hij A s t).eq

/-- Negative and positive numbered simple-root subgroups at distinct nodes commute over every
commutative 𝔽₃-algebra. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 2} (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 3) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.G2ShortRoot.PrimeField
