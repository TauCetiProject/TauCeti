/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.ChevalleyRelations
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor

/-!
# Commuting simple-root subgroups of the F₄ carrier generated over 𝔽₂

The zero-commutator Chevalley relations hold in the short-root subgroup scheme generated over
𝔽₂. They follow from the integral relations by the equality of the numbered root-subgroup
matrices. This does not identify the generated subgroup scheme with the reduction of the
integral toral closure. All equations hold over arbitrary commutative 𝔽₂-algebras, including
nonreduced algebras, and use the Bourbaki node numbering.

The carrier is not identified with the pinned simply connected group scheme of its diagram.
Its constructions transfer to that pinned group only along such an identification, once proved.

## Main results

* `commute_rootSubgroupPoints_inl_inl` and `commute_rootSubgroupPoints_inr_inr`:
  same-sign root points commute at nonadjacent nodes.
* `commute_rootSubgroupPoints_inl_inr` and `commute_rootSubgroupPoints_inr_inl`:
  opposite-sign root points commute at distinct nodes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* The integral relations in `TauCeti.Algebra.Lie.F4.ShortRoot.ChevalleyRelations`.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

universe u

/-- Positive numbered simple-root subgroups at nonadjacent Bourbaki nodes commute over every
commutative 𝔽₂-algebra. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin 4} (hij : CartanMatrix.F₄ i j = 0)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inl j) A t) := by
  apply Commute.of_map (f := (points A).subtype) Subtype.val_injective
  simpa only [Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    (F4ShortRoot.commute_rootSubgroupPoints_inl_inl hij A s t).map (F4ShortRoot.points A).subtype

/-- Negative numbered simple-root subgroups at nonadjacent Bourbaki nodes commute over every
commutative 𝔽₂-algebra. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin 4} (hij : CartanMatrix.F₄ i j = 0)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inr j) A t) := by
  apply Commute.of_map (f := (points A).subtype) Subtype.val_injective
  simpa only [Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    (F4ShortRoot.commute_rootSubgroupPoints_inr_inr hij A s t).map (F4ShortRoot.points A).subtype

/-- A positive and a negative numbered simple-root subgroup at distinct nodes commute over
every commutative 𝔽₂-algebra. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) := by
  apply Commute.of_map (f := (points A).subtype) Subtype.val_injective
  simpa only [Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    (F4ShortRoot.commute_rootSubgroupPoints_inl_inr hij A s t).map (F4ShortRoot.points A).subtype

/-- A negative and a positive numbered simple-root subgroup at distinct nodes commute over
every commutative 𝔽₂-algebra. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] [Algebra (ZMod 2) A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.F4ShortRoot.PrimeField
