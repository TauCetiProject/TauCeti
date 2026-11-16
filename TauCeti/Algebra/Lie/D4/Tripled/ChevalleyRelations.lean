/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Commuting simple-root subgroups of the tripled type-D₄ carrier

The numbered positive and negative simple-root subgroups of the integral tripled type-`D₄` carrier
on `8_v ⊕ 8_s ⊕ 8_c` satisfy the zero-commutator Chevalley relations. Root subgroups of the same
sign commute when their nodes are not joined in the Dynkin diagram, that is when the corresponding
entry of `CartanMatrix.D 4` vanishes, and root subgroups of opposite signs commute at distinct
nodes. These are equalities in the carrier's group of points over every commutative ring,
including rings of positive characteristic.

Together with the torus conjugation equations, these relations are part of the pinned
root-subgroup data used to compare the carrier with a simply connected group scheme of type
`D₄`. The nonzero commutator formulas at adjacent nodes involve nonsimple root subgroups and are
not asserted here.

## Main results

* `TauCeti.D4Tripled.commute_rootSubgroupPoints_inl_inl`: positive root subgroups at
  nonadjacent nodes commute.
* `TauCeti.D4Tripled.commute_rootSubgroupPoints_inr_inr`: negative root subgroups at
  nonadjacent nodes commute.
* `TauCeti.D4Tripled.commute_rootSubgroupPoints_inl_inr` and
  `TauCeti.D4Tripled.commute_rootSubgroupPoints_inr_inl`: opposite-sign root subgroups at
  distinct nodes commute.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* The formal argument follows `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.
-/

public section

namespace TauCeti.D4Tripled

open TauCeti.UniversalEnvelopingAlgebra

universe u

local notation "rootGen" => TauCeti.serreRootGenerator weightTable.cartanMatrix

/-- The entries of the carrier's Cartan matrix are those of `CartanMatrix.D 4`. -/
private theorem cartanMatrix_apply (i j : Fin 4) :
    weightTable.cartanMatrix i j = CartanMatrix.D 4 i j := by
  rw [weightTable_cartanMatrix]

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin 4 ⊕ Fin 4} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints i A s) (rootSubgroupPoints j A t) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_rootSubgroupPoints]
  exact (commute_kostantRootSubgroupMatrix _ _ _ _ _ _ hij _ _ _ _).eq

/-- Positive numbered simple-root subgroups at nonadjacent nodes commute over every commutative
ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin 4} (hij : CartanMatrix.D 4 i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inl j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (by
    simpa only [serreRootGenerator_inl] using
      lie_serreE_serreE_of_eq_zero ℚ _ ((cartanMatrix_apply i j).trans hij)) A s t

/-- Negative numbered simple-root subgroups at nonadjacent nodes commute over every commutative
ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin 4} (hij : CartanMatrix.D 4 i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (by
    simpa only [serreRootGenerator_inr] using
      lie_serreF_serreF_of_eq_zero ℚ _ ((cartanMatrix_apply i j).trans hij)) A s t

/-- Positive and negative numbered simple-root subgroups at distinct nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (by
    simpa only [serreRootGenerator_inl, serreRootGenerator_inr] using
      lie_serreE_serreF_of_ne ℚ weightTable.cartanMatrix hij) A s t

/-- Negative and positive numbered simple-root subgroups at distinct nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.D4Tripled
