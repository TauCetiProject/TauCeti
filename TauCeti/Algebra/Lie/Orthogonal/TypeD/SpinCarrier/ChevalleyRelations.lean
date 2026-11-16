/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Commuting simple-root subgroups of the type-D spin carrier

The numbered positive and negative simple-root subgroups of the full-weight type-`Dₙ` spin carrier
satisfy the zero-commutator Chevalley relations. Root subgroups of the same sign commute when their
nodes are not joined in the Dynkin diagram, that is when the corresponding entry of
`CartanMatrix.D n` vanishes, and root subgroups of opposite signs commute at distinct nodes. These
are equalities in the carrier's group of points over every commutative ring, including rings of
positive characteristic.

Together with the torus conjugation equations, these relations are part of the pinned root-subgroup
data used to compare the spin carrier with a simply connected group scheme of type `Dₙ`. The
nonzero commutator formulas at adjacent nodes involve nonsimple root subgroups and are not asserted
here.

## Main results

* `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_inl_inl`: positive root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_inr_inr`: negative root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_inl_inr` and
  `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_inr_inl`: opposite-sign root subgroups at
  distinct nodes commute.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* The formal argument follows `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe u

variable {n : ℕ} {hn : 4 ≤ n}

local notation "CM" => CartanMatrix.D n
local notation "rootGen" => TauCeti.serreRootGenerator CM

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin n ⊕ Fin n} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n hn i A s) (rootSubgroupPoints n hn j A t) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_rootSubgroupPoints]
  exact (commute_kostantRootSubgroupMatrix _ _ _ _ _ _ hij _ _ _ _).eq

/-- Positive numbered simple-root subgroups at nonadjacent type-`D` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin n} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n hn (.inl i) A s) (rootSubgroupPoints n hn (.inl j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero
    (by simpa only [serreRootGenerator_inl] using lie_serreE_serreE_of_eq_zero ℚ CM hij) A s t

/-- Negative numbered simple-root subgroups at nonadjacent type-`D` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin n} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n hn (.inr i) A s) (rootSubgroupPoints n hn (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero
    (by simpa only [serreRootGenerator_inr] using lie_serreF_serreF_of_eq_zero ℚ CM hij) A s t

/-- Positive and negative numbered simple-root subgroups at distinct type-`D` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin n} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n hn (.inl i) A s) (rootSubgroupPoints n hn (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (by
    simpa only [serreRootGenerator_inl, serreRootGenerator_inr] using
      lie_serreE_serreF_of_ne ℚ CM hij) A s t

/-- Negative and positive numbered simple-root subgroups at distinct type-`D` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin n} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n hn (.inr i) A s) (rootSubgroupPoints n hn (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.TypeDSpinCarrier
