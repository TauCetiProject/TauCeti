/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Commuting simple-root subgroups of the type-E₇ minuscule carrier

The numbered positive and negative simple-root subgroups of the integral minuscule carrier
satisfy the commuting Chevalley relations. Two roots of the same sign commute when their nodes
are not joined in the Dynkin diagram, and roots of opposite signs commute at distinct nodes.
These are equalities in the carrier's group of points over **every** commutative ring, including
rings of positive characteristic.

The Serre relations give the required vanishing Lie brackets. The generic Kostant
root-subgroup theorem then transports those brackets through integral divided-power
exponentials; no factorial is inverted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.
-/

public section

namespace TauCeti.E7Minuscule

open TauCeti.UniversalEnvelopingAlgebra

universe u

local notation "CM" => CartanMatrix.E 7
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

private theorem lie_positive_positive_eq_zero {i j : Fin 7} (hij : CM i j = 0) :
    ⁅rootGen (.inl i), rootGen (.inl j)⁆ = 0 := by
  simpa only [TauCeti.serreRootGenerator_inl] using
    (show ⁅TauCeti.serreE ℚ CM i, TauCeti.serreE ℚ CM j⁆ = 0 by
      simpa [hij] using TauCeti.ad_pow_lie_serreE_serreE ℚ CM i j)

private theorem lie_negative_negative_eq_zero {i j : Fin 7} (hij : CM i j = 0) :
    ⁅rootGen (.inr i), rootGen (.inr j)⁆ = 0 := by
  simpa only [TauCeti.serreRootGenerator_inr] using
    (show ⁅TauCeti.serreF ℚ CM i, TauCeti.serreF ℚ CM j⁆ = 0 by
      simpa [hij] using TauCeti.ad_pow_lie_serreF_serreF ℚ CM i j)

private theorem lie_positive_negative_eq_zero {i j : Fin 7} (hij : i ≠ j) :
    ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
  simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
    TauCeti.lie_serreE_serreF_of_ne ℚ CM hij

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin 7 ⊕ Fin 7} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints i A s) (rootSubgroupPoints j A t) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints] using
    (commute_kostantRootSubgroupMatrix rootGen cartanGen rep
      lattice.toAddSubgroup rep_kostantForm_mem_lattice latticeBasis
      hij (isNilpotent_rep_serreRootGenerator i)
      (isNilpotent_rep_serreRootGenerator j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm s)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)).eq

/-- Positive numbered simple-root subgroups at nonadjacent nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin 7} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inl j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_positive_eq_zero hij) A s t

/-- Negative numbered simple-root subgroups at nonadjacent nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin 7} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_negative_negative_eq_zero hij) A s t

/-- A positive and a negative numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 7} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_negative_eq_zero hij) A s t

/-- A negative and a positive numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 7} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.E7Minuscule
