/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# Commuting simple-root subgroups of the type-B spin carrier

The numbered positive and negative simple-root subgroups of the full-weight type-`B` spin carrier
satisfy the zero-commutator Chevalley relations. Root subgroups of the same sign commute when their
nodes are not adjacent in the Dynkin diagram, while root subgroups of opposite signs commute at
distinct nodes. These statements hold over every commutative coefficient ring, including rings of
positive characteristic.

Together with the torus conjugation equations, these relations provide part of the pinned root
subgroup data for comparing the spin carrier with a simply connected group scheme of type `B`.
The nonzero commutator formulas at adjacent nodes require the remaining nonsimple root subgroups
and are not asserted here.

## Main results

* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inl_inl`: positive root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inr_inr`: negative root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inl_inr` and
  `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inr_inl`: opposite-sign root subgroups at
  distinct nodes commute.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* The formal argument follows
  `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, specialized to the type-`B` Serre
  generators and spin representation.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe u

variable {n : ℕ}

local notation "CM" => CartanMatrix.B (n + 1)
local notation "rootGen" k => TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k

private theorem lie_positive_positive_eq_zero {i j : Fin (n + 1)}
    (hij : CM i j = 0) :
    ⁅rootGen (.inl i), rootGen (.inl j)⁆ = 0 := by
  have hji : CM j i = 0 :=
    (TauCeti.isFiniteType_cartanMatrix_B (n + 1)).apply_eq_zero_symm hij
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inl, hji] using
    TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator
      (K := ℚ) i j

private theorem lie_negative_negative_eq_zero {i j : Fin (n + 1)}
    (hij : CM i j = 0) :
    ⁅rootGen (.inr i), rootGen (.inr j)⁆ = 0 := by
  have hji : CM j i = 0 :=
    (TauCeti.isFiniteType_cartanMatrix_B (n + 1)).apply_eq_zero_symm hij
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inr, hji] using
    TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
      (K := ℚ) i j

private theorem lie_positive_negative_eq_zero {i j : Fin (n + 1)} (hij : i ≠ j) :
    ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
  simpa only [TauCeti.typeBSimpleRootGeneratorFamily_inl,
    TauCeti.typeBSimpleRootGeneratorFamily_inr] using
      TauCeti.typeBSimpleRootGenerator_lie_negative_of_ne (K := ℚ) i j hij

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin (n + 1) ⊕ Fin (n + 1)} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n i A s) (rootSubgroupPoints n j A t) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints] using
    (commute_kostantRootSubgroupMatrix
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n)
      (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) (latticeBasis n)
      hij (isNilpotent_rep_rootGenerator n i) (isNilpotent_rep_rootGenerator n j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm s)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)).eq

/-- Positive numbered simple-root subgroups at nonadjacent type-`B` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin (n + 1)} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inl i) A s) (rootSubgroupPoints n (.inl j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_positive_eq_zero hij) A s t

/-- Negative numbered simple-root subgroups at nonadjacent type-`B` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin (n + 1)} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inr i) A s) (rootSubgroupPoints n (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_negative_negative_eq_zero hij) A s t

/-- Positive and negative numbered simple-root subgroups at distinct type-`B` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin (n + 1)} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inl i) A s) (rootSubgroupPoints n (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_negative_eq_zero hij) A s t

/-- Negative and positive numbered simple-root subgroups at distinct type-`B` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin (n + 1)} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inr i) A s) (rootSubgroupPoints n (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.TypeBSpinCarrier
