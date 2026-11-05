/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
public import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Chevalley relations between simple-root subgroups of the type-E₇ minuscule carrier

The numbered positive and negative simple-root subgroups of the integral minuscule carrier
satisfy the commuting Chevalley relations. Two roots of the same sign commute when their nodes
are not joined in the Dynkin diagram, and roots of opposite signs commute at distinct nodes.
These are equalities in the carrier's group of points over **every** commutative ring, including
rings of positive characteristic.

Together these give the zero-commutator cases of the pinned Chevalley relations for the E₇
carrier. They allow the numbered root-subgroup points to be reordered at nonadjacent nodes or
at distinct nodes with opposite signs.

At adjacent nodes `i` and `j` the root points do not commute. Instead they satisfy the nested
commutator relations `⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and
`⁅⁅x₋ᵢ(t), x₋ⱼ(s)⁆, xⱼ(r)⁆ = x₋ᵢ(t * s * r)`, again over every commutative ring.
The minuscule weight table supplies the square-zero identities
and the Serre relations between the integral generator matrices supply the bracket and
vanishing-product identities that `Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`
turns into the group identity.

## Main results

* `TauCeti.E7Minuscule.commute_rootSubgroupPoints_inl_inl` and `commute_rootSubgroupPoints_inr_inr`:
  root points of the same sign commute at nonadjacent nodes.
* `TauCeti.E7Minuscule.commute_rootSubgroupPoints_inl_inr` and `commute_rootSubgroupPoints_inr_inl`:
  root points of opposite signs commute at distinct nodes.
* `TauCeti.E7Minuscule.commutatorElement_commutatorElement_rootSubgroupPoints_inl` and
  `commutatorElement_commutatorElement_rootSubgroupPoints_inr`: the nested commutator relations at
  adjacent nodes.

## References

* Formalization adapted:
  `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.SimpleRootRelations`.
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
  commute_rootSubgroupPoints_of_lie_eq_zero
    (by simpa only [TauCeti.serreRootGenerator_inl] using
      TauCeti.lie_serreE_serreE_of_eq_zero ℚ CM hij) A s t

/-- Negative numbered simple-root subgroups at nonadjacent nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin 7} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero
    (by simpa only [TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreF_serreF_of_eq_zero ℚ CM hij) A s t

/-- A positive and a negative numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 7} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (by
    simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hij) A s t

/-- A negative and a positive numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 7} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

/-! ## Nested commutators at adjacent nodes -/

section NestedCommutators

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem adjacent_ne {i j : Fin 7} (hij : CM i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.E_diag] at hij
  norm_num at hij

private theorem raising_lie_lie_eq_zero {i j : Fin 7} (hij : CM i j = -1) :
    ⁅raisingMatrix i, ⁅raisingMatrix i, raisingMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_E_E i j

private theorem lowering_lie_lie_eq_zero {i j : Fin 7} (hij : CM i j = -1) :
    ⁅loweringMatrix i, ⁅loweringMatrix i, loweringMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_F_F i j

/-- **The nested commutator relation of positive simple-root points at adjacent nodes**:
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin 7}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by
    rw [(CartanMatrix.E_isSymm 7).apply, hij]
  have hAC := isSerreSystem.lie_E_F_of_ne i j (adjacent_ne hij)
  have hABC : ⁅⁅raisingMatrix i, raisingMatrix j⁆, loweringMatrix j⁆ = raisingMatrix i := by
    rw [isSerreSystem.lie_lie_E_E_F_of_ne (adjacent_ne hij), hji, neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (raisingMatrix i)
    (raisingMatrix j) (loweringMatrix j) (raisingMatrix_mul_self i) (raisingMatrix_mul_self j)
    (loweringMatrix_mul_self j) hAC hABC (raising_lie_lie_eq_zero hij)
    (raising_lie_lie_eq_zero hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])

/-- **The nested commutator relation of negative simple-root points at adjacent nodes**:
`⁅⁅x₋ᵢ(t), x₋ⱼ(s)⁆, xⱼ(r)⁆ = x₋ᵢ(t * s * r)` over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr {i j : Fin 7}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by
    rw [(CartanMatrix.E_isSymm 7).apply, hij]
  have hAC : ⁅loweringMatrix i, raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, isSerreSystem.lie_E_F_of_ne j i (adjacent_ne hji), neg_zero]
  have hABC : ⁅⁅loweringMatrix i, loweringMatrix j⁆, raisingMatrix j⁆ = loweringMatrix i := by
    rw [isSerreSystem.lie_lie_F_F_E_of_ne (adjacent_ne hij), hji, neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (loweringMatrix i)
    (loweringMatrix j) (raisingMatrix j) (loweringMatrix_mul_self i) (loweringMatrix_mul_self j)
    (raisingMatrix_mul_self j) hAC hABC (lowering_lie_lie_eq_zero hij)
    (lowering_lie_lie_eq_zero hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])

end NestedCommutators

end TauCeti.E7Minuscule
