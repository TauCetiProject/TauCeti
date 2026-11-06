/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Rank-one Weyl products in the E₇ minuscule carrier

For a unit `u`, the numbered root word `nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` lies in the
minuscule carrier. Products and quotients of two such words are values of the numbered
simple coroot in its weight torus. These identities fix the coroot normalization at the
group level, over arbitrary commutative rings, including rings with torsion or nilpotents.

The carrier is not identified here with the pinned simply connected group scheme of type E₇.
These identities transfer to that pinned group along a pinning-preserving identification,
once one is proved.

The proofs use `UniversalEnvelopingAlgebra.kostantWeylParam_mul_kostantWeylParam` and
the palindromic inverse-word identity, with the existing minuscule lattice, its Cartan
weight basis, and its represented `sl₂` triples. No new choice of Weyl representatives is
introduced.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "rootGen" => TauCeti.serreRootGenerator weightTable.cartanMatrix
local notation "cartanGen" => TauCeti.serreH ℚ weightTable.cartanMatrix

noncomputable section

universe v

variable (A : Type v) [CommRing A]

-- This comparison is specific to the minuscule carrier's matrix-valued point presentation.
private theorem basisMatrix_rootSubgroupParam (k : Fin 7 ⊕ Fin 7) (t : Multiplicative A) :
    Units.map (LinearMap.toMatrixAlgEquiv (latticeBasis.baseChange A)).toMonoidHom
        (kostantRootSubgroupParam rootGen cartanGen rep lattice.toAddSubgroup
          rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k)
          (CommAlgCat.of ℤ A) t) =
      (rootSubgroupPoints k A t : Matrix.GeneralLinearGroup (Fin 56) A) := by
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_def,
    MonoidHom.comp_apply, kostantRootSubgroupParam_apply]

private theorem basisMatrix_weylParam (i : Fin 7) (u : Aˣ) :
    Units.map (LinearMap.toMatrixAlgEquiv (latticeBasis.baseChange A)).toMonoidHom
        (kostantWeylParam rootGen cartanGen rep lattice.toAddSubgroup
          rep_kostantForm_mem_lattice (isNilpotent_rep_serreRootGenerator (.inl i))
          (isNilpotent_rep_serreRootGenerator (.inr i)) (CommAlgCat.of ℤ A) u) =
      ((rootSubgroupPoints (.inl i) A (.ofAdd (u : A)) *
        rootSubgroupPoints (.inr i) A (.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (.ofAdd (u : A))) :
          Matrix.GeneralLinearGroup (Fin 56) A) := by
  rw [kostantWeylParam_def, map_mul, map_mul,
    basisMatrix_rootSubgroupParam A (.inl i), basisMatrix_rootSubgroupParam A (.inr i)]

private theorem basisMatrix_coordinateCocharacter (i : Fin 7) (u : Aˣ) :
    Units.map (LinearMap.toMatrixAlgEquiv (latticeBasis.baseChange A)).toMonoidHom
        (kostantCoordinateCocharacter lattice.toAddSubgroup latticeBasis e7MinusculeWeight
          A i u) =
      (weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 56) A) := by
  rw [kostantCoordinateCocharacter_apply, coe_weightTorusPoints]
  -- The torus comparison is stated for the multiplicative equivalence on units; here the
  -- same coordinate map is bundled as a monoid homomorphism so it also transports products.
  exact basisMatrix_kostantTorusPoints lattice.toAddSubgroup latticeBasis e7MinusculeWeight _

/-- Products of unit-parameter Weyl words are numbered simple-coroot values:
`nᵢ(u) nᵢ(v) = hᵢ(-u v⁻¹)`. The equality is inside the minuscule carrier itself. -/
theorem rootSubgroupPoints_weyl_mul (i : Fin 7) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (.ofAdd (u : A)) *
      rootSubgroupPoints (.inr i) A (.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (.ofAdd (u : A))) *
    (rootSubgroupPoints (.inl i) A (.ofAdd (v : A)) *
      rootSubgroupPoints (.inr i) A (.ofAdd (-((v⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (.ofAdd (v : A))) =
      weightTorusPoints A (Pi.mulSingle i (-(u * v⁻¹))) := by
  have h := kostantWeylParam_mul_kostantWeylParam rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice
    (isNilpotent_rep_serreRootGenerator (.inl i))
    (isNilpotent_rep_serreRootGenerator (.inr i))
    latticeBasis e7MinusculeWeight isCartanWeightVector_latticeBasis
    (isSl2Triple_rep_serreRootGenerator i)
    (α := fun j ↦ CartanMatrix.E 7 i j)
    (by
      intro j
      rw [weightTable_cartanMatrix, TauCeti.serreRootGenerator_inl, TauCeti.lie_serreH_serreE,
        (CartanMatrix.E_isSymm 7).apply]
      simp only [Int.cast_smul_eq_zsmul])
    (by
      intro j
      rw [weightTable_cartanMatrix, TauCeti.serreRootGenerator_inr, TauCeti.lie_serreH_serreF,
        (CartanMatrix.E_isSymm 7).apply]
      simp only [Int.cast_smul_eq_zsmul])
    (CommAlgCat.of ℤ A) u v
  apply Subtype.val_injective
  simpa only [map_mul, basisMatrix_weylParam, basisMatrix_coordinateCocharacter,
    Subgroup.coe_mul] using congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (latticeBasis.baseChange A)).toMonoidHom) h

/-- Quotients of unit-parameter Weyl words are numbered simple-coroot values:
`nᵢ(u) nᵢ(v)⁻¹ = hᵢ(u v⁻¹)`. In particular, setting `v = 1` recovers the coroot from
root-subgroup words over an arbitrary commutative coefficient ring. -/
theorem rootSubgroupPoints_weyl_mul_inv (i : Fin 7) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (.ofAdd (u : A)) *
      rootSubgroupPoints (.inr i) A (.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (.ofAdd (u : A))) *
    (rootSubgroupPoints (.inl i) A (.ofAdd (v : A)) *
      rootSubgroupPoints (.inr i) A (.ofAdd (-((v⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (.ofAdd (v : A)))⁻¹ =
      weightTorusPoints A (Pi.mulSingle i (u * v⁻¹)) := by
  simpa only [mul_inv_rev, ← map_inv, ← ofAdd_neg, inv_neg,
    Units.val_neg, neg_neg, mul_neg, mul_assoc] using rootSubgroupPoints_weyl_mul A i u (-v)

end

end TauCeti.E7Minuscule
