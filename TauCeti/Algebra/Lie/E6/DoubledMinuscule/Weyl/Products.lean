/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Coordinate

/-!
# Unit-parameter Weyl products in the doubled E₆ carrier

For the numbered positive and negative simple-root maps of the doubled minuscule carrier,
write `nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)`. This file identifies the products
`nᵢ(u) nᵢ(v)⁻¹` and `nᵢ(u) nᵢ(v)` with the corresponding coordinate values of the
represented weight torus. The identities fix the group-level normalization of the simple
coroots against the root parameters, over every commutative coefficient ring.

The quotient identity transports
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_mul_inv_kostantWeylParam`
through the doubled carrier's admissible lattice basis; the product identity follows by
inversion of the second root word. No identification with an independently pinned simply
connected group scheme is asserted.

## Main results

* `TauCeti.E6DoubledMinuscule.rootSubgroupPoints_weylWord_mul_inv`:
  `nᵢ(u) nᵢ(v)⁻¹ = hᵢ(u v⁻¹)`.
* `TauCeti.E6DoubledMinuscule.rootSubgroupPoints_weylWord_mul`:
  `nᵢ(u) nᵢ(v) = hᵢ(-u v⁻¹)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.2.
-/

public section

namespace TauCeti.E6DoubledMinuscule

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

private noncomputable abbrev rootGen := TauCeti.serreRootGenerator (CartanMatrix.E 6).transpose
private noncomputable abbrev cartanGen := TauCeti.serreH ℚ (CartanMatrix.E 6).transpose

/-- Quotients of unit-parameter pinned Weyl words are simple-coroot values:
`nᵢ(u) nᵢ(v)⁻¹ = hᵢ(u v⁻¹)`. The coroot is the coordinate cocharacter of the
carrier's represented rank-six weight torus. -/
theorem rootSubgroupPoints_weylWord_mul_inv (A : Type*) [CommRing A]
    (i : Fin 6) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)))⁻¹ =
      weightTorusPoints A (Pi.mulSingle i (u * v⁻¹)) := by
  have hneg : ∀ j, ⁅cartanGen j, rootGen (.inr i)⁆ =
      -((E6.rootGeneratorWeight (.inl i) j : ℚ) • rootGen (.inr i)) := by
    intro j
    rw [E6.lie_serreH_rootGenerator, E6.rootGeneratorWeight_inr_eq_neg_inl]
    simp
  have h := kostantWeylParam_mul_inv_kostantWeylParam rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice
    (isNilpotent_rep_serreRootGenerator (.inl i))
    (isNilpotent_rep_serreRootGenerator (.inr i)) matrixBasis matrixWeight
    isCartanWeightVector_matrixBasis (isSl2Triple_rep_serreRootGenerator i)
    (E6.lie_serreH_rootGenerator (.inl i)) hneg (CommAlgCat.of ℤ A) u v
  rw [kostantCoordinateCocharacter_apply] at h
  have hm := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (matrixBasis.baseChange A)).toMonoidHom) h
  rw [MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantTorusPoints lattice.toAddSubgroup matrixBasis matrixWeight
      (Pi.mulSingle i (u * v⁻¹))] at hm
  apply Subtype.ext
  simpa only [kostantWeylParam_def, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_rootSubgroupPoints, coe_weightTorusPoints,
    basisMatrix_kostantRootSubgroupParam rootGen cartanGen rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis A] using hm

/-- Products of unit-parameter pinned Weyl words are simple-coroot values:
`nᵢ(u) nᵢ(v) = hᵢ(-u v⁻¹)`, including their signs on both minuscule summands. -/
theorem rootSubgroupPoints_weylWord_mul (A : Type*) [CommRing A]
    (i : Fin 6) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A))) =
      weightTorusPoints A (Pi.mulSingle i (-(u * v⁻¹))) := by
  simpa only [inv_neg, Units.val_neg, neg_neg, mul_neg, ofAdd_neg, map_inv,
    mul_inv_rev, inv_inv, mul_assoc] using rootSubgroupPoints_weylWord_mul_inv A i u (-v)

end TauCeti.E6DoubledMinuscule
