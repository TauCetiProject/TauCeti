/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Unit-parameter Weyl products in the minuscule E₆ carrier

For a numbered simple root, put `nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)`. Products and quotients
of these words recover the numbered coroot in the full weight torus:
`nᵢ(u)nᵢ(v) = hᵢ(-uv⁻¹)` and `nᵢ(u)nᵢ(v)⁻¹ = hᵢ(uv⁻¹)`.
These identities normalize the group-level coroot parameters, not just their differentials.
They hold inside the explicit 27-dimensional carrier over every commutative value ring.

Taking `v = 1` in the quotient identity recovers `hᵢ(u) = nᵢ(u)nᵢ(1)⁻¹`, fixing
which unit parameter in the numbered weight torus corresponds to the simple coroot.
Thus the coroot values can be expressed using only the corresponding positive and negative
simple-root subgroups. No identification with an independently pinned simply connected
group scheme is asserted.

## References

* Formal rank-one product identity:
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_mul_kostantWeylParam`.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.E6Minuscule

open TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)

universe v

private noncomputable def basisMatrix (A : Type v) [CommRing A] :
    LinearMap.GeneralLinearGroup A (A ⊗[ℤ] Λ) →*
      Matrix.GeneralLinearGroup (Fin 27) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv ((𝓑).baseChange A)).toMonoidHom)

private theorem basisMatrix_root (A : Type v) [CommRing A]
    (k : Fin 6 ⊕ Fin 6) (t : Multiplicative A) :
    basisMatrix A
        (kostantRootSubgroupParam (serreRootGenerator weightTable.cartanMatrix)
          (serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
          weightTable.rep_kostantForm_mem_lattice k
          (weightTable.isNilpotent_rep_serreRootGenerator k) (CommAlgCat.of ℤ A) t) =
      (rootSubgroupPoints k A t : Matrix.GeneralLinearGroup (Fin 27) A) := by
  simpa only [basisMatrix, coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using
    basisMatrix_kostantRootSubgroupParam (serreRootGenerator weightTable.cartanMatrix)
      (serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
      weightTable.rep_kostantForm_mem_lattice weightTable.isNilpotent_rep_serreRootGenerator
      𝓑 A k t

private theorem basisMatrix_coroot (A : Type v) [CommRing A] (i : Fin 6) (u : Aˣ) :
    basisMatrix A (kostantCoordinateCocharacter (Λ).toAddSubgroup 𝓑 weightTable.weight
        A i u) =
      (weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 27) A) := by
  simpa only [kostantCoordinateCocharacter_apply, basisMatrix, coe_weightTorusPoints,
    MulEquiv.toMonoidHom_eq_coe] using
    basisMatrix_kostantTorusPoints (Λ).toAddSubgroup 𝓑 weightTable.weight
      (A := A) (Pi.mulSingle i u)

private theorem basisMatrix_weylParam (A : Type v) [CommRing A] (i : Fin 6) (u : Aˣ) :
    basisMatrix A
        (kostantWeylParam (serreRootGenerator weightTable.cartanMatrix)
          (serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
          weightTable.rep_kostantForm_mem_lattice
          (weightTable.isNilpotent_rep_serreRootGenerator (.inl i))
          (weightTable.isNilpotent_rep_serreRootGenerator (.inr i)) (CommAlgCat.of ℤ A) u) =
      ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
          rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
          rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) : points A) :
        Matrix.GeneralLinearGroup (Fin 27) A) := by
  simp only [kostantWeylParam_def, map_mul, Subgroup.coe_mul]
  rw [basisMatrix_root A (.inl i) (Multiplicative.ofAdd (u : A)),
    basisMatrix_root A (.inr i) (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A)))]

/-- Products of two unit-parameter Weyl words are the simple-coroot value at `-uv⁻¹`. -/
-- Match the word before simplification rewrites inverses into the root parameters.
@[simp↓]
theorem rootSubgroupPoints_weyl_mul (A : Type v) [CommRing A] (i : Fin 6) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A))) =
      weightTorusPoints A (Pi.mulSingle i (-(u * v⁻¹))) := by
  have htriple := weightTable.isSl2Triple_rep_serreRootGenerator i (by
    obtain ⟨a, ha⟩ := DynkinType.exists_e6MinusculeWeight_apply_eq_neg_one i
    exact ⟨a, by simpa only [weightTable_weight, ha] using (neg_ne_zero.mpr (one_ne_zero :
      (1 : ℤ) ≠ 0))⟩)
  have h := kostantWeylParam_mul_kostantWeylParam
    (serreRootGenerator weightTable.cartanMatrix) (serreH ℚ weightTable.cartanMatrix)
    weightTable.rep (Λ).toAddSubgroup weightTable.rep_kostantForm_mem_lattice
    (weightTable.isNilpotent_rep_serreRootGenerator (.inl i))
    (weightTable.isNilpotent_rep_serreRootGenerator (.inr i)) 𝓑 weightTable.weight
    weightTable.isCartanWeightVector_coordinateLatticeBasis htriple
    (fun j => lie_serreH_serreRootGenerator_inl weightTable.cartanMatrix i j)
    (fun j => by
      simpa only [Int.cast_neg, neg_smul] using
        lie_serreH_serreRootGenerator_inr weightTable.cartanMatrix i j)
    (CommAlgCat.of ℤ A) u v
  apply Subtype.ext
  simpa only [map_mul, basisMatrix_weylParam, basisMatrix_coroot, Subgroup.coe_mul] using
    congrArg (basisMatrix A) h

/-- Quotients of unit-parameter Weyl words are the simple-coroot value at `uv⁻¹`.
In particular, quotienting by the parameter-one word recovers the coroot at `u`. -/
-- Match the quotient before simplification distributes its inverse over the root word.
@[simp↓]
theorem rootSubgroupPoints_weyl_mul_inv (A : Type v) [CommRing A] (i : Fin 6) (u v : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (v : A)))⁻¹ =
      weightTorusPoints A (Pi.mulSingle i (u * v⁻¹)) := by
  simpa only [mul_inv_rev, ← map_inv, ← ofAdd_neg, inv_neg, Units.val_neg, neg_neg,
    mul_neg, mul_assoc] using rootSubgroupPoints_weyl_mul A i u (-v)

end TauCeti.E6Minuscule
