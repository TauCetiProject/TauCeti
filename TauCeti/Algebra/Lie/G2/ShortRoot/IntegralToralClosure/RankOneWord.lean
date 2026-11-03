/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Pinned rank-one words in the integral short-root G₂ carrier

The word `rankOneWord i A` is `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the numbered simple pinning.
Its matrix is a constant signed permutation matrix, and its inverse matrix is its transpose.
These words fix the signs of the nonsimple root parametrizations in the root relations.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

noncomputable section

/-- The pinned rank-one word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)`. Node zero is short and node one long. -/
def rankOneWord (i : Fin 2) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The rank-one word is the product prescribed by the numbered simple pinning. -/
theorem rankOneWord_def (i : Fin 2) (A : Type v) [CommRing A] :
    rankOneWord i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) := (rfl)

/-- The integral signed permutation matrix of the pinned rank-one word at each node. -/
def rankOneWordMatrix : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, -1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, -1, 0],
    !![1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 0, 1]]

/-- The integral matrix of the short-node rank-one word. -/
@[simp]
theorem rankOneWordMatrix_zero :
    rankOneWordMatrix 0 =
      !![0, 1, 0, 0, 0, 0, 0;
         -1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, -1, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, -1, 0] := (rfl)

/-- The integral matrix of the long-node rank-one word. -/
@[simp]
theorem rankOneWordMatrix_one :
    rankOneWordMatrix 1 =
      !![1, 0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, -1, 0, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, -1, 0, 0;
         0, 0, 0, 0, 0, 0, 1] := (rfl)

private theorem rankOneWordMatrix_formula (i : Fin 2) :
    (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) *
      (1 - rootMatrix (.inr i) + rootDividedSquareMatrix (.inr i)) *
      (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) =
        rankOneWordMatrix i := by
  fin_cases i <;>
    simp only [rootMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inl,
      rootDividedSquareMatrix_inr] <;> decide +kernel

/-- Each integral rank-one-word matrix has its transpose as a right inverse. -/
theorem rankOneWordMatrix_mul_transpose (i : Fin 2) :
    rankOneWordMatrix i * (rankOneWordMatrix i).transpose = 1 := by
  fin_cases i <;> decide +kernel

/-- The numbered rank-one words are the following constant signed permutation matrices. -/
@[simp]
theorem coe_rankOneWord (i : Fin 2) (A : Type v) [CommRing A] :
    ((rankOneWord i A : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (rankOneWordMatrix i).map (Int.castRingHom A) := by
  simp only [rankOneWord_def, Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints,
    toAdd_ofAdd, one_smul, neg_one_smul, neg_one_sq, one_pow]
  have h := congrArg (fun m : Matrix (Fin 7) (Fin 7) ℤ => m.map (Int.castRingHom A))
    (rankOneWordMatrix_formula i)
  simp only [Matrix.map_mul, Matrix.map_add _ (map_add _),
    Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)] at h
  simpa only [Int.coe_castRingHom, sub_eq_add_neg] using h

/-- The inverse of a pinned rank-one word has the transpose matrix. -/
-- Not a simp lemma: Matrix.coe_units_inv and coe_rankOneWord already simplify its left side.
theorem coe_rankOneWord_inv (i : Fin 2) (A : Type v) [CommRing A] :
    (((rankOneWord i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
      ((rankOneWordMatrix i).map (Int.castRingHom A)).transpose := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_rankOneWord, ← Matrix.transpose_map, ← Matrix.map_mul,
    rankOneWordMatrix_mul_transpose,
    Matrix.map_one _ (map_zero _) (map_one _)]

end

end TauCeti.G2ShortRoot.IntegralToralClosure
