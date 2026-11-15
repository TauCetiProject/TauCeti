/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Weyl

/-!
# Pinned rank-one words in the integral short-root G₂ carrier

The representative `simpleWeylPoint i A`, defined in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Weyl`, is `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the
numbered simple pinning. Its matrix is a constant signed permutation matrix, and its inverse
matrix is its transpose. These words fix the signs of the nonsimple root parametrizations in the
root relations.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

noncomputable section

/-- The pinned word agrees with the generic Kostant Weyl representative as a general-linear
point, so the generic conjugation and normalizer results apply through this comparison. -/
theorem coe_simpleWeylPoint_eq_kostantToralWeylPoint (i : Fin 2) (A : Type v) [CommRing A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) =
      (TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint
        (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂)
        rep lattice.toAddSubgroup rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator
        latticeBasis weight (.inl i) (.inr i) A : Matrix.GeneralLinearGroup (Fin 7) A) := by
  simp only [simpleWeylPoint_def,
    TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_def, Subgroup.coe_mul,
    coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix,
    TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints]

/-- The integral signed permutation matrix of the pinned rank-one word at each node. -/
def simpleWeylPointMatrix : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ :=
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
theorem simpleWeylPointMatrix_zero :
    simpleWeylPointMatrix 0 =
      !![0, 1, 0, 0, 0, 0, 0;
         -1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, -1, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, -1, 0] := (rfl)

/-- The integral matrix of the long-node rank-one word. -/
theorem simpleWeylPointMatrix_one :
    simpleWeylPointMatrix 1 =
      !![1, 0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, -1, 0, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, -1, 0, 0;
         0, 0, 0, 0, 0, 0, 1] := (rfl)

private theorem simpleWeylPointMatrix_formula (i : Fin 2) :
    (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) *
      (1 - rootMatrix (.inr i) + rootDividedSquareMatrix (.inr i)) *
      (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) =
        simpleWeylPointMatrix i := by
  fin_cases i <;>
    simp only [rootMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inl,
      rootDividedSquareMatrix_inr] <;> decide +kernel

/-- Each integral rank-one-word matrix has its transpose as a right inverse. -/
@[simp]
theorem simpleWeylPointMatrix_mul_transpose (i : Fin 2) :
    simpleWeylPointMatrix i * (simpleWeylPointMatrix i).transpose = 1 := by
  fin_cases i <;> decide +kernel

/-- The numbered rank-one words are the following constant signed permutation matrices. -/
@[simp]
theorem coe_simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] :
    ((simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (simpleWeylPointMatrix i).map (Int.castRingHom A) := by
  simp only [simpleWeylPoint_def, Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints,
    toAdd_ofAdd, one_smul, neg_one_smul, neg_one_sq, one_pow]
  have h := congrArg (fun m : Matrix (Fin 7) (Fin 7) ℤ => m.map (Int.castRingHom A))
    (simpleWeylPointMatrix_formula i)
  simp only [Matrix.map_mul, Matrix.map_add _ (map_add _),
    Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)] at h
  simpa only [Int.coe_castRingHom, sub_eq_add_neg] using h

/-- The inverse of a pinned rank-one word has the transpose matrix. -/
-- Not a simp lemma: Matrix.coe_units_inv and coe_simpleWeylPoint already simplify its left side.
theorem coe_simpleWeylPoint_inv (i : Fin 2) (A : Type v) [CommRing A] :
    (((simpleWeylPoint i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
      ((simpleWeylPointMatrix i).map (Int.castRingHom A)).transpose := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_simpleWeylPoint, ← Matrix.transpose_map, ← Matrix.map_mul,
    simpleWeylPointMatrix_mul_transpose,
    Matrix.map_one _ (map_zero _) (map_one _)]

end

end TauCeti.G2ShortRoot.IntegralToralClosure
