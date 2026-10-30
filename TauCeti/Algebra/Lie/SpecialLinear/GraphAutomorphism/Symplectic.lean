/-
Copyright (c) 2026 Robert Boyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Boyer
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import TauCeti.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The native type-A reversal form in symplectic coordinates

For the native type-`A_(2k+1)` conjugator `Q`, the matrix dimension is `2(k+1)`.
Pair each index in the lower half with its reversal, then multiply the second
vector in the pair by the alternating sign of the first. The inverse form `Q⁻¹`
has Gram matrix `Matrix.J`, whose upper-right block is negative, in these coordinates.

`typeAGraphSkewAdjointSymplecticEquiv` identifies the skew-adjoint Lie algebra for
the literal inverse matrix with Mathlib's native symplectic Lie algebra. Its two
matrix-value theorems specify the change of coordinates and its inverse.
The construction works over every commutative ring, including characteristic two.
-/

public section

open Matrix

namespace TauCeti

variable (k : ℕ) (A : Type*) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Pair the lower half of the native indices with their reversals. -/
def typeASymplecticIndex :
    Fin (k + 1) ⊕ Fin (k + 1) ≃ Fin (2 * k + 1 + 1) :=
  finSumFinRevEquiv (k + 1) (k + 1) (2 * k + 1 + 1) (by omega)

/-- The first index of each pair is the original lower-half index. -/
@[simp]
theorem typeASymplecticIndex_inl_val (i : Fin (k + 1)) :
    (typeASymplecticIndex k (Sum.inl i) : ℕ) = i := by
  simp [typeASymplecticIndex]

/-- The second index of each pair is its reversal in the full matrix. -/
@[simp]
theorem typeASymplecticIndex_inr_val (i : Fin (k + 1)) :
    (typeASymplecticIndex k (Sum.inr i) : ℕ) = 2 * k + 1 - i := by
  rw [typeASymplecticIndex, finSumFinRevEquiv_inr_val]
  omega

/-- Reversal exchanges the two indices of a pair. -/
@[simp]
theorem rev_typeASymplecticIndex_inl (i : Fin (k + 1)) :
    (typeASymplecticIndex k (Sum.inl i)).rev =
      typeASymplecticIndex k (Sum.inr i) := by
  apply Fin.ext
  simp [Fin.val_rev]

/-- Reversal takes the second index back to the first. -/
@[simp]
theorem rev_typeASymplecticIndex_inr (i : Fin (k + 1)) :
    (typeASymplecticIndex k (Sum.inr i)).rev =
      typeASymplecticIndex k (Sum.inl i) := by
  rw [← rev_typeASymplecticIndex_inl, Fin.rev_rev]

/-- The diagonal sign change in paired coordinates: `1` on the first copy and
`(-1)^i` on the second. -/
def typeASymplecticDiagonal :
    Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) A :=
  diagonal (Sum.elim (fun _ ↦ 1) (fun i ↦ (-1 : A) ^ (i : ℕ)))

/-- The coordinate sign change is the diagonal matrix of alternating signs. -/
theorem typeASymplecticDiagonal_def :
    typeASymplecticDiagonal k A =
      diagonal (Sum.elim (fun _ : Fin (k + 1) ↦ 1)
        (fun i : Fin (k + 1) ↦ (-1 : A) ^ (i : ℕ))) := by
  rfl

/-- The sign change fixes each vector in the first copy. -/
@[simp]
theorem typeASymplecticDiagonal_apply_inl_inl (i : Fin (k + 1)) :
    typeASymplecticDiagonal k A (Sum.inl i) (Sum.inl i) = 1 := by
  simp [typeASymplecticDiagonal_def]

/-- The sign on the second copy alternates with the index. -/
@[simp]
theorem typeASymplecticDiagonal_apply_inr_inr (i : Fin (k + 1)) :
    typeASymplecticDiagonal k A (Sum.inr i) (Sum.inr i) = (-1 : A) ^ (i : ℕ) := by
  simp [typeASymplecticDiagonal_def]

/-- The coordinate sign change is symmetric. -/
@[simp]
theorem typeASymplecticDiagonal_transpose :
    (typeASymplecticDiagonal k A)ᵀ = typeASymplecticDiagonal k A := by
  simp [typeASymplecticDiagonal_def]

/-- Applying the coordinate sign change twice is the identity. -/
@[simp]
theorem typeASymplecticDiagonal_mul_self :
    typeASymplecticDiagonal k A * typeASymplecticDiagonal k A = 1 := by
  rw [typeASymplecticDiagonal_def, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  cases i <;> simp [← pow_add, ← two_mul, pow_mul]

/-- The nonsingular inverse of the coordinate sign change is itself. -/
@[simp]
theorem typeASymplecticDiagonal_inv :
    (typeASymplecticDiagonal k A)⁻¹ = typeASymplecticDiagonal k A :=
  Matrix.inv_eq_left_inv (typeASymplecticDiagonal_mul_self k A)

private theorem typeASymplectic_sign_product (i : Fin (k + 1)) :
    (-1 : A) ^ (typeASymplecticIndex k (Sum.inr i) : ℕ) * (-1 : A) ^ (i : ℕ) =
      -1 := by
  rw [← pow_add]
  have h : (typeASymplecticIndex k (Sum.inr i) : ℕ) + i = 2 * k + 1 := by
    rw [typeASymplecticIndex_inr_val]
    omega
  rw [h, pow_add, pow_mul]
  simp

/-- In the explicit paired and signed coordinates, the inverse native reversal
form is exactly Mathlib's symplectic form, with no scalar factor. -/
theorem typeASymplecticDiagonal_transpose_mul_reindex_typeAGraphConjugator_inv_mul_eq_J :
    (typeASymplecticDiagonal k A)ᵀ *
        reindex (typeASymplecticIndex k).symm (typeASymplecticIndex k).symm
          (typeAGraphConjugator (2 * k + 1) A :
            Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) A)⁻¹ *
        typeASymplecticDiagonal k A = Matrix.J (Fin (k + 1)) A := by
  rw [typeASymplecticDiagonal_transpose, typeAGraphConjugator_inv_eq_transpose]
  ext a b
  simp only [typeASymplecticDiagonal_def, diagonal_mul, mul_diagonal, reindex_apply,
    submatrix_apply, Equiv.symm_symm, transpose_apply, typeAGraphConjugator_apply]
  rcases a with i | i <;> rcases b with j | j
  · simp [Matrix.J]
  · by_cases h : i = j
    · subst j
      simpa [Matrix.J] using typeASymplectic_sign_product k A i
    · simp [Matrix.J, h]
  · by_cases h : i = j
    · subst j
      simp [Matrix.J, ← pow_add, ← two_mul, pow_mul]
    · simp [Matrix.J, h]
  · simp [Matrix.J]

/-- Reindexing and diagonal conjugation identify the skew-adjoint Lie algebra for
the inverse native type-`A_(2k+1)` reversal form with the native symplectic Lie algebra. -/
noncomputable def typeAGraphSkewAdjointSymplecticEquiv :
    skewAdjointMatricesLieSubalgebra
        (typeAGraphConjugator (2 * k + 1) A :
          Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) A)⁻¹ ≃ₗ⁅A⁆
      LieAlgebra.Symplectic.sp (Fin (k + 1)) A :=
  (skewAdjointMatricesLieSubalgebraEquivTranspose _
    (reindexAlgEquiv A A (typeASymplecticIndex k).symm)
    (by
      intro X
      rw [coe_reindexAlgEquiv]
      exact transpose_reindex _ _ X)).trans
    ((skewAdjointMatricesLieSubalgebraEquiv _
      (typeASymplecticDiagonal k A)
      ⟨typeASymplecticDiagonal k A, typeASymplecticDiagonal_mul_self k A,
        typeASymplecticDiagonal_mul_self k A⟩).trans
      (LieEquiv.ofEq _ (LieAlgebra.Symplectic.sp (Fin (k + 1)) A) (by
        unfold LieAlgebra.Symplectic.sp
        rw [coe_reindexAlgEquiv,
          typeASymplecticDiagonal_transpose_mul_reindex_typeAGraphConjugator_inv_mul_eq_J])))

/-- The forward map is reindexing followed by the explicit diagonal conjugation. -/
@[simp]
theorem typeAGraphSkewAdjointSymplecticEquiv_apply_val
    (X : skewAdjointMatricesLieSubalgebra
      (typeAGraphConjugator (2 * k + 1) A :
        Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) A)⁻¹) :
    (typeAGraphSkewAdjointSymplecticEquiv k A X :
        Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) A) =
      typeASymplecticDiagonal k A *
        reindex (typeASymplecticIndex k).symm (typeASymplecticIndex k).symm
          (X : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) A) *
        typeASymplecticDiagonal k A := by
  rw [typeAGraphSkewAdjointSymplecticEquiv, LieEquiv.trans_apply, LieEquiv.trans_apply,
    LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply,
    skewAdjointMatricesLieSubalgebraEquivTranspose_apply, typeASymplecticDiagonal_inv]
  simp only [coe_reindexAlgEquiv]

/-- The inverse map conjugates by the same diagonal matrix and undoes the index change. -/
@[simp]
theorem typeAGraphSkewAdjointSymplecticEquiv_symm_apply_val
    (Y : LieAlgebra.Symplectic.sp (Fin (k + 1)) A) :
    ((typeAGraphSkewAdjointSymplecticEquiv k A).symm Y :
        Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) A) =
      reindex (typeASymplecticIndex k) (typeASymplecticIndex k)
        (typeASymplecticDiagonal k A *
          (Y : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) A) *
          typeASymplecticDiagonal k A) := by
  apply (reindex (typeASymplecticIndex k).symm (typeASymplecticIndex k).symm).injective
  have h := typeAGraphSkewAdjointSymplecticEquiv_apply_val k A
    ((typeAGraphSkewAdjointSymplecticEquiv k A).symm Y)
  rw [LieEquiv.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc, ← mul_assoc (typeASymplecticDiagonal k A)
    (typeASymplecticDiagonal k A)]

end TauCeti
