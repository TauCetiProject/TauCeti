/-
Copyright (c) 2026 Robert Boyer and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.SkewAdjoint
public import TauCeti.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The odd-dimensional type-A reversal in split orthogonal coordinates

When two is invertible, the inverse signed reversal form in dimension `2 * k + 1`
is similar to Mathlib's split type-B form `LieAlgebra.Orthogonal.JB`.
The explicit coordinates put the middle
vector first, followed by the lower-half vectors and their reversals. A diagonal
change of basis gives the scalar multiple `2 * (-1)^k` of `JB`, not the identity
Gram matrix. Thus no square root of a scalar is required.

With the same invertibility hypothesis, `typeAGraphSkewAdjointOrthogonalEquiv`
constructs the resulting Lie equivalence, and `typeASpecialLinearFixedOrthogonalEquiv`
identifies the fixed
Lie algebra of the pinned type-`A_(2k)` graph automorphism with the native split
orthogonal algebra. This includes `k = 0` and works over commutative rings.

The construction adapts Robert Boyer's paired-coordinate method and equivalence
proofs in `typeAGraphSkewAdjointSymplecticEquiv`, with a scalar similarity in odd dimension.
See V. G. Kac, *Infinite dimensional Lie algebras*, §7.9, for diagram folding, and
Mathlib's `LieAlgebra.Orthogonal.typeB` for the split-form convention.
-/

public section

open Matrix

namespace TauCeti

variable (k : ℕ) (A : Type*) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Put the middle vector first, then pair each lower-half index with its reversal. -/
def typeAOrthogonalIndex : Unit ⊕ (Fin k ⊕ Fin k) ≃ Fin (2 * k + 1) :=
  ((Equiv.sumAssoc Unit (Fin k) (Fin k)).symm.trans
    (Equiv.sumCongr
      (((Equiv.sumComm Unit (Fin k)).trans
        (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1)))).trans
          finSumFinEquiv)
      (Equiv.refl _))).trans
    (finSumFinRevEquiv (k + 1) k (2 * k + 1) (by omega))

/-- The distinguished vector is the middle coordinate. -/
@[simp]
theorem typeAOrthogonalIndex_inl_val (u : Unit) :
    (typeAOrthogonalIndex k (Sum.inl u) : ℕ) = k := by
  simp [typeAOrthogonalIndex]

/-- The first isotropic copy is the lower half of the original coordinates. -/
@[simp]
theorem typeAOrthogonalIndex_inr_inl_val (i : Fin k) :
    (typeAOrthogonalIndex k (Sum.inr (Sum.inl i)) : ℕ) = i := by
  simp [typeAOrthogonalIndex]

/-- The second isotropic copy consists of the reversed lower-half coordinates. -/
@[simp]
theorem typeAOrthogonalIndex_inr_inr_val (i : Fin k) :
    (typeAOrthogonalIndex k (Sum.inr (Sum.inr i)) : ℕ) = 2 * k - i := by
  simp [typeAOrthogonalIndex]
  omega

/-- Reversal fixes the middle vector. -/
@[simp]
theorem rev_typeAOrthogonalIndex_inl (u : Unit) :
    (typeAOrthogonalIndex k (Sum.inl u)).rev = typeAOrthogonalIndex k (Sum.inl u) := by
  apply Fin.ext
  simp only [Fin.val_rev, typeAOrthogonalIndex_inl_val]
  omega

/-- Reversal exchanges the two isotropic copies. -/
@[simp]
theorem rev_typeAOrthogonalIndex_inr_inl (i : Fin k) :
    (typeAOrthogonalIndex k (Sum.inr (Sum.inl i))).rev =
      typeAOrthogonalIndex k (Sum.inr (Sum.inr i)) := by
  apply Fin.ext
  simp [Fin.val_rev]

/-- Reversing the second copy returns to the first. -/
@[simp]
theorem rev_typeAOrthogonalIndex_inr_inr (i : Fin k) :
    (typeAOrthogonalIndex k (Sum.inr (Sum.inr i))).rev =
      typeAOrthogonalIndex k (Sum.inr (Sum.inl i)) := by
  rw [← rev_typeAOrthogonalIndex_inr_inl, Fin.rev_rev]

/-- Scale the middle vector by two and the second isotropic copy by signed twos. -/
def typeAOrthogonalDiagonal :
    Matrix (Unit ⊕ (Fin k ⊕ Fin k)) (Unit ⊕ (Fin k ⊕ Fin k)) A :=
  diagonal (Sum.elim (fun _ ↦ 2)
    (Sum.elim (fun _ ↦ 1) (fun i ↦ 2 * (-1 : A) ^ (k + (i : ℕ)))))

/-- The explicit entries of the diagonal coordinate change. -/
theorem typeAOrthogonalDiagonal_def :
    typeAOrthogonalDiagonal k A =
      diagonal (Sum.elim (fun _ : Unit ↦ 2)
        (Sum.elim (fun _ : Fin k ↦ 1) (fun i : Fin k ↦ 2 * (-1 : A) ^ (k + (i : ℕ))))) :=
  (rfl)

private theorem typeAOrthogonal_sign_product (i : Fin k) :
    (-1 : A) ^ (typeAOrthogonalIndex k (Sum.inr (Sum.inr i)) : ℕ) *
        (-1 : A) ^ (k + (i : ℕ)) = (-1 : A) ^ k := by
  rw [← pow_add]
  have h : (typeAOrthogonalIndex k (Sum.inr (Sum.inr i)) : ℕ) + (k + i) = 2 * k + k := by
    rw [typeAOrthogonalIndex_inr_inr_val]
    omega
  rw [h, pow_add, pow_mul]
  simp

/-- The paired coordinates and diagonal scaling give exactly a scalar multiple of
Mathlib's split type-B form. This is a similarity, not an isometry to `JB`. -/
theorem typeAOrthogonalDiagonal_transpose_mul_reindex_typeAGraphConjugator_inv_mul :
    (typeAOrthogonalDiagonal k A)ᵀ *
        reindex (typeAOrthogonalIndex k).symm (typeAOrthogonalIndex k).symm
          (typeAGraphConjugator (2 * k) A :
            Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) A)⁻¹ *
        typeAOrthogonalDiagonal k A =
      (2 * (-1 : A) ^ k) • LieAlgebra.Orthogonal.JB (Fin k) A := by
  rw [typeAGraphConjugator_inv_eq_transpose]
  ext a b
  simp only [typeAOrthogonalDiagonal_def, diagonal_transpose, diagonal_mul, mul_diagonal,
    reindex_apply, submatrix_apply, Equiv.symm_symm, transpose_apply, typeAGraphConjugator_apply]
  rcases a with u | (i | i) <;> rcases b with v | (j | j)
  all_goals simp only [Sum.elim_inl, Sum.elim_inr]
  all_goals try (solve | simp [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
    mul_assoc, mul_left_comm, mul_comm])
  · suffices h :
        (if i = j then (-1 : A) ^ (k + (j : ℕ)) * (2 * (-1 : A) ^ (2 * k - j)) else 0) =
          (-1 : A) ^ k * (2 * (1 : Matrix (Fin k) (Fin k) A) i j) by
      simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
        mul_assoc, mul_left_comm, mul_comm, Nat.mul_comm 2 k] using h
    by_cases h : i = j
    · subst j
      simp only [ite_true, one_apply_eq, mul_one]
      have hs := typeAOrthogonal_sign_product k A i
      simp only [typeAOrthogonalIndex_inr_inr_val] at hs
      linear_combination 2 * hs
    · simp [h]
  · suffices h :
        (if i = j then (-1 : A) ^ (j : ℕ) * ((-1 : A) ^ (k + (i : ℕ)) * 2) else 0) =
          (-1 : A) ^ k * (2 * (1 : Matrix (Fin k) (Fin k) A) i j) by
      simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
        mul_assoc, mul_left_comm, mul_comm] using h
    by_cases h : i = j
    · subst j
      simp only [ite_true, one_apply_eq, mul_one]
      rw [← mul_assoc, ← pow_add]
      have hsum : (i : ℕ) + (k + i) = 2 * i + k := by omega
      rw [hsum, pow_add, pow_mul]
      simp
    · simp [h]

variable [Invertible (2 : A)]

/-- The coordinate change is invertible as soon as two is invertible. -/
theorem isUnit_typeAOrthogonalDiagonal : IsUnit (typeAOrthogonalDiagonal k A) := by
  rw [typeAOrthogonalDiagonal_def, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro a
  rcases a with u | (i | i)
  · exact isUnit_of_invertible (2 : A)
  · exact isUnit_one
  · exact (isUnit_of_invertible (2 : A)).mul (isUnit_neg_one.pow _)

/-- Reindexing, diagonal conjugation and scalar similarity identify the inverse
native type-`A_(2k)` reversal form with the split type-B Lie algebra. -/
noncomputable def typeAGraphSkewAdjointOrthogonalEquiv :
    skewAdjointMatricesLieSubalgebra
        (typeAGraphConjugator (2 * k) A :
          Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) A)⁻¹ ≃ₗ⁅A⁆
      LieAlgebra.Orthogonal.typeB (Fin k) A :=
  (skewAdjointMatricesLieSubalgebraEquivTranspose _
    (reindexAlgEquiv A A (typeAOrthogonalIndex k).symm)
    (by
      intro X
      rw [coe_reindexAlgEquiv]
      exact transpose_reindex _ _ X)).trans
    ((skewAdjointMatricesLieSubalgebraEquiv _
      (typeAOrthogonalDiagonal k A)
      (isUnit_typeAOrthogonalDiagonal k A).invertible).trans
      (LieEquiv.ofEq _ (LieAlgebra.Orthogonal.typeB (Fin k) A) (by
        rw [coe_reindexAlgEquiv,
          typeAOrthogonalDiagonal_transpose_mul_reindex_typeAGraphConjugator_inv_mul]
        ext X
        exact mem_skewAdjointMatricesLieSubalgebra_unit_smul
          (unitOfInvertible (2 : A) * (-1 : Aˣ) ^ k)
          (LieAlgebra.Orthogonal.JB (Fin k) A) X)))

/-- The forward map reindexes and then conjugates by the explicit diagonal matrix. -/
@[simp]
theorem typeAGraphSkewAdjointOrthogonalEquiv_apply_val
    (X : skewAdjointMatricesLieSubalgebra
      (typeAGraphConjugator (2 * k) A :
        Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) A)⁻¹) :
    (typeAGraphSkewAdjointOrthogonalEquiv k A X :
        Matrix (Unit ⊕ (Fin k ⊕ Fin k)) (Unit ⊕ (Fin k ⊕ Fin k)) A) =
      (typeAOrthogonalDiagonal k A)⁻¹ *
        reindex (typeAOrthogonalIndex k).symm (typeAOrthogonalIndex k).symm
          (X : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) A) *
        typeAOrthogonalDiagonal k A := by
  rw [typeAGraphSkewAdjointOrthogonalEquiv, LieEquiv.trans_apply, LieEquiv.trans_apply,
    LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply,
    skewAdjointMatricesLieSubalgebraEquivTranspose_apply]
  simp only [coe_reindexAlgEquiv]

/-- The inverse map undoes the diagonal conjugation and the reindexing. -/
@[simp]
theorem typeAGraphSkewAdjointOrthogonalEquiv_symm_apply_val
    (Y : LieAlgebra.Orthogonal.typeB (Fin k) A) :
    ((typeAGraphSkewAdjointOrthogonalEquiv k A).symm Y :
        Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) A) =
      reindex (typeAOrthogonalIndex k) (typeAOrthogonalIndex k)
        (typeAOrthogonalDiagonal k A *
          (Y : Matrix (Unit ⊕ (Fin k ⊕ Fin k)) (Unit ⊕ (Fin k ⊕ Fin k)) A) *
          (typeAOrthogonalDiagonal k A)⁻¹) := by
  apply (reindex (typeAOrthogonalIndex k).symm (typeAOrthogonalIndex k).symm).injective
  have h := typeAGraphSkewAdjointOrthogonalEquiv_apply_val k A
    ((typeAGraphSkewAdjointOrthogonalEquiv k A).symm Y)
  rw [LieEquiv.apply_symm_apply] at h
  rw [h]
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_typeAOrthogonalDiagonal k A)
  simp [mul_assoc, ← mul_assoc (typeAOrthogonalDiagonal k A),
    Matrix.mul_nonsing_inv _ hP]

/-- The fixed algebra of the pinned type-`A_(2k)` graph automorphism is the
split orthogonal Lie algebra in dimension `2 * k + 1`. -/
noncomputable def typeASpecialLinearFixedOrthogonalEquiv :
    (typeASpecialLinearGraphAutomorphism (2 * k) A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      LieAlgebra.Orthogonal.typeB (Fin k) A :=
  (typeASpecialLinearFixedSkewAdjointEquiv (2 * k) A).trans
    (typeAGraphSkewAdjointOrthogonalEquiv k A)

/-- The fixed-algebra comparison is the specified reindexing and diagonal conjugation. -/
@[simp]
theorem typeASpecialLinearFixedOrthogonalEquiv_apply_val
    (X : (typeASpecialLinearGraphAutomorphism (2 * k) A).toLieHom.fixedSubalgebra) :
    (typeASpecialLinearFixedOrthogonalEquiv k A X :
        Matrix (Unit ⊕ (Fin k ⊕ Fin k)) (Unit ⊕ (Fin k ⊕ Fin k)) A) =
      (typeAOrthogonalDiagonal k A)⁻¹ *
        reindex (typeAOrthogonalIndex k).symm (typeAOrthogonalIndex k).symm X.val.val *
        typeAOrthogonalDiagonal k A := by
  simp [typeASpecialLinearFixedOrthogonalEquiv]

/-- The inverse fixed-algebra comparison has the inverse coordinate formula. -/
@[simp]
theorem typeASpecialLinearFixedOrthogonalEquiv_symm_apply_val
    (Y : LieAlgebra.Orthogonal.typeB (Fin k) A) :
    ((typeASpecialLinearFixedOrthogonalEquiv k A).symm Y).val.val =
      reindex (typeAOrthogonalIndex k) (typeAOrthogonalIndex k)
        (typeAOrthogonalDiagonal k A *
          (Y : Matrix (Unit ⊕ (Fin k ⊕ Fin k)) (Unit ⊕ (Fin k ⊕ Fin k)) A) *
          (typeAOrthogonalDiagonal k A)⁻¹) := by
  simp [typeASpecialLinearFixedOrthogonalEquiv]

end TauCeti
