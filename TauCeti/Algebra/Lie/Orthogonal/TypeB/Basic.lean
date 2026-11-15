/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic.LinearCombination

/-!
# Basic lemmas for the split odd orthogonal Lie algebra

This file records the entry relations and basic block maps for Mathlib's split type-`B` Lie
algebra, indexed by `Unit ⊕ ι ⊕ ι`. They do not depend on a choice of Cartan subalgebra or root
system. They are the type-`B` counterparts of the type-`D` relations
`LieAlgebra.Orthogonal.typeD.apply_inr_inr`, `LieAlgebra.Orthogonal.typeD.apply_inl_inr` and
`LieAlgebra.Orthogonal.typeD.apply_inr_inl`.

## Main results

* `LieAlgebra.Orthogonal.typeB.ofTypeD` and `LieAlgebra.Orthogonal.typeB.toTypeD`:
  zero extension and projection of the even orthogonal block.
* `LieAlgebra.Orthogonal.typeB.apply_inl_inl`: the anisotropic diagonal entry vanishes when `2`
  is regular.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inl_inl` and
  `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inl`: the anisotropic column is determined by the
  anisotropic row.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inl_inr_inr` and
  `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inr_inl`: the two off-diagonal isotropic blocks are
  skew-symmetric.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inr_inr`: the lower-right isotropic block is the
  negative transpose of the upper-left one.
-/

public section

namespace LieAlgebra.Orthogonal.typeB

open Matrix

section EntryRelations

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The skew-adjointness equation defining the split type-`B` Lie algebra, as an equation between
matrices. -/
private theorem transpose_mul_JB (A : LieAlgebra.Orthogonal.typeB ι K) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JB ι K =
      LieAlgebra.Orthogonal.JB ι K * (-(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)) := by
  simpa only [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using A.property

/-- In a type-`B` matrix, the anisotropic diagonal entry vanishes when `2` is regular. -/
theorem apply_inl_inl (A : LieAlgebra.Orthogonal.typeB ι K) (h2 : IsRegular (2 : K))
    (u : Unit) : (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inl u) = 0 := by
  have h := congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inl ())
  simp [LieAlgebra.Orthogonal.JB, Matrix.mul_apply] at h
  apply h2.left
  apply h2.left
  linear_combination h

/-- In a type-`B` matrix, the anisotropic column at the first isotropic half is determined by the
anisotropic row at the second. -/
@[simp]
theorem apply_inr_inl_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i : ι) (u : Unit) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inl u) =
      -(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inr (.inr i))) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inr (.inr i))

/-- In a type-`B` matrix, the anisotropic column at the second isotropic half is determined by the
anisotropic row at the first. -/
@[simp]
theorem apply_inr_inr_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i : ι) (u : Unit) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inl u) =
      -(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inr (.inl i))) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inr (.inl i))

/-- In a type-`B` matrix, the upper-right isotropic block is skew-symmetric. -/
theorem apply_inr_inl_inr_inr (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inr j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl j)) (.inr (.inr i)) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using
    congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inr j))) (.inr (.inr i))

/-- In a type-`B` matrix, the lower-left isotropic block is skew-symmetric. -/
theorem apply_inr_inr_inr_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inr (.inl j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr j)) (.inr (.inl i)) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using
    congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inl j))) (.inr (.inl i))

/-- In a type-`B` matrix, the lower-right isotropic block is the negative transpose of the
upper-left one. -/
@[simp]
theorem apply_inr_inr_inr_inr (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inr (.inr j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl j)) (.inr (.inl i)) := by
  have h := congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inl i))) (.inr (.inr j))
  simp [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] at h
  linear_combination h

end EntryRelations

section TypeDBlock

variable {R ι : Type*} [CommRing R] [DecidableEq ι] [Fintype ι]

/-- Extend a type-`D` matrix by zero on the anisotropic row and column. -/
def ofTypeD : typeD ι R →ₗ[R] typeB ι R where
  toFun X := ⟨fromBlocks 0 0 0 (X : Matrix (ι ⊕ ι) (ι ⊕ ι) R), by
    have hX := X.property
    simp only [typeD, mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hX
    simp only [typeB, mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, JB,
      fromBlocks_transpose, transpose_zero, fromBlocks_neg, neg_zero,
      fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, hX]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, fromBlocks_add, add_zero]
  map_smul' c X := by
    apply Subtype.ext
    simp only [SetLike.val_smul, fromBlocks_smul, smul_zero, RingHom.id_apply]

/-- The isotropic block of a native type-`B` matrix. -/
def toTypeD : typeB ι R →ₗ[R] typeD ι R where
  toFun X := ⟨(X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) R).toBlocks₂₂, by
    have hX := transpose_mul_JB X
    rw [← fromBlocks_toBlocks (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) R)] at hX
    simp only [JB, fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hX
    simpa only [typeD, mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      toBlocks_fromBlocks₂₂] using
      congrArg Matrix.toBlocks₂₂ hX⟩
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- Projection recovers a zero-extended type-`D` matrix. -/
@[simp]
theorem toTypeD_ofTypeD (X : typeD ι R) : toTypeD (ofTypeD X) = X := by
  rfl

/-- Zero extension has a zero anisotropic row and column. -/
@[simp]
theorem coe_ofTypeD (X : typeD ι R) :
    (ofTypeD X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) R) =
      fromBlocks 0 0 0 (X : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  rfl

/-- The underlying matrix of the isotropic projection. -/
@[simp]
theorem coe_toTypeD (X : typeB ι R) :
    (toTypeD X : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
      (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) R).toBlocks₂₂ := by
  rfl

end TypeDBlock

end LieAlgebra.Orthogonal.typeB
