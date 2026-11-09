/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical

/-!
# Basic lemmas for the split even orthogonal Lie algebra

This file records structural matrix lemmas for Mathlib's split type-`D` Lie algebra that do not
depend on a choice of Cartan subalgebra or root system.

## Main results

* `Matrix.fromBlocks_mem_typeD_iff`: a block matrix `[[A, B], [C, D]]` belongs to the split
  type-`D` Lie algebra if and only if its off-diagonal blocks are skew-symmetric and `D = -Aᵀ`.
* `LieAlgebra.Orthogonal.typeD.apply_inr_inr`, `LieAlgebra.Orthogonal.typeD.apply_inl_inr`, and
  `LieAlgebra.Orthogonal.typeD.apply_inr_inl`: the three block relations satisfied by a type-`D`
  matrix.
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A block matrix `[[A, B], [C, D]]` belongs to the split type-`D` Lie algebra if and only if its
off-diagonal blocks are skew-symmetric and `D = -Aᵀ`. -/
theorem fromBlocks_mem_typeD_iff {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]
    {A B C D : Matrix ι ι K} :
    fromBlocks A B C D ∈ LieAlgebra.Orthogonal.typeD ι K ↔
      Bᵀ = -B ∧ Cᵀ = -C ∧ D = -Aᵀ := by
  simp only [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    LieAlgebra.Orthogonal.JD, fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply,
    fromBlocks_inj, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
  constructor
  · rintro ⟨hC, hA, -, hB⟩
    exact ⟨hB, hC, (neg_eq_iff_eq_neg.mpr hA).symm⟩
  · rintro ⟨hB, hC, rfl⟩
    simp [hB, hC]

end Matrix

namespace LieAlgebra.Orthogonal.typeD

open Matrix

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The skew-adjointness equation defining the split type-`D` Lie algebra, as an equation between
matrices. -/
private theorem transpose_mul_JD (A : LieAlgebra.Orthogonal.typeD ι K) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JD ι K =
      LieAlgebra.Orthogonal.JD ι K * (-(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) := by
  simpa only [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using A.property

/-- In a type-`D` matrix, the lower-right block is the negative transpose of the upper-left
block. -/
@[simp]
theorem apply_inr_inr (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inr j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl i) := by
  have h := congr_fun (congr_fun (transpose_mul_JD A) (.inl i)) (.inr j)
  exact neg_eq_iff_eq_neg.mp (by
    simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h.symm)

/-- In a type-`D` matrix, the upper-right block is skew-symmetric. -/
theorem apply_inl_inr (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inr i) := by
  have h := congr_fun (congr_fun (transpose_mul_JD A) (.inr j)) (.inr i)
  simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h

/-- In a type-`D` matrix, the lower-left block is skew-symmetric. -/
theorem apply_inr_inl (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr j) (.inl i) := by
  have h := congr_fun (congr_fun (transpose_mul_JD A) (.inl j)) (.inl i)
  simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h

end LieAlgebra.Orthogonal.typeD
