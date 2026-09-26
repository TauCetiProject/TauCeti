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

* `Matrix.fromBlocks_mem_typeD`: a block matrix `[[A, B], [C, -Aᵀ]]` belongs to the split
  type-`D` Lie algebra when its off-diagonal blocks are skew-symmetric.
* `TauCeti.typeD_apply_inr_inr`, `TauCeti.typeD_apply_inl_inr`, and
  `TauCeti.typeD_apply_inr_inl`: the three block relations satisfied by a type-`D` matrix.
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A block matrix `[[A, B], [C, -Aᵀ]]` belongs to the split type-`D` Lie algebra when its
off-diagonal blocks are skew-symmetric. -/
theorem fromBlocks_mem_typeD {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]
    (A B C : Matrix ι ι K) (hB : B.transpose = -B) (hC : C.transpose = -C) :
    fromBlocks A B C (-A.transpose) ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- The membership lemmas leave `Matrix.IsSkewAdjoint`; its matrix-form definition reduces to
  -- this equation, and no public rewrite lemma names that final definitional reduction.
  change (Matrix.fromBlocks A B C (-A.transpose)).transpose *
      LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K *
      (-Matrix.fromBlocks A B C (-A.transpose))
  simp only [LieAlgebra.Orthogonal.JD, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.transpose_neg,
    Matrix.transpose_transpose, hB, hC, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, neg_neg]

end Matrix

namespace TauCeti

open Matrix

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- In a type-`D` matrix, the lower-right block is the negative transpose of the upper-left
block. -/
@[simp]
theorem typeD_apply_inr_inr (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inr j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl i) := by
  have hA := A.2
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JD ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K * (-(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) at hA
  have h := congr_fun (congr_fun hA (.inl i)) (.inr j)
  exact neg_eq_iff_eq_neg.mp (by
    simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h.symm)

/-- In a type-`D` matrix, the upper-right block is skew-symmetric. -/
theorem typeD_apply_inl_inr (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inr i) := by
  have hA := A.2
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JD ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K * (-(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) at hA
  have h := congr_fun (congr_fun hA (.inr j)) (.inr i)
  simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h

/-- In a type-`D` matrix, the lower-left block is skew-symmetric. -/
theorem typeD_apply_inr_inl (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr j) (.inl i) := by
  have hA := A.2
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JD ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K * (-(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) at hA
  have h := congr_fun (congr_fun hA (.inl j)) (.inl i)
  simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h

end TauCeti
