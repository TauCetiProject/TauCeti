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
