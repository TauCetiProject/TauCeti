/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Rank of off-diagonal block matrices

The rank of a matrix supported on its two off-diagonal blocks is the sum of their ranks.
In particular, a Hermitian dilation doubles the rank of its rectangular block.
-/

public section

namespace Matrix

/-- An off-diagonal block matrix has rank equal to the sum of the ranks of its two blocks. -/
@[simp]
theorem rank_fromBlocks_zero₁₁_zero₂₂ {K m n p q : Type*} [Field K] [Finite n] [Finite q]
    (B : Matrix m q K) (C : Matrix p n K) :
    (fromBlocks 0 B C 0).rank = B.rank + C.rank := by
  rw [← rank_submatrix (fromBlocks 0 B C 0) (Equiv.refl _) (Equiv.sumComm q n)]
  simpa only [Equiv.coe_refl, Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_right,
    submatrix_id_id] using rank_fromBlocks_zero₁₂_zero₂₁ B C

end Matrix
