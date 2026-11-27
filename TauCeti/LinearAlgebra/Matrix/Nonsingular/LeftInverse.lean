/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Left inverses of matrices with independent columns

Over a field, a rectangular matrix has a left inverse exactly when its columns are linearly
independent (`Matrix.linearIndependent_col_iff_exists_left_inverse`). This is the column form of
Mathlib's `Matrix.vecMul_surjective_iff_exists_left_inverse`.
-/

public section

namespace Matrix

variable {K m n : Type*} [Field K] [Finite n] [Fintype m] [DecidableEq n]

/-- **A matrix has a left inverse exactly when its columns are independent**: over a field,
`T * M = 1` for some `T` if and only if the columns of `M` are linearly independent. -/
theorem linearIndependent_col_iff_exists_left_inverse {M : Matrix m n K} :
    LinearIndependent K M.col ↔ ∃ T : Matrix n m K, T * M = 1 := by
  cases nonempty_fintype n
  refine ⟨fun hM ↦ ?_, fun ⟨T, hT⟩ ↦ mulVec_injective_iff.1 fun x y h ↦ ?_⟩
  · classical
    obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (mulVec_injective_iff.2 hM))
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  · simpa [mulVec_mulVec, hT] using congrArg (T *ᵥ ·) h

end Matrix
