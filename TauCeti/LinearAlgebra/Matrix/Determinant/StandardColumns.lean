/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of matrices with standard columns

If every column of a square matrix `M` outside the image of an embedding `e : r ↪ n` is the
corresponding column of the identity matrix, then `M` is block triangular for the splitting of
`n` into `Set.range e` and its complement, with identity block on the complement. Its determinant
is therefore the determinant of the square submatrix `M.submatrix e e`.

## Main results

* `Matrix.det_eq_det_submatrix_of_col_eq_one`: the determinant of a square matrix whose columns
  off `Set.range e` are those of `1` is the determinant of its submatrix on the rows and columns
  `e`.
-/

public section

namespace Matrix

variable {n r R : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] [CommRing R]

/-- If the columns of `M` off the image of `e` are those of the identity matrix, then the
determinant of `M` is the determinant of its square submatrix on the rows and columns `e`. -/
theorem det_eq_det_submatrix_of_col_eq_one {M : Matrix n n R} (e : r ↪ n)
    (h : ∀ k ∉ Set.range e, ∀ i, M i k = (1 : Matrix n n R) i k) :
    M.det = (M.submatrix e e).det := by
  rw [M.twoBlockTriangular_det' (· ∈ Set.range e) fun i hi j hj ↦ by
    rw [h j hj, one_apply_ne fun hij : i = j ↦ hj (hij ▸ hi)]]
  have hone : (M.toSquareBlockProp fun i ↦ i ∉ Set.range e) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      simp [toSquareBlockProp_def, h i hi]
    · simp [toSquareBlockProp_def, h j hj, hij]
  have hblock : M.toSquareBlockProp (· ∈ Set.range e) = (M.submatrix e e).submatrix
      (Equiv.ofInjective e e.injective).symm (Equiv.ofInjective e e.injective).symm := by
    ext ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    simp [toSquareBlockProp_def]
  rw [hone, det_one, mul_one, hblock]
  -- `convert` identifies the two `Fintype` instances on `Set.range e` (subtype and range).
  convert det_submatrix_equiv_self _ (M.submatrix e e)

end Matrix
