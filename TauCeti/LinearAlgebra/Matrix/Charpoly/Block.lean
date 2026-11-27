/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import TauCeti.LinearAlgebra.Matrix.Block

/-!
# The characteristic polynomial of a block-diagonal matrix

The characteristic polynomial of the block-diagonal matrix `Matrix.blockDiagonal' A`, whose blocks
`A i` may have different sizes, is the product of the characteristic polynomials of the blocks
(`Matrix.charpoly_blockDiagonal'`). This extends Mathlib's `Matrix.charpoly_fromBlocks_zero₁₂`
from two blocks to finitely many.

If the column `i` of a square matrix `M` vanishes off the diagonal, then `M` is block triangular for
the splitting of the indices into `i` and the rest, and its characteristic polynomial is
`(X - M i i)` times that of the square block on the other indices
(`Matrix.charpoly_eq_X_sub_C_mul_charpoly_toSquareBlockProp`).
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {o : Type*} {m : o → Type*} [Fintype o] [DecidableEq o]
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The characteristic polynomial of a block-diagonal matrix, whose blocks may have different
sizes, is the product of the characteristic polynomials of its blocks. -/
@[simp]
theorem charpoly_blockDiagonal' (A : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' A).charpoly = ∏ i, (A i).charpoly := by
  have h : charmatrix (blockDiagonal' A) = blockDiagonal' fun i ↦ charmatrix (A i) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rcases eq_or_ne i j with rfl | h
    · simp [charmatrix_apply, blockDiagonal'_apply_eq, diagonal_apply]
    · simp [blockDiagonal'_apply_ne _ _ _ h, h]
  simp only [charpoly, h, det_blockDiagonal']

section ColumnBlock

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Taking a square block commutes with forming the characteristic matrix. This is the analogue of
Mathlib's `Matrix.charmatrix_toSquareBlock` for a block cut out by a predicate. -/
theorem charmatrix_toSquareBlockProp (M : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    (M.toSquareBlockProp p).charmatrix = M.charmatrix.toSquareBlockProp p := by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlockProp_def, diagonal_apply, Subtype.ext_iff]

/-- If the column `i` of `M` vanishes off the diagonal, the characteristic polynomial of `M` is
`X - M i i` times that of the square block of `M` on the indices other than `i`. -/
theorem charpoly_eq_X_sub_C_mul_charpoly_toSquareBlockProp {M : Matrix n n R} {i : n}
    (hM : ∀ j ≠ i, M j i = 0) :
    M.charpoly = (X - C (M i i)) * (M.toSquareBlockProp (· ≠ i)).charpoly := by
  -- The characteristic matrix inherits the zero column, so it is block triangular as well.
  have h_tri : ∀ r, ¬r = i → ∀ c, c = i → M.charmatrix r c = 0 := by
    rintro r hr c rfl
    simp [charmatrix_apply_ne _ _ _ hr, hM r hr]
  rw [charpoly, twoBlockTriangular_det _ (· = i) h_tri]
  congr 1
  · -- `det_eq_elem_of_subsingleton` synthesizes `Fintype.subtypeEq i` on `{j // j = i}`, while
    -- the block determinant uses `Subtype.fintype`; `convert` identifies the two instances.
    rw [← charmatrix_apply_eq]
    convert det_eq_elem_of_subsingleton (M.charmatrix.toSquareBlockProp (· = i)) ⟨i, rfl⟩
    rw [toSquareBlockProp_def, of_apply]
  · rw [charpoly, charmatrix_toSquareBlockProp]

end ColumnBlock

end Matrix
