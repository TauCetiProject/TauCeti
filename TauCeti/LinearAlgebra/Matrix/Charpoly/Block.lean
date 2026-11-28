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

If a square matrix `M` is block triangular for the splitting of the indices along a predicate, its
characteristic polynomial is the product of those of the two diagonal blocks
(`Matrix.twoBlockTriangular_charpoly`). In particular, if the column `i` of `M` vanishes off the
diagonal, its characteristic polynomial is `(X - M i i)` times that of the square block on the
other indices (`Matrix.charpoly_eq_X_sub_C_mul_charpoly_toSquareBlockProp`).
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

/-- If `M` is block triangular for the splitting of the indices along a predicate `p`, its
characteristic polynomial is the product of those of the two diagonal blocks. This is the
characteristic polynomial analogue of Mathlib's `Matrix.twoBlockTriangular_det`. -/
theorem twoBlockTriangular_charpoly (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.charpoly = (M.toSquareBlockProp p).charpoly * (M.toSquareBlockProp (¬p ·)).charpoly := by
  -- The characteristic matrix is block triangular as well, as its diagonal lies in the blocks.
  have h_tri : ∀ i, ¬p i → ∀ j, p j → M.charmatrix i j = 0 := fun i hi j hj ↦ by
    have hij : i ≠ j := fun hij ↦ hi (hij ▸ hj)
    rw [charmatrix_apply_ne _ _ _ hij, h i hi j hj, C_0, neg_zero]
  rw [charpoly, twoBlockTriangular_det _ p h_tri]
  congr 1 <;> rw [charpoly] <;> congr 1 <;> ext <;>
    simp [charmatrix_apply, toSquareBlockProp_def, diagonal_apply, Subtype.ext_iff]

/-- If the column `i` of `M` vanishes off the diagonal, the characteristic polynomial of `M` is
`X - M i i` times that of the square block of `M` on the indices other than `i`. -/
theorem charpoly_eq_X_sub_C_mul_charpoly_toSquareBlockProp {M : Matrix n n R} {i : n}
    (hM : ∀ j ≠ i, M j i = 0) :
    M.charpoly = (X - C (M i i)) * (M.toSquareBlockProp (· ≠ i)).charpoly := by
  rw [twoBlockTriangular_charpoly M (· = i) fun r hr c hc ↦ hc ▸ hM r hr]
  congr 1
  -- The block on `i` alone is the square block of `id` at `i`.
  change (M.toSquareBlock id i).charpoly = _
  rw [charpoly, charmatrix_toSquareBlock, det_toSquareBlock_id, charmatrix_apply_eq]

end ColumnBlock

end Matrix
