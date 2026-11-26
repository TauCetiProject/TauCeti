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

end Matrix
