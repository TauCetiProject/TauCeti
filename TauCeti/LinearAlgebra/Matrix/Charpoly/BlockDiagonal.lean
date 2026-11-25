/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Characteristic polynomials of block-diagonal matrices

The characteristic matrix of a block-diagonal matrix `Matrix.blockDiagonal' B`, with blocks of
possibly different sizes, is block diagonal with the characteristic matrices of the blocks as
blocks (`Matrix.charmatrix_blockDiagonal'`). Since the determinant of a block-diagonal matrix is
the product of the determinants of its blocks (`Matrix.det_blockDiagonal'`), its characteristic
polynomial is the product of those of the blocks. The reversed characteristic polynomial
`det (1 - X A)` is treated in the same way by `Matrix.charpolyRev_blockDiagonal'`.

## Main results

* `Matrix.charmatrix_blockDiagonal'`: the characteristic matrix of a block-diagonal matrix.
* `Matrix.charpoly_blockDiagonal'`: the characteristic polynomial of a block-diagonal matrix is
  the product of the characteristic polynomials of its blocks.
-/

public section

open Polynomial

namespace Matrix

variable {R o : Type*} [CommRing R] [Fintype o] [DecidableEq o] {m : o → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The characteristic matrix of a block-diagonal matrix is block diagonal, with the
characteristic matrices of the blocks as blocks. -/
theorem charmatrix_blockDiagonal' (B : ∀ i, Matrix (m i) (m i) R) :
    charmatrix (blockDiagonal' B) = blockDiagonal' fun i => charmatrix (B i) := by
  refine Matrix.ext fun ⟨i, a⟩ ⟨j, c⟩ => ?_
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne a c with rfl | hac
    · simp [charmatrix_apply_eq]
    · simp [hac]
  · simp [h, blockDiagonal'_apply_ne _ _ _ h]

/-- The characteristic polynomial of a block-diagonal matrix with blocks of possibly different
sizes is the product of the characteristic polynomials of the blocks. -/
@[simp]
theorem charpoly_blockDiagonal' (B : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' B).charpoly = ∏ i, (B i).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal', det_blockDiagonal']
  rfl

end Matrix
