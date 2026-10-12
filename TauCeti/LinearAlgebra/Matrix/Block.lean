/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of dependent block-diagonal matrices

The determinant of a block-diagonal matrix `Matrix.blockDiagonal' M` whose blocks may have
different index types is the product of the determinants of its blocks. This is the dependent
version of Mathlib's `Matrix.det_blockDiagonal`, and computes the determinant of a coordinatewise
endomorphism of a finite dependent product.

## Main results

* `Matrix.det_blockDiagonal'`: `(blockDiagonal' M).det = ∏ i, (M i).det`.
-/

namespace Matrix

/-- The determinant of a block-diagonal matrix with blocks of possibly different sizes is the
product of the determinants of the blocks. This is the dependent version of
`Matrix.det_blockDiagonal`. -/
@[simp]
public theorem det_blockDiagonal' {o R : Type*} {m : o → Type*} [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [CommRing R] (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  -- `BlockTriangular.det_fintype` needs a linear order on the block indices; any one will do.
  let _ : LinearOrder o := Equiv.linearOrder (Fintype.equivFin o)
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← det_reindex_self (Equiv.sigmaSubtype i)]
  congr 1
  ext j k
  -- The `@[simps]` lemmas of `Equiv.sigmaSubtype` only give the first component of
  -- `(Equiv.sigmaSubtype i).symm j`, so the definition is unfolded to see that it is `⟨i, j⟩`.
  simp [toSquareBlock_def, Equiv.sigmaSubtype]

end Matrix
