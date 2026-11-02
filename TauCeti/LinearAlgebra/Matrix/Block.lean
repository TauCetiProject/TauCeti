/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Block matrix identities

The four blocks extracted from a matrix on sum index types are its submatrices along the
corresponding sum injections. These identities connect the block and submatrix APIs.

The determinant of a block-diagonal matrix `Matrix.blockDiagonal' M` whose blocks may have
different index types is the product of the determinants of its blocks. This is the dependent
version of Mathlib's `Matrix.det_blockDiagonal`, and computes the determinant of a coordinatewise
endomorphism of a finite dependent product.

## Main results

* `Matrix.toBlocks₁₁_eq_submatrix`, `Matrix.toBlocks₁₂_eq_submatrix`,
  `Matrix.toBlocks₂₁_eq_submatrix`, and `Matrix.toBlocks₂₂_eq_submatrix`: block extraction
  as submatrix restriction.
* `Matrix.det_blockDiagonal'`: `(blockDiagonal' M).det = ∏ i, (M i).det`.
-/

namespace Matrix

-- Keep these bridges as explicit rewrite rules so block expressions retain their simp normal form.
/-- The upper-left block is the submatrix along the left sum injections. -/
public theorem toBlocks₁₁_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₁₁ = M.submatrix Sum.inl Sum.inl :=
  (rfl)

/-- The upper-right block restricts rows along the left injection and columns along the right. -/
public theorem toBlocks₁₂_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₁₂ = M.submatrix Sum.inl Sum.inr :=
  (rfl)

/-- The lower-left block restricts rows along the right injection and columns along the left. -/
public theorem toBlocks₂₁_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₂₁ = M.submatrix Sum.inr Sum.inl :=
  (rfl)

/-- The lower-right block is the submatrix along the right sum injections. -/
public theorem toBlocks₂₂_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₂₂ = M.submatrix Sum.inr Sum.inr :=
  (rfl)

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
