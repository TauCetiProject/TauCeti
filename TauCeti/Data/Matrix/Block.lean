/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block

/-!
# Products and idempotents of block matrices

The difference of the two products of block matrices can be computed block by block.
`Matrix.fromBlocks_mul_sub_mul` records this calculation without requiring an associative
or unital coefficient ring.

The block-diagonal matrix `Matrix.fromBlocks e 0 0 f` is the direct sum of the square matrices `e`
and `f`. It is idempotent when `e` and `f` are, which is how direct sums of idempotent matrices,
and hence the addition of algebraic `K₀`, are formed.

## Main results

* `Matrix.fromBlocks_mul_sub_mul`: the four blocks of a difference of products.
* `IsIdempotentElem.fromBlocks_zero₁₂_zero₂₁`: the direct sum of idempotent matrices is
  idempotent.
-/

/-- The difference of the two products of block matrices, computed in each block. -/
public theorem Matrix.fromBlocks_mul_sub_mul {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalNonAssocRing R] (A E : Matrix m m R) (B F : Matrix m n R)
    (C G : Matrix n m R) (D H : Matrix n n R) :
    Matrix.fromBlocks A B C D * Matrix.fromBlocks E F G H -
        Matrix.fromBlocks E F G H * Matrix.fromBlocks A B C D =
      Matrix.fromBlocks (A * E + B * G - (E * A + F * C))
        (A * F + B * H - (E * B + F * D))
        (C * E + D * G - (G * A + H * C))
        (C * F + D * H - (G * B + H * D)) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> rfl

/-- The block-diagonal matrix `Matrix.fromBlocks e 0 0 f` with idempotent diagonal blocks is
idempotent. -/
public theorem IsIdempotentElem.fromBlocks_zero₁₂_zero₂₁ {m n α : Type*} [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring α] {e : Matrix m m α} {f : Matrix n n α} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : IsIdempotentElem (Matrix.fromBlocks e 0 0 f) := by
  rw [IsIdempotentElem, Matrix.fromBlocks_multiply, he.eq, hf.eq]
  simp
