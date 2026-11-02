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

Idempotent matrices `e` and `f`, possibly of different sizes, are Murray–von Neumann equivalent when
`e = a * b` and `f = b * a` for rectangular matrices `a` and `b`. After normalizing `a` and `b`, the
block matrix `!![1 - e, a; b, 1 - f]` is an involution conjugating `e ⊕ 0` to `0 ⊕ f`. This is how
equivalent idempotents, such as those presenting isomorphic projective modules, become conjugate
after stabilization.

## Main results

* `Matrix.fromBlocks_mul_sub_mul`: the four blocks of a difference of products.
* `IsIdempotentElem.fromBlocks_zero₁₂_zero₂₁`: the direct sum of idempotent matrices is
  idempotent.
* `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq` and
  `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`: Murray–von Neumann
  equivalent idempotents are conjugate after stabilization.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, Chapter III, §4.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, Chapter 1.
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

section MurrayVonNeumann

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring α]
  {e : Matrix m m α} {f : Matrix n n α} {a : Matrix m n α} {b : Matrix n m α}

/-- If `a * b = e` and `b * a = f`, with `a` a left `e`-multiple and `b` a right `e`-multiple,
then the block matrix `!![1 - e, a; b, 1 - f]` is an involution. -/
public theorem Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (hab : a * b = e) (hba : b * a = f)
    (hea : e * a = a) (hbe : b * e = b) :
    Matrix.fromBlocks (1 - e) a b (1 - f) * Matrix.fromBlocks (1 - e) a b (1 - f) = 1 := by
  have haf : a * f = a := by rw [← hba, ← Matrix.mul_assoc, hab, hea]
  have hfb : f * b = b := by rw [← hba, Matrix.mul_assoc, hab, hbe]
  have hee : e * e = e := by nth_rw 1 [← hab]; rw [Matrix.mul_assoc, hbe, hab]
  have hff : f * f = f := by nth_rw 1 [← hba]; rw [Matrix.mul_assoc, haf, hba]
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hab, hba, hea, hbe,
    haf, hfb, hee, hff, sub_self, sub_zero, add_zero, sub_add_cancel,
    add_sub_cancel]

/-- **Murray–von Neumann equivalent idempotents are stably conjugate.** If `a * b = e`,
`b * a = f` and `b * e = b`, then conjugating `e ⊕ 0` by `!![1 - e, a; b, 1 - f]` gives `0 ⊕ f`.
When also `e * a = a`, this block matrix is an involution, by
`Matrix.fromBlocks_one_sub_mul_self_of_mul_eq`. -/
public theorem Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (hab : a * b = e) (hba : b * a = f) (hbe : b * e = b) :
    Matrix.fromBlocks (1 - e) a b (1 - f) * Matrix.fromBlocks e 0 0 0 *
        Matrix.fromBlocks (1 - e) a b (1 - f) =
      Matrix.fromBlocks 0 0 0 f := by
  have hee : e * e = e := by nth_rw 1 [← hab]; rw [Matrix.mul_assoc, hbe, hab]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, hee, hbe, hba, sub_self, add_zero]

end MurrayVonNeumann
