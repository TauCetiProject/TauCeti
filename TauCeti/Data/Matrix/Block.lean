/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Products, powers and idempotents of block matrices

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

Heights `h` on `X` and `h'` on `X'` combine to the height `TauCeti.sumHeight h h'` on `X ⊕ X'`,
with `h'` shifted above every value of `h`. When the nonzero entries of square matrices `D` and
`D'` raise `h` and `h'`, those of the block upper-triangular matrix `fromBlocks D G 0 D'` raise
`sumHeight h h'`, so its paths of nonzero entries have bounded length.

The four blocks of a product `B * C` of rectangular block matrices are computed directly in terms
of the blocks of `B` and `C` via `Matrix.toBlocks₁₁_mul`, `Matrix.toBlocks₁₂_mul`,
`Matrix.toBlocks₂₁_mul`, and `Matrix.toBlocks₂₂_mul`, over any type with
`[AddCommMonoid α] [Mul α]`.

For an upper two-block matrix, the diagonal blocks of its powers are the powers of the diagonal
blocks. Its off-diagonal block is the finite convolution of the powers of the two diagonal
blocks with the original off-diagonal block. This holds over semirings, including zeroth powers
and empty blocks.

## Main results

* `Matrix.toBlocks₁₁_mul`, `Matrix.toBlocks₁₂_mul`, `Matrix.toBlocks₂₁_mul`,
  `Matrix.toBlocks₂₂_mul`: the four blocks of a product of block matrices.
* `Matrix.fromBlocks_zero₂₁_pow`: the power formula for an upper two-block matrix.
* `Matrix.fromBlocks₁₁NonUnitalStarAlgHom`: the corner embedding `y ↦ fromBlocks y 0 0 0` as a
  non-unital `⋆`-algebra homomorphism.
* `Matrix.fromBlocks_mul_sub_mul`: the four blocks of a difference of products.
* `IsIdempotentElem.fromBlocks_zero₁₂_zero₂₁` and `IsStarProjection.fromBlocks_zero₁₂_zero₂₁`:
  the direct sum of idempotent matrices is idempotent, and that of star projections is a star
  projection. Conversely, by `Matrix.isIdempotentElem_fromBlocks_zero₁₂_zero₂₁_iff` and
  `Matrix.isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff`, so are the diagonal blocks of such a
  direct sum.
* `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq` and
  `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`: Murray–von Neumann
  equivalent idempotents are conjugate after stabilization.
* `TauCeti.sumHeight_lt_of_fromBlocks`: a block upper-triangular matrix raises the height
  `TauCeti.sumHeight h h'` along its nonzero entries; `TauCeti.univ_sup_sumHeight_le` bounds
  that height.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, Chapter III, §4.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, Chapter 1.
-/

namespace Matrix

section ToBlocksMul

variable {n o l m p q α : Type*} [Fintype l] [Fintype m] [AddCommMonoid α] [Mul α]

/-- The upper-left block of a product of block matrices. -/
public theorem toBlocks₁₁_mul (B : Matrix (n ⊕ o) (l ⊕ m) α) (C : Matrix (l ⊕ m) (p ⊕ q) α) :
    (B * C).toBlocks₁₁ = B.toBlocks₁₁ * C.toBlocks₁₁ + B.toBlocks₁₂ * C.toBlocks₂₁ := by
  ext i j
  simp only [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.mul_apply, Matrix.add_apply,
    Fintype.sum_sum_type]

/-- The upper-right block of a product of block matrices. -/
public theorem toBlocks₁₂_mul (B : Matrix (n ⊕ o) (l ⊕ m) α) (C : Matrix (l ⊕ m) (p ⊕ q) α) :
    (B * C).toBlocks₁₂ = B.toBlocks₁₁ * C.toBlocks₁₂ + B.toBlocks₁₂ * C.toBlocks₂₂ := by
  ext i j
  simp only [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, of_apply, Matrix.mul_apply, Matrix.add_apply,
    Fintype.sum_sum_type]

/-- The lower-left block of a product of block matrices. -/
public theorem toBlocks₂₁_mul (B : Matrix (n ⊕ o) (l ⊕ m) α) (C : Matrix (l ⊕ m) (p ⊕ q) α) :
    (B * C).toBlocks₂₁ = B.toBlocks₂₁ * C.toBlocks₁₁ + B.toBlocks₂₂ * C.toBlocks₂₁ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₁, toBlocks₂₂, of_apply, Matrix.mul_apply, Matrix.add_apply,
    Fintype.sum_sum_type]

/-- The lower-right block of a product of block matrices. -/
public theorem toBlocks₂₂_mul (B : Matrix (n ⊕ o) (l ⊕ m) α) (C : Matrix (l ⊕ m) (p ⊕ q) α) :
    (B * C).toBlocks₂₂ = B.toBlocks₂₁ * C.toBlocks₁₂ + B.toBlocks₂₂ * C.toBlocks₂₂ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₂, toBlocks₂₂, of_apply, Matrix.mul_apply, Matrix.add_apply,
    Fintype.sum_sum_type]

end ToBlocksMul

/-- The power of an upper two-block matrix, with its off-diagonal block given by the finite
convolution of the two diagonal-block powers. -/
public theorem fromBlocks_zero₂₁_pow {R m n : Type*} [Semiring R]
    [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) (k : ℕ) :
    fromBlocks A B 0 D ^ k = fromBlocks (A ^ k)
      (∑ i ∈ Finset.range k, A ^ i * B * D ^ (k - 1 - i)) 0 (D ^ k) := by
  induction k with
  | zero =>
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, ih, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ]
    congr 1
    rw [Matrix.sum_mul, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hidx : k - 1 - i + 1 = k - i := by
      have := Finset.mem_range.mp hi
      omega
    rw [Matrix.mul_assoc, ← pow_succ, hidx]

/-- The corner embedding `y ↦ fromBlocks y 0 0 0` of `Matrix l l α` into
`Matrix (l ⊕ m) (l ⊕ m) α`, as a non-unital `⋆`-algebra homomorphism. -/
public def fromBlocks₁₁NonUnitalStarAlgHom (R α l m : Type*) [Fintype l] [Fintype m]
    [Monoid R] [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [StarAddMonoid α] :
    Matrix l l α →⋆ₙₐ[R] Matrix (l ⊕ m) (l ⊕ m) α where
  toFun y := fromBlocks y 0 0 0
  map_smul' c y := by simp [fromBlocks_smul]
  map_zero' := by simp
  map_add' y z := by simp [fromBlocks_add]
  map_mul' y z := by simp [fromBlocks_multiply]
  map_star' y := by simp [star_eq_conjTranspose, fromBlocks_conjTranspose]

/-- The corner embedding places a matrix in the top-left block. -/
@[simp]
public theorem fromBlocks₁₁NonUnitalStarAlgHom_apply {R α l m : Type*} [Fintype l] [Fintype m]
    [Monoid R] [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [StarAddMonoid α]
    (y : Matrix l l α) : fromBlocks₁₁NonUnitalStarAlgHom R α l m y = fromBlocks y 0 0 0 :=
  (rfl)

end Matrix

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

/-- The block-diagonal matrix `Matrix.fromBlocks p 0 0 q` with star projections as diagonal blocks
is a star projection. -/
public theorem IsStarProjection.fromBlocks_zero₁₂_zero₂₁ {m n α : Type*} [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring α] [StarAddMonoid α] {p : Matrix m m α} {q : Matrix n n α}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (Matrix.fromBlocks p 0 0 q) :=
  ⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hq.isIdempotentElem,
    (hp.isSelfAdjoint.isHermitian.fromBlocks Matrix.conjTranspose_zero
      hq.isSelfAdjoint.isHermitian).isSelfAdjoint⟩

/-- This is the `iff` version of `IsIdempotentElem.fromBlocks_zero₁₂_zero₂₁`. -/
@[simp]
public theorem Matrix.isIdempotentElem_fromBlocks_zero₁₂_zero₂₁_iff {m n α : Type*} [Fintype m]
    [Fintype n] [NonUnitalNonAssocSemiring α] {e : Matrix m m α} {f : Matrix n n α} :
    IsIdempotentElem (Matrix.fromBlocks e 0 0 f) ↔ IsIdempotentElem e ∧ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_inj, true_and]

/-- This is the `iff` version of `IsStarProjection.fromBlocks_zero₁₂_zero₂₁`. -/
@[simp]
public theorem Matrix.isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff {m n α : Type*} [Fintype m]
    [Fintype n] [NonUnitalNonAssocSemiring α] [StarAddMonoid α] {p : Matrix m m α}
    {q : Matrix n n α} :
    IsStarProjection (Matrix.fromBlocks p 0 0 q) ↔ IsStarProjection p ∧ IsStarProjection q := by
  simp only [isStarProjection_iff, Matrix.isIdempotentElem_fromBlocks_zero₁₂_zero₂₁_iff,
    ← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_fromBlocks_iff,
    Matrix.conjTranspose_zero, true_and]
  exact and_and_and_comm

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

namespace TauCeti

section SumHeight

open Finset

variable {X X' A : Type*}

/-- The height on `X ⊕ X'` of two heights on `X` and `X'`, that of `X'` shifted above that of
`X`. -/
public def sumHeight [Fintype X] (h : X → ℕ) (h' : X' → ℕ) : X ⊕ X' → ℕ :=
  Sum.elim h fun y => univ.sup h + 1 + h' y

/-- On `X`, `sumHeight h h'` is `h`. -/
@[simp]
public theorem sumHeight_inl [Fintype X] (h : X → ℕ) (h' : X' → ℕ) (x : X) :
    sumHeight h h' (.inl x) = h x :=
  (rfl)

/-- On `X'`, `sumHeight h h'` is `h'` shifted above the largest value of `h`. -/
@[simp]
public theorem sumHeight_inr [Fintype X] (h : X → ℕ) (h' : X' → ℕ) (y : X') :
    sumHeight h h' (.inr y) = univ.sup h + 1 + h' y :=
  (rfl)

/-- The largest value of `sumHeight h h'` is at most the sum of the largest heights plus one. -/
public theorem univ_sup_sumHeight_le [Fintype X] [Fintype X'] (h : X → ℕ) (h' : X' → ℕ) :
    univ.sup (sumHeight h h') ≤ univ.sup h + univ.sup h' + 1 :=
  Finset.sup_le fun a _ => by
    rcases a with x | y
    · have := le_sup (f := h) (mem_univ x)
      rw [sumHeight_inl]
      omega
    · have := le_sup (f := h') (mem_univ y)
      rw [sumHeight_inr]
      omega

/-- A block upper-triangular matrix `fromBlocks D G 0 D'` increases `sumHeight h h'` along its
nonzero entries when `D` and `D'` increase `h` and `h'`. -/
public theorem sumHeight_lt_of_fromBlocks [Fintype X] [Zero A] {D : Matrix X X A}
    {D' : Matrix X' X' A} (h : X → ℕ) (hD : ∀ x y, D x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hD' : ∀ x y, D' x y ≠ 0 → h' x < h' y) (G : Matrix X X' A) {a b : X ⊕ X'}
    (hab : Matrix.fromBlocks D G 0 D' a b ≠ 0) :
    sumHeight h h' a < sumHeight h h' b := by
  rcases a with x | x <;> rcases b with y | y <;>
    simp only [sumHeight_inl, sumHeight_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at hab ⊢
  · exact hD x y hab
  · have := le_sup (f := h) (mem_univ x); omega
  · simp at hab
  · have := hD' x y hab; omega

end SumHeight

end TauCeti
