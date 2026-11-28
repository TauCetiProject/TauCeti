/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Conjugating the entries of a matrix

Over a commutative star ring, conjugating the entries of a matrix is mapping it through the ring
homomorphism `starRingEnd`, so lemmas about ring homomorphisms apply to it. The entries of an
integral matrix are fixed by conjugation, so over any star ring its conjugate transpose is its
transpose. Over any star semiring, a matrix `x` pulling the sesquilinear form of Gram matrix `A`
back to that of `B` (`star x * A * x = B`) carries pairings for `B` to pairings for `A`.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
* `Matrix.conjTranspose_map_intCast`: an integral matrix, viewed as a matrix over a star ring
  such as `ℂ`, has `Xᴴ = Xᵀ`.
* `Matrix.transpose_map_mul`, `Matrix.transpose_map_transpose_map`: for an entrywise map `σ`,
  `M ↦ (M.map σ)ᵀ` reverses products when `σ` is multiplicative, and is an involution when `σ` is.
* `Matrix.conjTranspose_mul_mul_mul_of_star_mul_mul_eq`: if `star x * A * x = B`, then
  `(x F)ᴴ A (x F') = Fᴴ B F'`.
-/

public section

namespace Matrix

variable {l m α : Type*} [CommSemiring α] [StarRing α]

/-- Conjugating the entries of a matrix is mapping it through the ring homomorphism
`starRingEnd α`, so that lemmas about ring homomorphisms, such as `Matrix.map_mul` and
`RingHom.map_det`, apply to it. -/
theorem map_star_eq_map_starRingEnd (M : Matrix l m α) : M.map star = M.map (starRingEnd α) := by
  ext
  exact (starRingEnd_apply _).symm

/-- An integral matrix, viewed as a matrix over a star ring, has `Xᴴ = Xᵀ`. -/
@[simp]
theorem conjTranspose_map_intCast {R : Type*} [Ring R] [StarRing R] (X : Matrix l m ℤ) :
    (X.map ((↑) : ℤ → R))ᴴ = (X.map ((↑) : ℤ → R))ᵀ := by
  ext i j
  simp

/-- The `σ`-twisted transpose reverses products: `((M N) ^ σ)ᵀ = (N ^ σ)ᵀ (M ^ σ)ᵀ`, where `^ σ`
applies `σ` to every entry, for `σ` in any type of non-unital ring endomorphisms. -/
theorem transpose_map_mul {m n R S : Type*} [Fintype m] [NonUnitalNonAssocCommSemiring R]
    [FunLike S R R] [NonUnitalRingHomClass S R R] (σ : S) (M : Matrix l m R) (N : Matrix m n R) :
    ((M * N).map σ)ᵀ = (N.map σ)ᵀ * (M.map σ)ᵀ := by
  ext i j
  simp only [transpose_apply, map_apply, Matrix.mul_apply, map_sum, map_mul, mul_comm]

/-- For an involution `σ`, the `σ`-twisted transpose is an involution on matrices. -/
@[simp]
theorem transpose_map_transpose_map {n R : Type*} {σ : R → R} (hσ : Function.Involutive σ)
    (M : Matrix l n R) : (((M.map σ)ᵀ).map σ)ᵀ = M :=
  Matrix.ext fun i j ↦ hσ (M i j)

section NonUnitalSemiring

variable {n R : Type*} [Fintype n] [NonUnitalSemiring R] [StarRing R] {A : Matrix n n R}

/-- If `x` pulls the form of Gram matrix `A` back to the form of Gram matrix `B`, that is
`star x * A * x = B`, then the pairing for `A` of the families of vectors `x * F` and `x * F'` is
the pairing for `B` of the families `F` and `F'`: `(x F)ᴴ A (x F') = Fᴴ B F'`. Here `x` sends
vectors on the side of `B` to vectors on the side of `A`. For `F' = F` this compares Gram matrices,
and for `B = A` an isometry of `A` does not change them. -/
theorem conjTranspose_mul_mul_mul_of_star_mul_mul_eq {m' : Type*} {B x : Matrix n n R}
    (hx : star x * A * x = B) (F : Matrix n m R) (F' : Matrix n m' R) :
    (x * F)ᴴ * A * (x * F') = Fᴴ * B * F' := by
  rw [← hx]
  simp only [conjTranspose_mul, star_eq_conjTranspose, Matrix.mul_assoc]

end NonUnitalSemiring

end Matrix
