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
back to that of `B` (`star x * A * x = B`) carries Gram matrices for `B` to Gram matrices for `A`.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
* `Matrix.transpose_map_starRingEnd`: `(M.map (starRingEnd S))ᵀ = Mᴴ`.
* `Matrix.conjTranspose_map_intCast`: an integral matrix, viewed as a matrix over a star ring
  such as `ℂ`, has `Xᴴ = Xᵀ`.
* `Matrix.conjTranspose_mul_mul_mul_of_star_mul_mul_eq`: if `star x * A * x = B`, then
  `(x F)ᴴ A (x F) = Fᴴ B F`.
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

/-- The transpose of the image of a matrix under `starRingEnd` is its conjugate transpose. -/
@[simp]
theorem transpose_map_starRingEnd {l m S : Type*} [CommSemiring S] [StarRing S]
    (M : Matrix l m S) : (M.map (starRingEnd S))ᵀ = Mᴴ := by
  ext
  simp [starRingEnd_apply]

/-- An integral matrix, viewed as a matrix over a star ring, has `Xᴴ = Xᵀ`. -/
@[simp]
theorem conjTranspose_map_intCast {R : Type*} [Ring R] [StarRing R] (X : Matrix l m ℤ) :
    (X.map ((↑) : ℤ → R))ᴴ = (X.map ((↑) : ℤ → R))ᵀ := by
  ext i j
  simp

section NonUnitalSemiring

variable {n R : Type*} [Fintype n] [NonUnitalSemiring R] [StarRing R] {A : Matrix n n R}

/-- If `x` pulls the form of Gram matrix `A` back to the form of Gram matrix `B`, that is
`star x * A * x = B`, then the Gram matrix for `A` of the family of vectors `x * F` is the Gram
matrix for `B` of the family `F`: `(x F)ᴴ A (x F) = Fᴴ B F`. Here `x` sends vectors on the side of
`B` to vectors on the side of `A`. For `B = A`, an isometry of `A` does not change Gram matrices. -/
theorem conjTranspose_mul_mul_mul_of_star_mul_mul_eq {B x : Matrix n n R}
    (hx : star x * A * x = B) (F : Matrix n m R) : (x * F)ᴴ * A * (x * F) = Fᴴ * B * F := by
  rw [← hx]
  simp only [conjTranspose_mul, star_eq_conjTranspose, Matrix.mul_assoc]

end NonUnitalSemiring

end Matrix
