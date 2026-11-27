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
back to that of `B` (`star x * A * x = B`) identifies the mixed Gram blocks for the two forms.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
* `Matrix.conjTranspose_map_intCast`: an integral matrix, viewed as a matrix over a star ring
  such as `ℂ`, has `Xᴴ = Xᵀ`.
* `Matrix.conjTranspose_mul_mul_mul_of_star_mul_mul_eq`: if `star x * A * x = B`, then
  `(x F)ᴴ A (x G) = Fᴴ B G`.
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

section NonUnitalSemiring

variable {n R : Type*} [Fintype n] [NonUnitalSemiring R] [StarRing R] {A : Matrix n n R}

/-- If `x` pulls the form `A` back to the form `B` by `star x * A * x = B`, the mixed
Gram block of `x * F` and `x * G` for `A` equals that of `F` and `G` for `B`. -/
theorem conjTranspose_mul_mul_mul_of_star_mul_mul_eq {k : Type*} {B x : Matrix n n R}
    (hx : star x * A * x = B) (F : Matrix n m R) (G : Matrix n k R) :
    (x * F)ᴴ * A * (x * G) = Fᴴ * B * G := by
  rw [← hx]
  simp only [conjTranspose_mul, star_eq_conjTranspose, Matrix.mul_assoc]

end NonUnitalSemiring

end Matrix
