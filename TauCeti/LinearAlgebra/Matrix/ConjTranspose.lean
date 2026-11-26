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
transpose.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
* `Matrix.conjTranspose_map_intCast`: an integral matrix, viewed as a matrix over a star ring
  such as `ℂ`, has `Xᴴ = Xᵀ`.
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

end Matrix
