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
homomorphism `starRingEnd`, so lemmas about ring homomorphisms apply to it.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
-/

public section

open scoped Matrix

namespace Matrix

section CommSemiring

variable {l m α : Type*} [CommSemiring α] [StarRing α]

/-- Conjugating the entries of a matrix is mapping it through the ring homomorphism
`starRingEnd α`, so that lemmas about ring homomorphisms, such as `Matrix.map_mul` and
`RingHom.map_det`, apply to it. -/
theorem map_star_eq_map_starRingEnd (M : Matrix l m α) : M.map star = M.map (starRingEnd α) := by
  ext
  exact (starRingEnd_apply _).symm

end CommSemiring

/-- Over a star semiring, conjugating `star v ⬝ᵥ (M *ᵥ v)` replaces `M` by `Mᴴ`. -/
theorem star_dotProduct_mulVec_self {n R : Type*} [Fintype n] [NonUnitalSemiring R] [StarRing R]
    (M : Matrix n n R) (v : n → R) :
    star (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (Mᴴ *ᵥ v) := by
  rw [← star_dotProduct, star_mulVec, dotProduct_mulVec]

/-- For a skew-Hermitian matrix `Mᴴ = -M`, `star v ⬝ᵥ (M *ᵥ v)` is skew-adjoint. -/
theorem star_dotProduct_mulVec_self_of_skewHermitian {n R : Type*} [Fintype n] [Ring R]
    [StarRing R] {M : Matrix n n R} (hM : Mᴴ = -M) (v : n → R) :
    star (star v ⬝ᵥ (M *ᵥ v)) = -(star v ⬝ᵥ (M *ᵥ v)) := by
  rw [star_dotProduct_mulVec_self, hM, neg_mulVec, dotProduct_neg]

end Matrix
