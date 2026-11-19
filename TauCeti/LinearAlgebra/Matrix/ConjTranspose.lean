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
homomorphism `starRingEnd`, so lemmas about ring homomorphisms apply to it. On a vector fixed by
`star`, such as a real vector of `ℂⁿ`, the matrix with conjugated entries takes the conjugate of
the value of the original matrix.

## Main results

* `Matrix.map_star_eq_map_starRingEnd`: `M.map star = M.map (starRingEnd α)`.
* `Matrix.map_star_mulVec_of_star_eq`: if `star v = v`, then `M.map star *ᵥ v = star (M *ᵥ v)`.
-/

public section

namespace Matrix

variable {l m n α : Type*} [CommSemiring α] [StarRing α]

/-- Conjugating the entries of a matrix is mapping it through the ring homomorphism
`starRingEnd α`, so that lemmas about ring homomorphisms, such as `Matrix.map_mul` and
`RingHom.map_det`, apply to it. -/
theorem map_star_eq_map_starRingEnd (M : Matrix l m α) : M.map star = M.map (starRingEnd α) := by
  ext
  exact (starRingEnd_apply _).symm

/-- On a vector fixed by `star`, such as a real vector of `ℂⁿ`, the matrix `M.map star` with
conjugated entries takes the conjugate value `star (M v)`. -/
theorem map_star_mulVec_of_star_eq [Fintype n] (M : Matrix m n α) {v : n → α} (hv : star v = v) :
    M.map star *ᵥ v = star (M *ᵥ v) := by
  rw [star_mulVec, hv, conjTranspose, transpose_map, vecMul_transpose]

end Matrix
