/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Matrix-vector multiplication

Multiplying a vector by a matrix twice is multiplying it by the square of the matrix, so a
square-zero matrix annihilates every vector in two steps. This is the form in which the nilpotence
of a root operator reaches the vector it acts on.

When row `i` of a matrix vanishes off the diagonal, coordinate `i` of a product with a vector only
sees coordinate `i` of that vector. In particular such a matrix maps the coordinate hyperplane
`{v | v i = 0}` into itself.

## Main results

* `TauCeti.mulVec_mulVec_eq_zero_of_pow_two_eq_zero`: a square-zero matrix annihilates every
  vector in two multiplications.
* `Matrix.mulVec_apply_eq_mul_of_forall_ne_eq_zero`: if row `i` of `A` vanishes off the diagonal,
  then `(A *ᵥ v) i = A i i * v i`.
-/

public section

open scoped Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square-zero matrix annihilates every vector in two multiplications. -/
theorem mulVec_mulVec_eq_zero_of_pow_two_eq_zero {R : Type*} [Semiring R] {M : Matrix n n R}
    (hM : M ^ 2 = 0) (v : n → R) : M *ᵥ M *ᵥ v = 0 := by
  rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]

end TauCeti

namespace Matrix

variable {n R : Type*} [Fintype n] [NonUnitalNonAssocSemiring R]

/-- If row `i` of `A` vanishes off the diagonal, then coordinate `i` of `A *ᵥ v` is
`A i i * v i`. -/
theorem mulVec_apply_eq_mul_of_forall_ne_eq_zero {A : Matrix n n R} {i : n}
    (h : ∀ j ≠ i, A i j = 0) (v : n → R) : (A *ᵥ v) i = A i i * v i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj ↦ by rw [h j hj, zero_mul]) (by simp)

end Matrix
