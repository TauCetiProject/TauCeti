/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Matrix-vector multiplication

Multiplying a vector by a matrix twice is multiplying it by the square of the matrix, so a
square-zero matrix annihilates every vector in two steps. This is the form in which the nilpotence
of a root operator reaches the vector it acts on.

Over an ordered semiring, multiplication by an entrywise nonnegative matrix is monotone and
preserves nonnegativity, and an entrywise strictly positive matrix sends a nonzero nonnegative
vector to a strictly positive one.

When row `i` of a matrix vanishes off the diagonal, coordinate `i` of a product with a vector only
sees coordinate `i` of that vector. In particular such a matrix maps the coordinate hyperplane
`{v | v i = 0}` into itself.

## Main results

* `TauCeti.mulVec_mulVec_eq_zero_of_pow_two_eq_zero`: a square-zero matrix annihilates every
  vector in two multiplications.
* `Matrix.mulVec_apply_eq_mul_of_forall_ne_eq_zero`: if row `i` of `A` vanishes off the diagonal,
  then `(A *ᵥ v) i = A i i * v i`.
* `Matrix.mulVec_mono` and `Matrix.mulVec_nonneg`: multiplication by an entrywise nonnegative
  matrix is monotone and preserves nonnegativity.
* `Matrix.mulVec_pos`: a strictly positive matrix sends a nonzero nonnegative vector to a strictly
  positive one.
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

variable {m n : Type*} [Fintype n]

section NonUnitalNonAssocSemiring

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/-- If row `i` of `A` vanishes off the diagonal, then coordinate `i` of `A *ᵥ v` is
`A i i * v i`. -/
theorem mulVec_apply_eq_mul_of_forall_ne_eq_zero {A : Matrix n n R} {i : n}
    (h : ∀ j ≠ i, A i j = 0) (v : n → R) : (A *ᵥ v) i = A i i * v i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj ↦ by rw [h j hj, zero_mul]) (by simp)

end NonUnitalNonAssocSemiring

section OrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] {A : Matrix m n R}
  {x y : n → R}

/-- Multiplication by an entrywise nonnegative matrix is monotone. -/
theorem mulVec_mono (hA : ∀ i j, 0 ≤ A i j) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := fun i =>
  dotProduct_le_dotProduct_of_nonneg_left hxy (hA i)

/-- An entrywise nonnegative matrix sends nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg (hA : ∀ i j, 0 ≤ A i j) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := fun i =>
  dotProduct_nonneg_of_nonneg (hA i) hx

end OrderedSemiring

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix m n R}
  {y : n → R}

/-- A strictly positive matrix sends a nonzero nonnegative vector to a vector all of whose entries
are strictly positive. -/
theorem mulVec_pos (hA : ∀ i j, 0 < A i j) (hy : 0 ≤ y) (hy0 : y ≠ 0) (i : m) :
    0 < (A *ᵥ y) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hy k))
    ⟨j, Finset.mem_univ j, mul_pos (hA i j) ((hy j).lt_of_ne' hj)⟩

end StrictOrderedSemiring

end Matrix
