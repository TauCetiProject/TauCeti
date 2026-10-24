/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Basic.Real.Star

/-!
# Basic facts about the orthogonal Lie algebras

Mathlib carries two unrelated descriptions of the skew-symmetric real matrices: the orthogonal Lie
algebra `LieAlgebra.Orthogonal.so n ℝ`, cut out by the skew-adjointness condition `Aᵀ = -A` for the
identity bilinear form, and `skewAdjoint (Matrix n n ℝ)`, the skew-adjoint part of the star ring
`Matrix n n ℝ`.  This file identifies them: over `ℝ` the star of a matrix is its conjugate
transpose, which is its transpose.

The bridge is purely algebraic, with no exponential or topological content, so it is stated here
and consumed by the exponential and Lie-subgroup files that compare `so` with star-algebra
statements about the unitary — that is, orthogonal — group of `Matrix n n ℝ`.

The file also records that the Gram matrix `LieAlgebra.Orthogonal.indefiniteDiagonal p q R` of
the indefinite form, which cuts out `LieAlgebra.Orthogonal.so' p q R`, is invertible.

## Main results

* `Matrix.mem_so_iff_mem_skewAdjoint` identifies the real orthogonal Lie algebra with the
  skew-adjoint matrices.
* `LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal`: the Gram matrix of the indefinite form is
  invertible.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over `ℝ` the orthogonal Lie algebra is the skew-adjoint part of the matrix algebra: the star
of a real matrix is its conjugate transpose, which is its transpose. -/
theorem mem_so_iff_mem_skewAdjoint (A : Matrix n n ℝ) :
    A ∈ LieAlgebra.Orthogonal.so n ℝ ↔ A ∈ skewAdjoint (Matrix n n ℝ) := by
  rw [LieAlgebra.Orthogonal.mem_so, skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end Matrix

namespace LieAlgebra.Orthogonal

variable {p q R : Type*} [DecidableEq p] [DecidableEq q] [Fintype p] [Fintype q] [CommRing R]

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form is invertible; it is its
own inverse. -/
theorem isUnit_indefiniteDiagonal : IsUnit (indefiniteDiagonal p q R) := by
  have h : indefiniteDiagonal p q R * indefiniteDiagonal p q R = 1 := by
    rw [indefiniteDiagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext (i | i) <;> simp
  let := invertibleOfRightInverse _ _ h
  exact isUnit_of_invertible _

end LieAlgebra.Orthogonal
