/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Orthogonal Lie algebras and skew-symmetric matrices

Mathlib carries two unrelated descriptions of the skew-symmetric real matrices: the orthogonal Lie
algebra `LieAlgebra.Orthogonal.so n ℝ`, cut out by the skew-adjointness condition `Aᵀ = -A` for the
identity bilinear form, and `skewAdjoint (Matrix n n ℝ)`, the skew-adjoint part of the star ring
`Matrix n n ℝ`.  This file identifies them: over `ℝ` the star of a matrix is its conjugate
transpose, which is its transpose.

The bridge is purely algebraic, with no exponential or topological content, so it is stated here
and consumed by the exponential and Lie-subgroup files that compare `so` with star-algebra
statements about the unitary — that is, orthogonal — group of `Matrix n n ℝ`.

A skew-symmetric matrix over any commutative ring has trace zero when `2` is invertible.

## Main results

* `Matrix.trace_eq_zero_of_transpose_eq_neg` gives trace zero for skew-symmetric matrices.
* `Matrix.mem_so_iff_mem_skewAdjoint` identifies the real orthogonal Lie algebra with the
  skew-adjoint matrices.
-/

public section

namespace Matrix

/-- A skew-symmetric matrix has trace zero when `2` is invertible. -/
theorem trace_eq_zero_of_transpose_eq_neg {n R : Type*} [Fintype n] [CommRing R]
    [Invertible (2 : R)] (X : Matrix n n R) (hX : Xᵀ = -X) : trace X = 0 := by
  have htrace : trace X = -trace X := by
    calc
      trace X = trace Xᵀ := (trace_transpose X).symm
      _ = -trace X := by rw [hX, trace_neg]
  have htwo : (2 : R) * trace X = 0 := by
    simpa only [two_mul] using (add_eq_zero_iff_eq_neg.mpr htrace)
  calc
    trace X = ⅟(2 : R) * ((2 : R) * trace X) := by simp
    _ = 0 := by rw [htwo]; simp

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over `ℝ` the orthogonal Lie algebra is the skew-adjoint part of the matrix algebra: the star
of a real matrix is its conjugate transpose, which is its transpose. -/
theorem mem_so_iff_mem_skewAdjoint (A : Matrix n n ℝ) :
    A ∈ LieAlgebra.Orthogonal.so n ℝ ↔ A ∈ skewAdjoint (Matrix n n ℝ) := by
  rw [LieAlgebra.Orthogonal.mem_so, skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end Matrix
