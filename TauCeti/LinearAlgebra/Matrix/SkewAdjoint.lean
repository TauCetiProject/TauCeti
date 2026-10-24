/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrices skew-adjoint for a bilinear form

For a square matrix `J`, Mathlib's `Matrix.IsSkewAdjoint J A` is the condition `Aᵀ * J = J * -A`:
the matrix `A` is skew-adjoint for the bilinear form `B(u, v) = u ⬝ᵥ J v`. This file records
basic facts about such matrices, independent of any Lie theory.

When `J` is invertible, skew-adjointness makes `Aᵀ` conjugate to `-A`, so `A` has trace zero as
soon as `2` is invertible. When `J` is symmetric, every pair of vectors `u`, `v` gives a
skew-adjoint matrix, the matrix `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` sending `x`
to `B(u, x) v - B(v, x) u`.

## Main results

* `Matrix.IsSkewAdjoint.trace_eq_zero`: a matrix skew-adjoint for an invertible matrix has trace
  zero when `2` is invertible.
* `Matrix.isSkewAdjoint_vecMulVec_sub_vecMulVec`: for symmetric `J`, the matrix
  `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` is skew-adjoint for `J`.
* `Matrix.vecMulVec_sub_vecMulVec_mulVec`: that matrix sends `x` to
  `(u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [CommRing R]

/-- **A matrix skew-adjoint for an invertible matrix has trace zero** when `2` is invertible:
skew-adjointness makes `Aᵀ` conjugate to `-A`. -/
theorem IsSkewAdjoint.trace_eq_zero [DecidableEq n] [Invertible (2 : R)] {J A : Matrix n n R}
    (hJ : IsUnit J) (hA : J.IsSkewAdjoint A) : A.trace = 0 := by
  rw [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hA
  have := hJ.invertible
  have h : A.trace = -A.trace := calc
    A.trace = (Aᵀ * J * ⅟J).trace := by
      rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one, trace_transpose]
    _ = (J * (-A * ⅟J)).trace := by rw [hA, Matrix.mul_assoc]
    _ = -A.trace := by
      rw [trace_mul_comm, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one, trace_neg]
  have h2 : (2 : R) * A.trace = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rw [← invOf_mul_cancel_left (2 : R) A.trace, h2, mul_zero]

/-- For a symmetric matrix `J`, the matrix sending `x` to `(u ⬝ᵥ J x) • v - (v ⬝ᵥ J x) • u` is
skew-adjoint for `J`. -/
theorem isSkewAdjoint_vecMulVec_sub_vecMulVec {J : Matrix n n R} (hJ : J.IsSymm) (u v : n → R) :
    J.IsSkewAdjoint (vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)) := by
  have h (w : n → R) : J *ᵥ w = w ᵥ* J := by rw [← vecMul_transpose, hJ.eq]
  rw [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  simp only [transpose_sub, transpose_vecMulVec, Matrix.sub_mul, vecMulVec_mul, Matrix.mul_sub,
    mul_vecMulVec, h, neg_sub]

/-- The matrix `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` sends `x` to
`(u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u`. -/
theorem vecMulVec_sub_vecMulVec_mulVec (J : Matrix n n R) (u v x : n → R) :
    (vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)) *ᵥ x =
      (u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u := by
  simp [sub_mulVec, vecMulVec_mulVec, dotProduct_mulVec]

end Matrix
