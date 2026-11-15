/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Traces of products with an inverse

For an invertible matrix `G` and any square matrix `P`, the trace of `G⁻¹ (Pᵀ G + G P)` is
`2 trace P`. This is the algebra that turns Jacobi's formula into the derivative of a Gram
determinant: if a Gram matrix varies as `dG = Pᵀ G + G P`, then `d (det G) = 2 det G trace P`.

## Main results

* `Matrix.trace_nonsing_inv_mul_transpose_mul_add_mul`: `trace (G⁻¹ (Pᵀ G + G P)) = 2 trace P`.
* `LinearMap.trace_ringInverse_mul_eq_matrix_trace`: the matrix formula for `trace (A⁻¹ B)`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- For an invertible matrix `G`, the trace of `G⁻¹ (Pᵀ G + G P)` is `2 trace P`. -/
theorem trace_nonsing_inv_mul_transpose_mul_add_mul {G : Matrix n n R} (hG : IsUnit G.det)
    (P : Matrix n n R) : (G⁻¹ * (Pᵀ * G + G * P)).trace = 2 * P.trace := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG,
    Matrix.one_mul, Matrix.trace_add, Matrix.trace_conj' ((Matrix.isUnit_iff_isUnit_det G).mpr hG),
    Matrix.trace_transpose, two_mul]

end Matrix

namespace LinearMap

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommMonoid M] [Module R M]

/-- The trace of the ring inverse of `A` composed with `B` equals the trace of the corresponding
matrix product. -/
theorem trace_ringInverse_mul_eq_matrix_trace (b : Module.Basis ι R M) (A B : M →ₗ[R] M) :
    trace R M (Ring.inverse A * B) = Matrix.trace ((toMatrix b b A)⁻¹ * toMatrix b b B) := by
  rw [trace_eq_matrix_trace R b, toMatrix_mul, toMatrix_ringInverse]

end LinearMap
