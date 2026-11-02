/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Traces of multiplication operators on square matrices

The square matrices `Matrix n n R` over a commutative semiring form a free module with the matrix
units `single i j 1` as a basis, so the trace of an `R`-linear endomorphism `f` of
`Matrix n n R` is the sum of the diagonal coefficients `f (single i j 1) i j`. This file
evaluates that sum for the operators built from left and right multiplication and
transposition:

* `Z ↦ A * Z * B` has trace `trace A * trace B`;
* in particular left and right multiplication by `A` have trace `card n * trace A`;
* `Z ↦ A * Zᵀ * B` has trace `trace (A * Bᵀ)`.

These are the inputs for computing the Killing form of a matrix Lie algebra, whose adjoint
operators are combinations of left and right multiplications.

## Main results

* `LinearMap.trace_eq_sum_apply_single_apply`: the trace of an endomorphism of the square
  matrices in terms of matrix units.
* `Matrix.trace_mulLeft_comp_mulRight`: the trace of `Z ↦ A * Z * B` is `trace A * trace B`.
* `Matrix.trace_mulLeft`, `Matrix.trace_mulRight`: the traces of left and right multiplication.
* `Matrix.trace_mulLeft_comp_mulRight_comp_transpose`: the trace of `Z ↦ A * Zᵀ * B` is
  `trace (A * Bᵀ)`.
-/

public section

open Matrix

variable {n R : Type*} [Fintype n] [CommSemiring R]

/-- The trace of an endomorphism `f` of the square matrices is the sum over all matrix units
`single i j 1` of the `(i, j)` entry of their image. -/
theorem LinearMap.trace_eq_sum_apply_single_apply [DecidableEq n]
    (f : Matrix n n R →ₗ[R] Matrix n n R) :
    LinearMap.trace R (Matrix n n R) f = ∑ i, ∑ j, f (Matrix.single i j 1) i j := by
  have hrepr (M : Matrix n n R) (p : n × n) : (stdBasis R n n).repr M p = M p.1 p.2 := by
    simp [stdBasis]
  rw [LinearMap.trace_eq_matrix_trace R (stdBasis R n n), Matrix.trace, Fintype.sum_prod_type]
  simp only [diag_apply, LinearMap.toMatrix_apply, stdBasis_eq_single, hrepr]

namespace Matrix

/-- The trace of the operator `Z ↦ A * Z * B` on square matrices is `trace A * trace B`. -/
@[simp]
theorem trace_mulLeft_comp_mulRight (A B : Matrix n n R) :
    LinearMap.trace R (Matrix n n R) (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) =
      A.trace * B.trace := by
  classical
  rw [LinearMap.trace_eq_sum_apply_single_apply]
  simp [Matrix.trace, Matrix.mul_apply, single, Finset.sum_mul_sum, ite_and]

/-- The trace of left multiplication by `A` on square matrices is `card n * trace A`. -/
@[simp]
theorem trace_mulLeft (A : Matrix n n R) :
    LinearMap.trace R (Matrix n n R) (LinearMap.mulLeft R A) = Fintype.card n * A.trace := by
  classical
  simpa [mul_comm] using trace_mulLeft_comp_mulRight A 1

/-- The trace of right multiplication by `B` on square matrices is `card n * trace B`. -/
@[simp]
theorem trace_mulRight (B : Matrix n n R) :
    LinearMap.trace R (Matrix n n R) (LinearMap.mulRight R B) = Fintype.card n * B.trace := by
  classical
  simpa using trace_mulLeft_comp_mulRight 1 B

/-- The trace of the operator `Z ↦ A * Zᵀ * B` on square matrices is `trace (A * Bᵀ)`, the sum
of the products `A i j * B i j` of corresponding entries. -/
@[simp]
theorem trace_mulLeft_comp_mulRight_comp_transpose (A B : Matrix n n R) :
    LinearMap.trace R (Matrix n n R) (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B ∘ₗ
      (transposeLinearEquiv n n R R).toLinearMap) = (A * Bᵀ).trace := by
  classical
  rw [LinearMap.trace_eq_sum_apply_single_apply]
  simp [Matrix.trace, Matrix.mul_apply, single, ite_and]

end Matrix
