/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Kronecker quadratic forms on vectorized matrices

The quadratic form of a Kronecker product `V ⊗ₖ U` on column-stacked matrices is a trace.
For positive semidefinite `U` and `V`, this makes `trace (Tᵀ * U * T * V)` nonnegative.

## Main results

* `Matrix.vec_dotProduct_kronecker_mulVec_vec`: the trace formula for the bilinear form of
  `V ⊗ₖ U` on vectorized matrices.
* `Matrix.IsSymm.vec_dotProduct_kronecker_mulVec_vec`: the same formula for symmetric `V`,
  without the transpose.
* `Matrix.PosSemidef.trace_transpose_mul_mul_mul_nonneg`: nonnegativity of
  `trace (Tᵀ * U * T * V)` for positive semidefinite `U` and `V`.
-/

public section

open scoped Kronecker Matrix

namespace TauCeti

variable {R l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The quadratic form of a Kronecker product on column-stacked matrices is a trace:
`vec A ⬝ᵥ (V ⊗ₖ U) *ᵥ vec B = trace (Aᵀ * U * B * Vᵀ)`. -/
theorem _root_.Matrix.vec_dotProduct_kronecker_mulVec_vec [NonUnitalCommSemiring R]
    (A : Matrix l p R) (U : Matrix l m R) (B : Matrix m n R) (V : Matrix p n R) :
    A.vec ⬝ᵥ (V ⊗ₖ U) *ᵥ B.vec = (Aᵀ * U * B * Vᵀ).trace := by
  rw [Matrix.kronecker_mulVec_vec, Matrix.vec_dotProduct_vec]
  simp only [Matrix.mul_assoc]

/-- For symmetric `V`, the Kronecker quadratic form on column-stacked matrices is
`vec A ⬝ᵥ (V ⊗ₖ U) *ᵥ vec B = trace (Aᵀ * U * B * V)`. -/
theorem _root_.Matrix.IsSymm.vec_dotProduct_kronecker_mulVec_vec [NonUnitalCommSemiring R]
    {V : Matrix n n R} (hV : V.IsSymm) (A : Matrix l n R) (U : Matrix l m R)
    (B : Matrix m n R) : A.vec ⬝ᵥ (V ⊗ₖ U) *ᵥ B.vec = (Aᵀ * U * B * V).trace := by
  rw [Matrix.vec_dotProduct_kronecker_mulVec_vec, hV.eq]

/-- For positive semidefinite `U` and `V`, the covariance quadratic form
`trace (Tᵀ * U * T * V)` is nonnegative. It is the quadratic form of `V ⊗ₖ U` at `vec T`. -/
theorem _root_.Matrix.PosSemidef.trace_transpose_mul_mul_mul_nonneg {U : Matrix m m ℝ}
    {V : Matrix n n ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (T : Matrix m n ℝ) :
    0 ≤ (Tᵀ * U * T * V).trace := by
  simpa only [star_trivial, hV.isHermitian.isSymm.vec_dotProduct_kronecker_mulVec_vec] using
    (hV.kronecker hU).dotProduct_mulVec_nonneg T.vec

end TauCeti
