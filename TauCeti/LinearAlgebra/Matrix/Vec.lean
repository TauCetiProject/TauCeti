/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Vectorized matrices: linear structure and Kronecker quadratic forms

Column-stacking vectorization `Matrix.vec` is a linear equivalence between `m × n` matrices and
functions on `n × m`, whose inverse puts `v (j, i)` at entry `(i, j)`.

The quadratic form of a Kronecker product `V ⊗ₖ U` on column-stacked matrices is a trace.
For positive semidefinite `U` and `V`, this makes `trace (Tᵀ * U * T * V)` nonnegative.

## Main results

* `Matrix.vecLinearEquiv`: vectorization as a linear equivalence.
* `Matrix.vec_dotProduct_kronecker_mulVec_vec`: the trace formula for the bilinear form of
  `V ⊗ₖ U` on vectorized matrices.
* `Matrix.IsSymm.vec_dotProduct_kronecker_mulVec_vec`: the same formula for symmetric `V`,
  without the transpose.
* `Matrix.PosSemidef.trace_transpose_mul_mul_mul_nonneg`: nonnegativity of
  `trace (Tᵀ * U * T * V)` for positive semidefinite `U` and `V`.
* `Matrix.eq_of_star_vec_dotProduct_mulVec_vec`: a matrix acting on column-stacked matrices is
  determined by its sesquilinear form on column-stacked matrices.
-/

public section

open scoped Kronecker Matrix

namespace Matrix

section LinearEquiv

variable {R m n : Type*} (S : Type*) [Semiring S] [AddCommMonoid R] [Module S R]

/-- Column-stacking vectorization `Matrix.vec` as a linear equivalence. Its inverse puts the
coordinate `v (j, i)` at the entry `(i, j)`. -/
@[expose] def vecLinearEquiv : Matrix m n R ≃ₗ[S] (n × m → R) where
  toFun := vec
  invFun v := of fun i j ↦ v (j, i)
  map_add' := vec_add
  map_smul' := vec_smul
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem vecLinearEquiv_apply (A : Matrix m n R) : vecLinearEquiv S A = A.vec := rfl

@[simp]
theorem vecLinearEquiv_symm_apply (v : n × m → R) (i : m) (j : n) :
    (vecLinearEquiv S).symm v i j = v (j, i) := rfl

@[simp]
theorem vec_vecLinearEquiv_symm (v : n × m → R) : ((vecLinearEquiv S).symm v).vec = v := rfl

end LinearEquiv

variable {R l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The quadratic form of a Kronecker product on column-stacked matrices is a trace:
`vec A ⬝ᵥ (V ⊗ₖ U) *ᵥ vec B = trace (Aᵀ * U * B * Vᵀ)`. -/
theorem vec_dotProduct_kronecker_mulVec_vec [NonUnitalCommSemiring R]
    (A : Matrix l p R) (U : Matrix l m R) (B : Matrix m n R) (V : Matrix p n R) :
    A.vec ⬝ᵥ (V ⊗ₖ U) *ᵥ B.vec = (Aᵀ * U * B * Vᵀ).trace := by
  rw [Matrix.kronecker_mulVec_vec, Matrix.vec_dotProduct_vec]
  simp only [Matrix.mul_assoc]

/-- For symmetric `V`, the Kronecker quadratic form on column-stacked matrices is
`vec A ⬝ᵥ (V ⊗ₖ U) *ᵥ vec B = trace (Aᵀ * U * B * V)`. -/
theorem IsSymm.vec_dotProduct_kronecker_mulVec_vec [NonUnitalCommSemiring R]
    {V : Matrix n n R} (hV : V.IsSymm) (A : Matrix l n R) (U : Matrix l m R)
    (B : Matrix m n R) : A.vec ⬝ᵥ (V ⊗ₖ U) *ᵥ B.vec = (Aᵀ * U * B * V).trace := by
  rw [Matrix.vec_dotProduct_kronecker_mulVec_vec, hV.eq]

/-- For positive semidefinite `U` and `V`, the covariance quadratic form
`trace (Tᵀ * U * T * V)` is nonnegative. It is the quadratic form of `V ⊗ₖ U` at `vec T`. -/
theorem PosSemidef.trace_transpose_mul_mul_mul_nonneg {U : Matrix m m ℝ}
    {V : Matrix n n ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (T : Matrix m n ℝ) :
    0 ≤ (Tᵀ * U * T * V).trace := by
  simpa only [star_trivial, hV.isHermitian.isSymm.vec_dotProduct_kronecker_mulVec_vec] using
    (hV.kronecker hU).dotProduct_mulVec_nonneg T.vec

/-- Two matrices acting on column-stacked matrices agree when their sesquilinear forms agree on
all column-stacked matrices. -/
theorem eq_of_star_vec_dotProduct_mulVec_vec [NonAssocSemiring R] [StarRing R]
    {M N : Matrix (n × m) (p × l) R}
    (h : ∀ (X : Matrix m n R) (Y : Matrix l p R),
      star X.vec ⬝ᵥ M *ᵥ Y.vec = star X.vec ⬝ᵥ N *ᵥ Y.vec) :
    M = N := by
  classical
  ext x y
  simpa [Matrix.vec_single] using h (Matrix.single x.2 x.1 1) (Matrix.single y.2 y.1 1)

end Matrix
