/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# Compressing skew-adjoint matrices along maps intertwining two forms

Let `J` and `K` be square matrices, read as bilinear forms, and let `P` and `Q` be rectangular
matrices with `Pᵀ * J = K * Q` and `J * P = Qᵀ * K`. Then `X ↦ Q * X * P` sends matrices
skew-adjoint for `J` to matrices skew-adjoint for `K`.

This is how a skew-adjoint operator is restricted to a summand of an orthogonal decomposition,
with `P` the inclusion of the summand and `Q` the projection onto it. Exchanging the two roles
extends an operator on the summand by zero. No symmetry or nondegeneracy of the forms is needed.

## Main results

* `TauCeti.mul_mul_mem_skewAdjointMatricesLieSubalgebra`: the compression `Q * X * P` of a matrix
  skew-adjoint for `J` is skew-adjoint for `K`.
-/

public section

open Matrix

namespace TauCeti

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- If `P` and `Q` intertwine the forms `J` and `K`, in the sense that `Pᵀ * J = K * Q` and
`J * P = Qᵀ * K`, then the compression `Q * X * P` of a matrix `X` skew-adjoint for `J` is
skew-adjoint for `K`. -/
theorem mul_mul_mem_skewAdjointMatricesLieSubalgebra {J : Matrix n n R} {K : Matrix m m R}
    {P : Matrix n m R} {Q : Matrix m n R} (hP : Pᵀ * J = K * Q) (hQ : J * P = Qᵀ * K)
    {X : Matrix n n R} (hX : X ∈ skewAdjointMatricesLieSubalgebra J) :
    Q * X * P ∈ skewAdjointMatricesLieSubalgebra K := by
  simp only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hX ⊢
  calc
    _ = Pᵀ * (Xᵀ * (Qᵀ * K)) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Pᵀ * (Xᵀ * J) * P := by rw [← hQ, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Pᵀ * J * (-X * P) := by rw [hX, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Q, Matrix.mul_neg, Matrix.neg_mul]

end TauCeti
