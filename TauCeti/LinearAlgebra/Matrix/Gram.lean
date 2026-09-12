/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.IsSymm` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

/-!
# Gram matrices, forms, and matrix reflection

This file records a factorization of finite Gram sums and the basic symmetry and quadratic-form
preservation identities for the bilinear and quadratic forms attached to a symmetric matrix.

## Main results

* `TauCeti.sum_vecMulVec_eq_transpose_mul` identifies a finite sum of vector outer products with
  the Gram matrix of the matrix whose rows are those vectors.
* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the value
  `(v ᵥ* M) ⬝ᵥ v` of the form at every vector.
-/

public section

namespace TauCeti

open _root_.Matrix

/-- The sum of the outer products of a finite family of vectors is the Gram matrix of the matrix
whose rows are those vectors. -/
theorem sum_vecMulVec_eq_transpose_mul {ι m R : Type*} [Fintype ι] [Mul R] [AddCommMonoid R]
    (v : ι → m → R) :
    ∑ i, Matrix.vecMulVec (v i) (v i) = (Matrix.of v)ᵀ * Matrix.of v := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]

variable {n : Type*} [Fintype n]

/-- The bilinear form carried by a symmetric matrix is symmetric. -/
theorem vecMul_dotProduct_comm {R : Type*} [NonUnitalCommSemiring R] {M : Matrix n n R}
    (hM : M.IsSymm) (v w : n → R) :
    (v ᵥ* M) ⬝ᵥ w = (w ᵥ* M) ⬝ᵥ v := by
  rw [← dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hM.eq]

variable {R : Type*} [CommRing R] {M : Matrix n n R}

/-- **Reflection in a vector of norm two preserves the value of the quadratic form.** For a
symmetric matrix `M` and a vector `u` with `(u ᵥ* M) ⬝ᵥ u = 2`, reflection in `u` preserves the
value `(v ᵥ* M) ⬝ᵥ v` of the form at every vector `v`. This is what makes a family of norm-two
vectors stable under its own reflections once the family exhausts the norm-two vectors. -/
theorem reflect_vecMul_dotProduct_self (hM : M.IsSymm) {u : n → R} (hu : (u ᵥ* M) ⬝ᵥ u = 2)
    (v : n → R) :
    ((v - ((v ᵥ* M) ⬝ᵥ u) • u) ᵥ* M) ⬝ᵥ (v - ((v ᵥ* M) ⬝ᵥ u) • u) = (v ᵥ* M) ⬝ᵥ v := by
  simp only [sub_vecMul, smul_vecMul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hu, vecMul_dotProduct_comm hM u v]
  ring

end TauCeti
