/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.IsSymm` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

/-!
# Gram forms, matrix reflection and Gram determinants

This file records the basic symmetry and quadratic-form preservation identities for the bilinear
and quadratic forms attached to a symmetric matrix, and the basic facts about the Gram
determinant `det (A * Aᵀ)` of the rows of a matrix `A`.

## Main results

* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the value
  `(v ᵥ* M) ⬝ᵥ v` of the form at every vector.
* `Matrix.det_mul_transpose_mul_left`: the Gram determinant of `B * A` is `det B ^ 2` times that
  of `A`.
* `Matrix.det_mul_transpose_ne_zero_iff`: over a linearly ordered commutative ring, the Gram
  determinant `det (A * Aᵀ)` is nonzero exactly when the rows of `A` are linearly independent.
-/

public section

namespace TauCeti

open _root_.Matrix

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

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- The Gram determinant of the rows of `B * A` is `det B ^ 2` times that of `A`. -/
theorem det_mul_transpose_mul_left [CommRing R] (B : Matrix m m R) (A : Matrix m n R) :
    (B * A * (B * A)ᵀ).det = B.det ^ 2 * (A * Aᵀ).det := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, det_mul, det_mul, det_transpose]
  ring

/-- Over a linearly ordered commutative ring, the Gram determinant `det (A * Aᵀ)` of the rows of
`A` is nonzero exactly when the rows are linearly independent. -/
theorem det_mul_transpose_ne_zero_iff [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {A : Matrix m n R} : (A * Aᵀ).det ≠ 0 ↔ LinearIndependent R A.row := by
  have key (v : m → R) : v ᵥ* (A * Aᵀ) = 0 ↔ v ᵥ* A = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [← vecMul_vecMul, h, zero_vecMul]⟩
    have := congr($h ⬝ᵥ v)
    rw [← vecMul_vecMul, ← dotProduct_mulVec, mulVec_transpose] at this
    simpa using this
  rw [← vecMul_injective_iff, Ne, ← exists_vecMul_eq_zero_iff, ← coe_vecMulLinear,
    injective_iff_map_eq_zero]
  simp only [key, vecMulLinear_apply]
  grind

end Matrix
