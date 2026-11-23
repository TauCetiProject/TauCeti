/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Star orthogonality of matrices

Transposing both matrices preserves star orthogonality over commutative coefficients.
-/

public section

open scoped Matrix

/-- Over commutative coefficients, transposing two square matrices preserves star orthogonality
in both directions. -/
@[simp]
theorem Matrix.isStarOrtho_transpose_iff {n R : Type*} [Fintype n]
    [NonUnitalCommSemiring R] [StarRing R] (p q : Matrix n n R) :
    IsStarOrtho pᵀ qᵀ ↔ IsStarOrtho p q := by
  simp only [isStarOrtho_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, ← Matrix.transpose_mul,
    Matrix.transpose_eq_zero, and_comm]
