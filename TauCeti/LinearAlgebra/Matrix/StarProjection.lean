/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Transposition of star projections

Transposition of square matrices preserves both star projections and star orthogonality.
These facts let transposition act on the projections as an orthogonality-preserving involution.
-/

public section

open scoped Matrix

namespace Matrix

/-- A square matrix is a star projection exactly when its transpose is a star projection. -/
@[simp]
theorem isStarProjection_transpose_iff {n R : Type*} [Fintype n] [AddCommMonoid R]
    [CommMagma R] [Star R] {p : Matrix n n R} :
    IsStarProjection pᵀ ↔ IsStarProjection p := by
  simp only [isStarProjection_iff', star_eq_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, transpose_inj]

/-- Transposing two square matrices preserves star orthogonality in both directions. -/
@[simp]
theorem isStarOrtho_transpose_iff {n R : Type*} [Fintype n]
    [NonUnitalCommSemiring R] [StarRing R] {p q : Matrix n n R} :
    IsStarOrtho pᵀ qᵀ ↔ IsStarOrtho p q := by
  simp only [isStarOrtho_iff, star_eq_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, transpose_eq_zero,
    and_comm]

end Matrix
