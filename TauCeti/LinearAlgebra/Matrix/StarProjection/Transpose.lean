/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Transposition of star projections

Over commutative coefficients, transposition of square matrices preserves both star projections
and star orthogonality. It acts on the projections as an orthogonality-preserving involution.
-/

public section

open scoped Matrix

namespace Matrix

/-- Over commutative coefficients, a square matrix is a star projection exactly when its
transpose is a star projection. -/
@[simp]
theorem isStarProjection_transpose_iff {n R : Type*} [Fintype n] [AddCommMonoid R]
    [CommMagma R] [Star R] (p : Matrix n n R) :
    IsStarProjection pᵀ ↔ IsStarProjection p := by
  simp only [isStarProjection_iff, isIdempotentElem_iff, ← transpose_mul, transpose_inj,
    ← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_transpose_iff]

/-- Over commutative coefficients, transposing two square matrices preserves star orthogonality
in both directions. -/
@[simp]
theorem isStarOrtho_transpose_iff {n R : Type*} [Fintype n]
    [NonUnitalCommSemiring R] [StarRing R] (p q : Matrix n n R) :
    IsStarOrtho pᵀ qᵀ ↔ IsStarOrtho p q := by
  simp only [isStarOrtho_iff, star_eq_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, transpose_eq_zero,
    and_comm]

/-- Transposition permutes the star projections in square matrices over commutative
coefficients. -/
def transposeStarProjection (n R : Type*) [Fintype n] [AddCommMonoid R] [CommMagma R] [Star R] :
    Equiv.Perm {p : Matrix n n R // IsStarProjection p} :=
  (transposeAddEquiv n n R).toEquiv.subtypeEquiv
    (p := IsStarProjection) (q := IsStarProjection) fun p ↦ by
      have hcoe : ⇑(transposeAddEquiv n n R).toEquiv = ⇑(transposeAddEquiv n n R) := rfl
      rw [hcoe, Matrix.transposeAddEquiv_apply, isStarProjection_transpose_iff]

@[simp]
theorem transposeStarProjection_apply {n R : Type*} [Fintype n] [AddCommMonoid R]
    [CommMagma R] [Star R] (p : {p : Matrix n n R // IsStarProjection p}) :
    (transposeStarProjection n R p).val = p.valᵀ := by
  have hcoe : ⇑(transposeAddEquiv n n R).toEquiv = ⇑(transposeAddEquiv n n R) := rfl
  simp only [transposeStarProjection, Equiv.subtypeEquiv_apply, hcoe,
    Matrix.transposeAddEquiv_apply]

/-- The transpose permutation preserves zero products of star projections in both directions. -/
theorem transposeStarProjection_mul_eq_zero_iff {n R : Type*} [Fintype n]
    [NonUnitalCommSemiring R] [StarRing R] (p q : {p : Matrix n n R // IsStarProjection p}) :
    (transposeStarProjection n R p).val * (transposeStarProjection n R q).val = 0 ↔
      p.val * q.val = 0 := by
  rw [← (transposeStarProjection n R p).property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero
      (transposeStarProjection n R q).property.isSelfAdjoint,
    ← p.property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero q.property.isSelfAdjoint]
  simp only [transposeStarProjection_apply, isStarOrtho_transpose_iff]

end Matrix
