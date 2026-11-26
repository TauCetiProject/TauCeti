/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.StarOrthogonal

/-!
# Transposition of star projections

Over commutative coefficients, transposition of square matrices preserves both star projections
and star orthogonality. It acts on the projections as an orthogonality-preserving involution.
-/

public section

open scoped Matrix

/-- Over commutative coefficients, a square matrix is a star projection exactly when its
transpose is a star projection. -/
@[simp]
theorem Matrix.isStarProjection_transpose_iff {n R : Type*} [Fintype n] [AddCommMonoid R]
    [CommMagma R] [Star R] (p : Matrix n n R) :
    IsStarProjection pᵀ ↔ IsStarProjection p := by
  simp only [isStarProjection_iff, isIdempotentElem_iff, ← Matrix.transpose_mul,
    Matrix.transpose_inj, ← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_transpose_iff]

namespace Matrix

variable {n R : Type*} [Fintype n] [AddCommMonoid R] [CommMagma R] [Star R]

variable (n R) in
/-- Transposition permutes the star projections in square matrices over commutative
coefficients. -/
def transposeStarProjection :
    Equiv.Perm {p : Matrix n n R // IsStarProjection p} :=
  (Matrix.transposeAddEquiv n n R).toEquiv.subtypeEquiv
    (p := IsStarProjection) (q := IsStarProjection) fun p ↦ by
      rw [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Matrix.transposeAddEquiv_apply,
        Matrix.isStarProjection_transpose_iff]

/-- The permutation of star projections acts by matrix transpose. -/
@[simp]
theorem transposeStarProjection_apply (p : {p : Matrix n n R // IsStarProjection p}) :
    (transposeStarProjection n R p).val = p.valᵀ := by
  simp only [transposeStarProjection, Equiv.subtypeEquiv_apply,
    AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Matrix.transposeAddEquiv_apply]

/-- Transposing a star projection twice gives back the original projection. -/
@[simp]
theorem transposeStarProjection_apply_apply (p : {p : Matrix n n R // IsStarProjection p}) :
    transposeStarProjection n R (transposeStarProjection n R p) = p := by
  apply Subtype.ext
  simp only [transposeStarProjection_apply, Matrix.transpose_transpose]

/-- Transposition is its own inverse on the star projections. -/
@[simp]
theorem transposeStarProjection_symm :
    (transposeStarProjection n R).symm = transposeStarProjection n R := by
  apply Equiv.ext
  intro p
  rw [Equiv.symm_apply_eq, transposeStarProjection_apply_apply]

end Matrix
