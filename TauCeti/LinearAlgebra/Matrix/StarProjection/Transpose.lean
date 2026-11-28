/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Transposition of star projections

Over commutative coefficients, transposition of square matrices preserves both star projections
and star orthogonality. For self-adjoint matrices it preserves zero products when star is
additive and reverses coefficient multiplication. On star projections it is an involution.
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

/-- Over commutative coefficients, transposing two square matrices preserves star orthogonality
in both directions. -/
@[simp]
theorem Matrix.isStarOrtho_transpose_iff {n R : Type*} [Fintype n]
    [NonUnitalCommSemiring R] [StarRing R] (p q : Matrix n n R) :
    IsStarOrtho pᵀ qᵀ ↔ IsStarOrtho p q := by
  simp only [isStarOrtho_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, ← Matrix.transpose_mul,
    Matrix.transpose_eq_zero, and_comm]

/-- Transposition preserves and reflects zero products of self-adjoint square matrices over
commutative coefficients when star preserves addition and reverses multiplication. -/
theorem Matrix.transpose_mul_eq_zero_iff_of_isSelfAdjoint {n R : Type*} [Fintype n]
    [AddCommMonoid R] [CommMagma R] [StarAddMonoid R]
    (hstar : ∀ a b : R, star (a * b) = star b * star a) (p q : Matrix n n R)
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) : pᵀ * qᵀ = 0 ↔ p * q = 0 := by
  have hconj : (q * p)ᴴ = pᴴ * qᴴ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, hstar]
  rw [← Matrix.transpose_mul, Matrix.transpose_eq_zero,
    ← Matrix.conjTranspose_eq_zero (M := q * p), hconj, hp.isHermitian.eq, hq.isHermitian.eq]

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
