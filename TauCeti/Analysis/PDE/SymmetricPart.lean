/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.UniformEllipticity
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Self-adjoint parts of PDE coefficient matrices

For a real divergence-form coefficient matrix `A`, the quadratic expression
`ξᵀ A ξ` only depends on Mathlib's self-adjoint part `(A + Aᵀ) / 2`. This file
records that bookkeeping in the explicit-constant API from
`TauCeti.Analysis.PDE.UniformEllipticity`.

The main result is `UniformlyEllipticOn.selfAdjointPart`: a uniformly elliptic, possibly
nonsymmetric coefficient field has a self-adjoint part that is uniformly elliptic with the
same constants. This is a small prerequisite for the PDE roadmap's energy-form and Lax--Milgram
lane, where coercivity comes from the symmetric quadratic part while boundedness still controls
the full bilinear form.

## Main declarations

* `TauCeti.PDE.toQuadraticForm'_selfAdjointPart`: symmetrization preserves `ξᵀ A ξ`.
* `TauCeti.PDE.UniformlyEllipticOn.selfAdjointPart`: uniform ellipticity descends to Mathlib's
  self-adjoint part with unchanged constants.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Mathlib's self-adjoint part of a real matrix, written with transpose. -/
lemma selfAdjointPart_eq (A : Matrix n n ℝ) :
    (selfAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A + Aᵀ) := by
  rw [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [invOf_eq_inv]

omit [Fintype n] [DecidableEq n] in
/-- Mathlib's skew-adjoint part of a real matrix, written with transpose. -/
lemma skewAdjointPart_eq (A : Matrix n n ℝ) :
    (skewAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A - Aᵀ) := by
  rw [skewAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [invOf_eq_inv]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise formula for Mathlib's self-adjoint part of a real matrix. -/
lemma selfAdjointPart_apply (A : Matrix n n ℝ) (i j : n) :
    (selfAdjointPart ℝ A : Matrix n n ℝ) i j = (2 : ℝ)⁻¹ * (A i j + A j i) := by
  rw [selfAdjointPart_eq]
  simp [smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise formula for Mathlib's skew-adjoint part of a real matrix. -/
lemma skewAdjointPart_apply (A : Matrix n n ℝ) (i j : n) :
    (skewAdjointPart ℝ A : Matrix n n ℝ) i j = (2 : ℝ)⁻¹ * (A i j - A j i) := by
  rw [skewAdjointPart_eq]
  simp [smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- Mathlib's self-adjoint part of a real matrix is symmetric. -/
lemma isSymm_selfAdjointPart (A : Matrix n n ℝ) :
    ((selfAdjointPart ℝ A : Matrix n n ℝ)).IsSymm := by
  rw [selfAdjointPart_eq]
  exact (Matrix.isSymm_add_transpose_self A).smul (2 : ℝ)⁻¹

omit [Fintype n] [DecidableEq n] in
/-- The transpose of Mathlib's skew-adjoint part is its negative. -/
lemma skewAdjointPart_transpose (A : Matrix n n ℝ) :
    ((skewAdjointPart ℝ A : Matrix n n ℝ))ᵀ = -(skewAdjointPart ℝ A : Matrix n n ℝ) := by
  ext i j
  simp [sub_eq_add_neg]

/-- Transposing a real matrix does not change its quadratic form. -/
@[simp]
lemma toQuadraticForm'_transpose (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    Aᵀ.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct]
  exact Matrix.dotProduct_transpose_mulVec A ξ ξ

/-- The skew-symmetric part has zero quadratic form. -/
@[simp]
lemma toQuadraticForm'_skewAdjointPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (skewAdjointPart ℝ A : Matrix n n ℝ).toQuadraticForm' ξ = 0 := by
  have htranspose := toQuadraticForm'_transpose (skewAdjointPart ℝ A : Matrix n n ℝ) ξ
  rw [skewAdjointPart_transpose] at htranspose
  have hneg :
      (-(skewAdjointPart ℝ A : Matrix n n ℝ)).toQuadraticForm' ξ =
        - (skewAdjointPart ℝ A : Matrix n n ℝ).toQuadraticForm' ξ := by
    simpa using toQuadraticForm'_smul (-1 : ℝ) (skewAdjointPart ℝ A : Matrix n n ℝ) ξ
  linarith

/-- The symmetric part has the same quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_selfAdjointPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (selfAdjointPart ℝ A : Matrix n n ℝ).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [selfAdjointPart_eq, toQuadraticForm'_smul, toQuadraticForm'_eq_dotProduct,
    toQuadraticForm'_eq_dotProduct]
  simp only [add_mulVec, dotProduct_add]
  have htranspose : ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) :=
    Matrix.dotProduct_transpose_mulVec A ξ ξ
  rw [htranspose]
  ring

/-- On the diagonal, the bilinear form attached to the symmetric part agrees with the
bilinear form attached to the original matrix. -/
@[simp]
lemma matrixBilinearForm_selfAdjointPart_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (selfAdjointPart ℝ A : Matrix n n ℝ) ξ ξ =
      matrixBilinearForm A ξ ξ := by
  rw [matrixBilinearForm_self, matrixBilinearForm_self, toQuadraticForm'_selfAdjointPart]

/-- The bilinear form attached to the symmetric part is the average of the two transposed
placements of the original bilinear form. -/
lemma matrixBilinearForm_selfAdjointPart_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (selfAdjointPart ℝ A : Matrix n n ℝ) η ξ =
      (2 : ℝ)⁻¹ * (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) := by
  classical
  rw [selfAdjointPart_eq, matrixBilinearForm_smul_apply, matrixBilinearForm_apply,
    matrixBilinearForm_apply, matrixBilinearForm_apply]
  rw [add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec]

omit [DecidableEq n] in
/-- If a matrix bilinear form is bounded by `Λ`, then the self-adjoint part is bounded by the
same `Λ`. -/
lemma abs_dotProduct_selfAdjointPart_mulVec_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((selfAdjointPart ℝ A : Matrix n n ℝ) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_selfAdjointPart_apply]
  have hηξ : |matrixBilinearForm A η ξ| ≤ Lam * ‖η‖ * ‖ξ‖ := by
    simpa using hA η ξ
  have hξη : |matrixBilinearForm A ξ η| ≤ Lam * ‖ξ‖ * ‖η‖ := by
    simpa using hA ξ η
  have hnorm_eq : Lam * ‖ξ‖ * ‖η‖ = Lam * ‖η‖ * ‖ξ‖ := by ring
  rw [hnorm_eq] at hξη
  calc
    |(2 : ℝ)⁻¹ * (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η)|
        = (2 : ℝ)⁻¹ * |matrixBilinearForm A η ξ + matrixBilinearForm A ξ η| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    _ ≤ (2 : ℝ)⁻¹ * (|matrixBilinearForm A η ξ| + |matrixBilinearForm A ξ η|) := by
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_nonneg.mpr zero_le_two)
    _ ≤ (2 : ℝ)⁻¹ * (Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (inv_nonneg.mpr zero_le_two)
          · exact hηξ
          · exact hξη
    _ = Lam * ‖η‖ * ‖ξ‖ := by ring

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- Taking the pointwise symmetric part preserves uniform ellipticity with the same
constants. -/
lemma selfAdjointPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => (selfAdjointPart ℝ (a x) : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rw [toQuadraticForm'_selfAdjointPart]
    exact h.lower_bound hx ξ
  · exact abs_dotProduct_selfAdjointPart_mulVec_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

end UniformlyEllipticOn

end PDE

end TauCeti
