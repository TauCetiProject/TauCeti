/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram matrices under a change of family

For a finite family `v` in an inner product space over `𝕜` (`ℝ` or `ℂ`) and a matrix `U`, the
family `w k = ∑ j, U k j • v j` has Gram matrix `U.map conj * gram 𝕜 v * Uᵀ`, by
sesquilinearity of the inner product (conjugate-linear in the first argument); `U` may be
rectangular. For square `U`, taking determinants,
`det (gram 𝕜 w) = ‖det U‖ ^ 2 * det (gram 𝕜 v)`, and over `ℝ` this reads
`det (gram ℝ w) = (det U) ^ 2 * det (gram ℝ v)`.

Neither linear independence of `v` nor any hypothesis on the dimension of the space is needed: for
dependent `v` both determinants vanish. When the family is the rows of a matrix `A` in Euclidean
space the real identity is `Matrix.det_mul_transpose_mul_left` in
`TauCeti.LinearAlgebra.Matrix.Gram`; the statements here concern a family in an arbitrary inner
product space, where no coordinate matrix is given.

## Main results

* `Matrix.gram_sum_smul`: the Gram matrix of `fun k ↦ ∑ j, U k j • v j` is
  `U.map conj * gram 𝕜 v * Uᵀ`, for a possibly rectangular `U`.
* `Matrix.det_gram_sum_smul`: its determinant is `‖det U‖ ^ 2 * det (gram 𝕜 v)`.
* `Matrix.det_gram_matrix_smul`: over `ℝ`, the determinant is `det U ^ 2 * det (gram ℝ v)`.
* `Matrix.det_gram_sum_smul_of_det_eq_one`, `Matrix.det_gram_smul`: a change of determinant one,
  such as a unitriangular one, preserves the Gram determinant, and rescaling `v i` by `r i`
  multiplies it by `∏ i, ‖r i‖ ^ 2`.

## References

* J. S. Milne, *Algebraic Number Theory*, Chapter 2, Review of bilinear forms, formula (6): for a
  bilinear form and a family `f_k = ∑_i a_{ki} e_i`, the matrix of values on the `f` is
  `A (ψ(e_i, e_j)) Aᵀ`.
-/

public section

namespace Matrix

open Finset

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- **The Gram matrix under a change of family.** The Gram matrix of `w k = ∑ j, U k j • v j` is
`U.map conj * gram 𝕜 v * Uᵀ`; the conjugate appears because the inner product is conjugate-linear
in its first argument. The coefficient matrix `U` may be rectangular: the new family `w` can have
any index type `κ`. -/
theorem gram_sum_smul {κ : Type*} (U : Matrix κ ι 𝕜) (v : ι → E) :
    gram 𝕜 (fun i ↦ ∑ j, U i j • v j) = U.map (starRingEnd 𝕜) * gram 𝕜 v * Uᵀ := by
  ext i k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.mul_apply, map_apply, transpose_apply, sum_mul, mul_sum]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ mul_comm _ _

variable [DecidableEq ι]

/-- **The Gram determinant under a change of family.** For `w i = ∑ j, U i j • v j`,
`det (gram 𝕜 w) = ‖det U‖ ^ 2 * det (gram 𝕜 v)`, with no independence or dimension
hypothesis. -/
theorem det_gram_sum_smul (U : Matrix ι ι 𝕜) (v : ι → E) :
    (gram 𝕜 (fun i ↦ ∑ j, U i j • v j)).det = ((‖U.det‖ ^ 2 : ℝ) : 𝕜) * (gram 𝕜 v).det := by
  -- Conjugating the entries conjugates the determinant: `U.map conj` is `Uᴴᵀ`, so this is
  -- `det_transpose` followed by Mathlib's `det_conjTranspose`.
  have hconj : (U.map (starRingEnd 𝕜)).det = starRingEnd 𝕜 U.det :=
    (det_transpose Uᴴ).trans (det_conjTranspose U)
  -- Expand the Gram matrix of the new family and split the determinant of the product.
  rw [gram_sum_smul, det_mul, det_mul, det_transpose, hconj]
  -- The two factors `conj (det U)` and `det U` combine to `‖det U‖ ^ 2`.
  rw [mul_right_comm, RCLike.conj_mul, RCLike.ofReal_pow]

/-- **The real Gram determinant under a change of family.** For `w i = ∑ j, U i j • v j` in a real
inner product space, `det (gram ℝ w) = det U ^ 2 * det (gram ℝ v)`, with no independence or
dimension hypothesis. -/
theorem det_gram_matrix_smul {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (U : Matrix ι ι ℝ) (v : ι → F) :
    (gram ℝ (fun i ↦ ∑ j, U i j • v j)).det = U.det ^ 2 * (gram ℝ v).det := by
  simp [det_gram_sum_smul, sq_abs]

/-- A change of family of determinant one, such as an upper or lower unitriangular one, preserves
the Gram determinant. -/
theorem det_gram_sum_smul_of_det_eq_one {U : Matrix ι ι 𝕜} (hU : U.det = 1) (v : ι → E) :
    (gram 𝕜 (fun i ↦ ∑ j, U i j • v j)).det = (gram 𝕜 v).det := by
  rw [det_gram_sum_smul, hU, norm_one, one_pow, RCLike.ofReal_one, one_mul]

/-- Rescaling the vector `v i` by `r i` multiplies the Gram determinant by `∏ i, ‖r i‖ ^ 2`. -/
theorem det_gram_smul (r : ι → 𝕜) (v : ι → E) :
    (gram 𝕜 (fun i ↦ r i • v i)).det = ((∏ i, ‖r i‖ ^ 2 : ℝ) : 𝕜) * (gram 𝕜 v).det := by
  have h := det_gram_sum_smul (diagonal r) v
  simp only [diagonal_apply, ite_smul, zero_smul, sum_ite_eq, mem_univ, ite_true, det_diagonal,
    norm_prod, ← prod_pow] at h
  exact h

end Matrix
