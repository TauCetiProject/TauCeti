/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Basic properties of Gram matrices and their determinants

The matrix of the inner product `innerₛₗ 𝕜` in a basis `b`, as computed by Mathlib's
`LinearMap.toMatrix₂`, is the Gram matrix `Matrix.gram 𝕜 b` of `b`, with entries `⟪b i, b j⟫`
(`Module.Basis.toMatrix₂_innerₛₗ`). This holds over `ℝ` and `ℂ` alike, in any semi-inner product
space. Over `ℝ` it reads `LinearMap.BilinForm.toMatrix b (innerₗ E) = Matrix.gram ℝ b`
(`LinearMap.BilinForm.toMatrix_innerₗ`), which is the form in which Gram matrices enter the
bilinear-form API, for instance through dual bases.

In a finite-dimensional real or complex semi-inner-product space `E`, any family of vectors indexed
by a finite type of cardinality strictly greater than `finrank 𝕜 E` is linearly dependent, so its
Gram determinant vanishes (`Matrix.det_gram_eq_zero_of_finrank_lt`).
-/

public section

open scoped InnerProductSpace

section Basis

variable {𝕜 E ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of the inner product in a basis `b` is the Gram matrix of `b`. -/
theorem Module.Basis.toMatrix₂_innerₛₗ [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (b : Module.Basis ι 𝕜 E) :
    LinearMap.toMatrix₂ b b (innerₛₗ 𝕜) = Matrix.gram 𝕜 b := by
  ext k l
  rw [LinearMap.toMatrix₂_apply, innerₛₗ_apply_apply, Matrix.gram_apply]

/-- The matrix of the real inner product in a basis `b` is the Gram matrix of `b`. -/
theorem LinearMap.BilinForm.toMatrix_innerₗ [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Module.Basis ι ℝ E) : toMatrix b (innerₗ E) = Matrix.gram ℝ b :=
  b.toMatrix₂_innerₛₗ

end Basis

namespace Matrix

/-- In a finite-dimensional semi-inner-product space of dimension smaller than the cardinality of
the index type, every Gram determinant vanishes. `Module.Finite 𝕜 E` is required because
`Module.finrank` defaults to `0` in infinite dimension. -/
theorem det_gram_eq_zero_of_finrank_lt {𝕜 E n : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Module.Finite 𝕜 E]
    [Fintype n] [DecidableEq n] (h : Module.finrank 𝕜 E < Fintype.card n) (v : n → E) :
    (gram 𝕜 v).det = 0 := by
  by_contra h0
  exact h.not_ge (linearIndependent_of_det_gram_ne_zero h0).fintype_card_le_finrank

end Matrix
