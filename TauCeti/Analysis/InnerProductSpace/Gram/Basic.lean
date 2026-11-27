/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The Gram matrix as the matrix of the inner product

The matrix of the inner product `innerₛₗ 𝕜` in a basis `b`, as computed by Mathlib's
`LinearMap.toMatrix₂`, is the Gram matrix `Matrix.gram 𝕜 b` of `b`, with entries `⟪b i, b j⟫`
(`Module.Basis.toMatrix₂_innerₛₗ`). This holds over `ℝ` and `ℂ` alike, in any semi-inner product
space. Over `ℝ` it reads `LinearMap.BilinForm.toMatrix b (innerₗ E) = Matrix.gram ℝ b`
(`LinearMap.BilinForm.toMatrix_innerₗ`), which is the form in which Gram matrices enter the
bilinear-form API, for instance through dual bases. In an orthonormal basis it is the identity
matrix (`LinearMap.BilinForm.toMatrix_innerₗ_orthonormalBasis`).
-/

public section

open scoped InnerProductSpace

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

/-- The matrix of the real inner product in an orthonormal basis is the identity matrix. -/
theorem LinearMap.BilinForm.toMatrix_innerₗ_orthonormalBasis [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) : toMatrix b.toBasis (innerₗ E) = 1 := by
  rw [toMatrix_innerₗ, OrthonormalBasis.coe_toBasis, Matrix.gram_eq_one_iff_orthonormal]
  exact b.orthonormal
