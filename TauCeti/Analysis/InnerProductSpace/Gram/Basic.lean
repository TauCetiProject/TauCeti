/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The Gram matrix as the matrix of the inner product

The matrix of the inner product `innerₛₗ 𝕜` in a basis `b`, as computed by Mathlib's
`LinearMap.toMatrix₂`, is the Gram matrix `Matrix.gram 𝕜 b` of `b`, with entries `⟪b i, b j⟫`
(`Module.Basis.toMatrix₂_innerₛₗ`). This holds over `ℝ` and `ℂ` alike, in any semi-inner product
space. Over `ℝ` it reads `LinearMap.BilinForm.toMatrix b (innerₗ E) = Matrix.gram ℝ b`
(`LinearMap.BilinForm.toMatrix_innerₗ`), which is the form in which Gram matrices enter the
bilinear-form API, for instance through dual bases.

For families `u, v : ι → E` that are pairwise orthogonal across the two families,
`Matrix.gram 𝕜 (u + v) = Matrix.gram 𝕜 u + Matrix.gram 𝕜 v` (`Matrix.gram_add_of_inner_eq_zero`).
Consequently, for nested subspaces `K ≤ K'` admitting orthogonal projections, projecting a family
onto `Kᗮ` rather than `K'ᗮ` increases its Gram matrix by the Gram matrix of the projection
difference `K'.starProjection - K.starProjection`
(`Matrix.gram_starProjection_orthogonal_sub_of_le`).
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

section Orthogonal

/-- The Gram matrix of a sum of two families of vectors that are pairwise orthogonal across the two
families is the sum of their Gram matrices. -/
theorem Matrix.gram_add_of_inner_eq_zero {𝕜 E ι : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {u v : ι → E}
    (h : ∀ i j, ⟪u i, v j⟫_𝕜 = 0) :
    Matrix.gram 𝕜 (u + v) = Matrix.gram 𝕜 u + Matrix.gram 𝕜 v := by
  ext i j
  have h' : ⟪v i, u j⟫_𝕜 = 0 := by
    rw [← inner_conj_symm, h j i, map_zero]
  simp [Pi.add_apply, inner_add_left, inner_add_right, h i j, h']

/-- For nested subspaces `K ≤ K'` admitting orthogonal projections, projecting onto `Kᗮ` rather
than `K'ᗮ` increases the Gram matrix by the Gram matrix of the projection difference
`K'.starProjection - K.starProjection`. -/
theorem Matrix.gram_starProjection_orthogonal_sub_of_le {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {K K' : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] (h : K ≤ K') (v : ι → E) :
    Matrix.gram 𝕜 (fun i ↦ Kᗮ.starProjection (v i)) -
        Matrix.gram 𝕜 (fun i ↦ K'ᗮ.starProjection (v i)) =
      Matrix.gram 𝕜 (fun i ↦ K'.starProjection (v i) - K.starProjection (v i)) := by
  have hsplit : (fun i ↦ Kᗮ.starProjection (v i)) =
      (fun i ↦ K'ᗮ.starProjection (v i)) +
        (fun i ↦ K'.starProjection (v i) - K.starProjection (v i)) := by
    ext i
    simp [Submodule.starProjection_orthogonal_val]
  rw [hsplit, Matrix.gram_add_of_inner_eq_zero, add_sub_cancel_left]
  intro i j
  exact Submodule.inner_left_of_mem_orthogonal
    (K'.sub_mem (K'.starProjection_apply_mem _) (h (K.starProjection_apply_mem _)))
    (K'ᗮ.starProjection_apply_mem _)

end Orthogonal
