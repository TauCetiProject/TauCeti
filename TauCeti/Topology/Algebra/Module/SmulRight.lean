/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Rank-one maps span the continuous linear maps out of a finite-dimensional space

Let `E` be a finite-dimensional Hausdorff topological vector space over `ℝ`, and `G` any
topological vector space. Every continuous linear map `L : E →L[ℝ] G` is the finite sum of the
rank-one maps `eᵏ ⊗ L(eₖ)`, `w ↦ eᵏ(w) L(eₖ)` (`ContinuousLinearMap.smulRight`), over a basis
`(eₖ)` of `E` with coordinate functionals `(eᵏ)` (`Module.Basis.sum_coord_smulRight`). So a linear
map out of `E →L[ℝ] G` is determined by its values on the rank-one maps `ξ ⊗ v`
(`LinearMap.ext_smulRight`). This is how a linear map on the `G`-valued one-forms at a point is
specified by a formula on decomposable tensors.
-/

public section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E] [T2Space E]
  {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G]

/-- A continuous linear map out of a finite-dimensional space is the sum of the rank-one maps
`eᵏ ⊗ L(eₖ)` over a basis `(eₖ)` and its coordinate functionals `(eᵏ)`. -/
theorem Module.Basis.sum_coord_smulRight {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (L : E →L[ℝ] G) :
    ∑ k, (LinearMap.toContinuousLinearMap (b.coord k)).smulRight (L (b k)) = L := by
  ext w
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  simp_rw [← map_smul, ← map_sum, b.sum_repr]

/-- Linear maps out of the continuous linear maps `E →L[ℝ] G`, for a finite-dimensional `E`,
agree as soon as they agree on the rank-one maps `ξ ⊗ v`. -/
theorem LinearMap.ext_smulRight {W : Type*} [AddCommGroup W] [Module ℝ W]
    {T T' : (E →L[ℝ] G) →ₗ[ℝ] W}
    (h : ∀ (ξ : E →L[ℝ] ℝ) (v : G), T (ξ.smulRight v) = T' (ξ.smulRight v)) : T = T' := by
  refine LinearMap.ext fun L ↦ ?_
  rw [← (Module.finBasis ℝ E).sum_coord_smulRight L]
  simp only [map_sum, h]
