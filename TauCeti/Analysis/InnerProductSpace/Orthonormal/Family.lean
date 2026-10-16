/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame

/-!
# Coordinate isometries of orthonormal families

The synthesis map of an orthonormal family is an isometry from Euclidean coefficient space into
the ambient inner-product space. Its coordinate formula and action on the standard basis make the
identified finite-dimensional subspace directly usable in operator constructions. In the other
direction, Bessel's inequality makes the analysis map of an orthonormal family a contraction.

The orthogonal projection onto the span of a finite orthonormal family is `x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ`,
synthesis after analysis, that is, the frame operator of the family. So Bessel's inequality
becomes an equality on the span: `‖P x‖² = ∑ᵢ ‖⟪vᵢ, x⟫‖²`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {v : ι → E}

/-- The synthesis map of an orthonormal family is a linear isometry from Euclidean coefficient
space into its ambient inner-product space. -/
def synthesisMapIsometry (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E :=
  (TauCeti.synthesisMap 𝕜 v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun ι 𝕜).toBasis)
    (EuclideanSpace.basisFun ι 𝕜).orthonormal <| by
    classical
    simpa only [OrthonormalBasis.coe_toBasis, Function.comp_def,
      EuclideanSpace.basisFun_apply, TauCeti.synthesisMap_single, one_smul] using hv

/-- The underlying linear map of the coordinate isometry is the synthesis map. -/
@[simp]
theorem synthesisMapIsometry_toLinearMap (hv : Orthonormal 𝕜 v) :
    hv.synthesisMapIsometry.toLinearMap = TauCeti.synthesisMap 𝕜 v := by
  unfold synthesisMapIsometry
  exact LinearMap.isometryOfOrthonormal_toLinearMap _ _ _

/-- The coordinate isometry sends a coefficient vector to the corresponding linear combination
of the orthonormal family. -/
@[simp]
theorem synthesisMapIsometry_apply (hv : Orthonormal 𝕜 v)
    (a : EuclideanSpace 𝕜 ι) :
    hv.synthesisMapIsometry a = ∑ i, a i • v i := by
  rw [← LinearIsometry.coe_toLinearMap, synthesisMapIsometry_toLinearMap,
    TauCeti.synthesisMap_apply]

open Classical in
/-- The coordinate isometry sends the single-coordinate vector supported at `i` with coefficient
`c` to `c • v i`. -/
@[simp high]
theorem synthesisMapIsometry_single (hv : Orthonormal 𝕜 v) (i : ι) (c : 𝕜) :
    hv.synthesisMapIsometry (EuclideanSpace.single i c) = c • v i := by
  classical
  rw [synthesisMapIsometry_apply]
  simp

/-- **Bessel's inequality** for the analysis map of an orthonormal family: the coefficient vector
`(⟪vᵢ, x⟫)ᵢ` has norm at most `‖x‖`. -/
theorem norm_analysisMap_le (hv : Orthonormal 𝕜 v) (x : E) :
    ‖TauCeti.analysisMap 𝕜 v x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg x) two_ne_zero).mp <| by
    rw [TauCeti.norm_analysisMap_sq]
    exact hv.sum_inner_products_le x

/-- The orthogonal projection onto the span `U` of a finite orthonormal family is
`x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ`. -/
theorem starProjection_apply_eq_sum (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range v) = U) (x : E) :
    U.starProjection x = ∑ i, ⟪v i, x⟫_𝕜 • v i := by
  subst hU
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    fun w hw ↦ ?_
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hw
  simp [inner_sum, inner_smul_right, inner_sub_left, hv.inner_left_fintype]

/-- The orthogonal projection onto the span `U` of a finite orthonormal family is its frame
operator, synthesis after analysis. -/
theorem toLinearMap_starProjection_eq_frameOperator (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range v) = U) :
    (U.starProjection : E →ₗ[𝕜] E) = TauCeti.frameOperator 𝕜 v := by
  ext x
  simp [hv.starProjection_apply_eq_sum hU]

/-- **Parseval's identity** on the span `U` of a finite orthonormal family: the orthogonal
projection of `x` onto `U` has squared norm `∑ᵢ ‖⟪vᵢ, x⟫‖²`. -/
theorem norm_starProjection_sq_eq_sum (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range v) = U) (x : E) :
    ‖U.starProjection x‖ ^ 2 = ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  have h : U.starProjection x = hv.synthesisMapIsometry (TauCeti.analysisMap 𝕜 v x) := by
    simp [hv.starProjection_apply_eq_sum hU, TauCeti.analysisMap_apply]
  rw [h, LinearIsometry.norm_map, TauCeti.norm_analysisMap_sq]

end Orthonormal
