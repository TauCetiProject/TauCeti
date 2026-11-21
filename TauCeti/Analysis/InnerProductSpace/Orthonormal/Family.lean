/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.InnerProductSpace.Frame.Basic
import TauCeti.LinearAlgebra.Matrix.Module

/-!
# Coordinate isometries of orthonormal families

The synthesis map of an orthonormal family is an isometry from Euclidean coefficient space into
the ambient inner-product space. Its coordinate formula and action on the standard basis make the
identified finite-dimensional subspace directly usable in operator constructions. In the other
direction, Bessel's inequality makes the analysis map of an orthonormal family a contraction.

The orthogonal projection onto the span of a finite orthonormal family is `x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ`,
synthesis after analysis, that is, the frame operator of the family. So Bessel's inequality
becomes an equality on the span: `‖P x‖² = ∑ᵢ ‖⟪vᵢ, x⟫‖²`. The same formula shows that the
projection onto the span of a continuous family of orthonormal families depends continuously on
the parameter (`Orthonormal.continuous_starProjection`).

Combining an orthonormal family with the rows of a matrix `A` gives an orthonormal family exactly
when `A * Aᴴ = 1` (`Orthonormal.orthonormal_sum_smul_iff`); for square matrices this
identifies the changes of orthonormal frame with the unitary group
(`Orthonormal.orthonormal_sum_smul_iff_mem_unitaryGroup`), and a unitary change of frame
preserves and reflects orthonormality (`TauCeti.orthonormal_sum_smul_iff_of_mem_unitaryGroup`).
-/

public section

noncomputable section

open scoped InnerProductSpace Matrix

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

/-- The range of the coordinate synthesis isometry is the span of the orthonormal family. -/
theorem range_synthesisMapIsometry (hv : Orthonormal 𝕜 v) :
    LinearMap.range hv.synthesisMapIsometry.toLinearMap = Submodule.span 𝕜 (Set.range v) := by
  rw [synthesisMapIsometry_toLinearMap, TauCeti.range_synthesisMap]

/-- The adjoint of the coordinate synthesis isometry reads inner products with the family. -/
@[simp]
theorem adjoint_synthesisMapIsometry_apply [CompleteSpace E] (hv : Orthonormal 𝕜 v)
    (y : E) (i : ι) :
    (ContinuousLinearMap.adjoint hv.synthesisMapIsometry.toContinuousLinearMap y) i =
      ⟪v i, y⟫_𝕜 := by
  classical
  have h := EuclideanSpace.inner_single_left i (1 : 𝕜)
    (ContinuousLinearMap.adjoint hv.synthesisMapIsometry.toContinuousLinearMap y)
  rw [map_one, one_mul, ContinuousLinearMap.adjoint_inner_right] at h
  simpa using h.symm

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

omit [Fintype ι] in
/-- The orthogonal projection onto the spans `U x` of a continuous family of finite orthonormal
families `f x` depends continuously on `x`. -/
theorem continuous_starProjection [Finite ι] {X : Type*} [TopologicalSpace X]
    {f : X → ι → E} (hf : Continuous f) (ho : ∀ x, Orthonormal 𝕜 (f x))
    {U : X → Submodule 𝕜 E} [∀ x, (U x).HasOrthogonalProjection]
    (hU : ∀ x, Submodule.span 𝕜 (Set.range (f x)) = U x) :
    Continuous fun x ↦ (U x).starProjection := by
  have := Fintype.ofFinite ι
  have h x : (U x).starProjection = ∑ i, (innerSL 𝕜 (f x i)).smulRight (f x i) := by
    ext w
    simp [(ho x).starProjection_apply_eq_sum (hU x)]
  simp only [h]
  fun_prop

/-- The orthogonal projection onto the span `U` of a finite orthonormal family is its frame
operator, synthesis after analysis. -/
theorem toLinearMap_starProjection_eq_frameOperator (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range v) = U) :
    (U.starProjection : E →ₗ[𝕜] E) = TauCeti.frameOperator 𝕜 v := by
  ext x
  simp [hv.starProjection_apply_eq_sum hU]

omit [Fintype ι] in
/-- **Bessel's identity**: subtracting from `x` its components `⟪vᵢ, x⟫ vᵢ` along finitely many
members of an orthonormal family removes their squared lengths `‖⟪vᵢ, x⟫‖²` from `‖x‖²`. This is
the identity behind Mathlib's Bessel inequality `Orthonormal.sum_inner_products_le`. -/
theorem norm_sub_sum_inner_smul_sq (hv : Orthonormal 𝕜 v) (s : Finset ι) (x : E) :
    ‖x - ∑ i ∈ s, ⟪v i, x⟫_𝕜 • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  have h₂ : (∑ i ∈ s, ∑ j ∈ s, ⟪v i, x⟫_𝕜 * ⟪x, v j⟫_𝕜 * ⟪v j, v i⟫_𝕜) =
      (∑ k ∈ s, ⟪v k, x⟫_𝕜 * ⟪x, v k⟫_𝕜 : 𝕜) :=
    hv.inner_left_right_finset
  have h₃ (z : 𝕜) : RCLike.re (z * (starRingEnd 𝕜) z) = ‖z‖ ^ 2 := by
    simp only [RCLike.mul_conj]
    norm_cast
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

/-- **Parseval's identity** on the span `U` of a finite orthonormal family: the orthogonal
projection of `x` onto `U` has squared norm `∑ᵢ ‖⟪vᵢ, x⟫‖²`. -/
theorem norm_starProjection_sq_eq_sum (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range v) = U) (x : E) :
    ‖U.starProjection x‖ ^ 2 = ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  have h : U.starProjection x = hv.synthesisMapIsometry (TauCeti.analysisMap 𝕜 v x) := by
    simp [hv.starProjection_apply_eq_sum hU, TauCeti.analysisMap_apply]
  rw [h, LinearIsometry.norm_map, TauCeti.norm_analysisMap_sq]

/-- Taking combinations of an orthonormal family with the rows of a matrix `A` produces an
orthonormal family exactly when `A` has orthonormal rows, that is, `A * Aᴴ = 1`. For a square
matrix this says that `A` is unitary. -/
theorem orthonormal_sum_smul_iff {κ : Type*} [DecidableEq κ] (hv : Orthonormal 𝕜 v)
    (A : Matrix κ ι 𝕜) :
    Orthonormal 𝕜 (fun j ↦ ∑ i, A j i • v i) ↔ A * Aᴴ = 1 := by
  classical
  rw [orthonormal_iff_ite, ← Matrix.ext_iff, forall_comm]
  refine forall_congr' fun j ↦ forall_congr' fun k ↦ ?_
  simp only [hv.inner_sum, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, mul_comm, eq_comm (a := k)]

/-- Combining an orthonormal family with the rows of a square matrix `A` produces an orthonormal
family exactly when `A` is unitary. -/
theorem orthonormal_sum_smul_iff_mem_unitaryGroup [DecidableEq ι] (hv : Orthonormal 𝕜 v)
    (A : Matrix ι ι 𝕜) :
    Orthonormal 𝕜 (fun j ↦ ∑ i, A j i • v i) ↔ A ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [hv.orthonormal_sum_smul_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]

end Orthonormal

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι] {v : ι → E}

/-- A unitary change of frame `vⱼ ↦ ∑ i, A j i • vᵢ` preserves and reflects orthonormality. -/
theorem orthonormal_sum_smul_iff_of_mem_unitaryGroup {A : Matrix ι ι 𝕜}
    (hA : A ∈ Matrix.unitaryGroup ι 𝕜) :
    Orthonormal 𝕜 (fun j ↦ ∑ i, A j i • v i) ↔ Orthonormal 𝕜 v := by
  refine ⟨fun hw ↦ ?_, fun hv ↦ (hv.orthonormal_sum_smul_iff_mem_unitaryGroup A).2 hA⟩
  -- The inverse change of frame is the one by `star A`, which is unitary too.
  have := (hw.orthonormal_sum_smul_iff_mem_unitaryGroup (star A)).2 (Unitary.star_mem hA)
  simp_rw [← Matrix.sum_mul_apply_smul, (Matrix.mem_unitaryGroup_iff').1 hA] at this
  simpa [Matrix.one_apply] using this

end TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The synthesis isometry of an orthonormal basis is the inverse of its coordinate map. -/
@[simp]
theorem OrthonormalBasis.synthesisMapIsometry_orthonormal (b : OrthonormalBasis ι 𝕜 E) :
    b.orthonormal.synthesisMapIsometry = b.repr.symm.toLinearIsometry := by
  ext x
  simp [Orthonormal.synthesisMapIsometry_apply, OrthonormalBasis.sum_repr_symm]
