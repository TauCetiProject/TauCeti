/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.TanTheta
public import TauCeti.Analysis.InnerProductSpace.RayleighRitz
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Ritz-residual tangent bounds

An upper spectral bound on a Ritz compression, separated from the unwanted
exact spectrum, controls the principal tangents by the Ritz residual in every
rectangular unitarily invariant seminorm. The gap itself excludes right-angle
poles; equal dimensions of the trial and exact subspaces are not required.

Adapted from `DavisKahan/FiniteDimensional/TanTheta/RitzResidual.lean` in the
[Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Jon Crall and GPT 5.6 High; copyright 2026 Kitware, Inc.; Apache-2.0).
The proof follows Davis and Kahan (1970), equation (6.6): normalized residual
witnesses for the sine singular vectors give Ky Fan prefix domination, then
Fan dominance gives every unitarily invariant seminorm.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

noncomputable section

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The trial-space spectral bound on the Ritz compression, in quadratic-form shape. -/
private theorem re_inner_ritz_le_of_pointSpectrumIn
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (X : F →ₗᵢ[𝕜] E) {α : ℝ}
    (h : Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α)) (y : F) :
    RCLike.re ⟪(X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) y, y⟫_𝕜 ≤ α * ‖y‖ ^ 2 :=
  (hA.adjoint_conj X.toLinearMap).re_inner_apply_self_le_of_pointSpectrumIn
    (fun _ _ => Submodule.mem_top) h Submodule.mem_top

/-- The separated spectral bound on `Uᗮ`, in quadratic-form shape. -/
private theorem le_re_inner_of_pointSpectrumIn_orthogonal
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : U ∈ Module.End.invtSubmodule A) {β : ℝ}
    (h : Module.End.PointSpectrumIn A Uᗮ (Set.Ici β)) {y : E} (hy : y ∈ Uᗮ) :
    β * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
  hA.le_re_inner_apply_self_of_pointSpectrumIn
    (LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA hU) h hy

/-- Separated one-sided spectral bounds force the trial and exact subspaces to be
transverse.  Thus the tangent has no `π/2` pole; this is a conclusion, not an
extra hypothesis. -/
private theorem isTransverse_of_tanThetaSpectralGap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {α δ : ℝ} (hδ : 0 < δ)
    (hgap : (Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α) ∧
      Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ)))) :
    Disjoint (LinearMap.range X.toLinearMap) Uᗮ := by
  rw [Submodule.disjoint_def]
  intro x hx hxperp
  rcases hx with ⟨y, rfl⟩
  have hxyUperp : X.toLinearMap y ∈ Uᗮ := hxperp
  have hMupper := re_inner_ritz_le_of_pointSpectrumIn hA X hgap.1 y
  have hAlower := le_re_inner_of_pointSpectrumIn_orthogonal hA hU hgap.2 hxyUperp
  have hinner :
      RCLike.re ⟪(X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) y, y⟫_𝕜 =
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 := by
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left]
  have hnorm : ‖X.toLinearMap y‖ = ‖y‖ := X.norm_map y
  have hyzero : y = 0 := by
    by_contra hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [← hinner, hnorm] at hAlower
    nlinarith [sq_pos_of_pos hynorm]
  simp [hyzero]

/-- The normalized residual-side witness attached to a sine singular vector.

At a zero singular value the tangent contribution is zero, so the corresponding Ritz-space
basis vector is used.  At a positive singular value, the left singular vector is projected
away from the Ritz space and normalized by the complementary cosine. -/
private noncomputable def tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (i : Fin (finrank 𝕜 F)) : E :=
  let S := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)
  let σ := S.singularValues i
  let v := LinearMap.rightSingularBasis S i
  if σ = 0 then X v else
    (((Real.sqrt (1 - σ ^ 2) : ℝ) : 𝕜)⁻¹) •
      (LinearMap.leftSingularVector S i - ((σ : ℝ) : 𝕜) • X v)


/-- At a zero sine the witness is the Ritz vector. -/
private theorem tanThetaResidualWitness_of_singularValues_eq_zero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    {i : Fin (finrank 𝕜 F)}
    (h : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i = 0) :
    tanThetaResidualWitness U X i = X.toLinearMap
      (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i) := by
  simp [tanThetaResidualWitness, h]

/-- At a nonzero sine the witness is the normalized residual direction. -/
private theorem tanThetaResidualWitness_of_singularValues_ne_zero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    {i : Fin (finrank 𝕜 F)}
    (h : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i ≠ 0) :
    tanThetaResidualWitness U X i =
      (((Real.sqrt (1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2) :
        ℝ) : 𝕜)⁻¹) •
        (LinearMap.leftSingularVector (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i -
          (((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i : ℝ) : 𝕜) •
            X.toLinearMap (LinearMap.rightSingularBasis
              (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)) := by
  simp [tanThetaResidualWitness, h]

/-- The residual witnesses form an orthonormal family once the tangent has no pole. -/
private theorem orthonormal_tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : Disjoint (LinearMap.range X.toLinearMap) Uᗮ) :
    Orthonormal 𝕜 (tanThetaResidualWitness U X) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i = 0 <;>
    by_cases hj : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues j = 0
  · rw [tanThetaResidualWitness_of_singularValues_eq_zero U X hi,
      tanThetaResidualWitness_of_singularValues_eq_zero U X hj]
    exact (X.inner_map_map _ _).trans
      ((LinearMap.rightSingularBasis
        (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)).inner_eq_ite i j)
  · rw [ite_eq_right (by rintro rfl; exact hj hi),
      tanThetaResidualWitness_of_singularValues_eq_zero U X hi,
      tanThetaResidualWitness_of_singularValues_ne_zero U X hj, inner_smul_right,
      Submodule.inner_map_sub_leftSingularVector_eq_zero, mul_zero]
  · rw [ite_eq_right (by rintro rfl; exact hi hj),
      tanThetaResidualWitness_of_singularValues_eq_zero U X hj,
      tanThetaResidualWitness_of_singularValues_ne_zero U X hi, inner_smul_left,
      ← inner_conj_symm, Submodule.inner_map_sub_leftSingularVector_eq_zero, map_zero, mul_zero]
  · rw [tanThetaResidualWitness_of_singularValues_ne_zero U X hi,
      tanThetaResidualWitness_of_singularValues_ne_zero U X hj, inner_smul_left, inner_smul_right,
      Submodule.inner_sub_leftSingularVector_eq_ite U X hi hj]
    by_cases hij : i = j
    · subst hij
      have hσlt := Submodule.singularValues_starProjection_orthogonal_comp_lt_one_of_disjoint
        U X htrans i
      have hσnonneg := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues_nonneg i
      have hpos : 0 < 1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2 :=
        by nlinarith
      have hnormalize : ∀ t : ℝ, 0 < t → (Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) = 1 :=
        fun t ht => by
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt ht.le, inv_mul_cancel₀ ht.ne']
      simp only [ite_true, map_inv₀, RCLike.conj_ofReal]
      exact_mod_cast hnormalize _ hpos
    · simp [hij]

/-- A tangent of the trial subspace against `U` is the sine over the cosine, with the sines
read off the singular values of the projection onto `Uᗮ`. -/
private theorem singularValues_eq_div_sqrt_of_singularValues_eq_principalTangents
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues = (LinearMap.range X.toLinearMap).principalTangents U)
    (i : Fin (finrank 𝕜 F)) :
    tanTheta0.singularValues i =
      (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i /
        Real.sqrt
          (1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2) := by
  calc
    tanTheta0.singularValues i = (LinearMap.range X.toLinearMap).principalTangents U i :=
      congrArg (fun z : ℕ →₀ ℝ => z (i : ℕ)) htan
    _ = _ := by
      rw [Submodule.principalTangents_apply_eq_div]
      have heq := U.principalSines_range_eq_singularValues
        (X := X.toContinuousLinearMap) X.isometry
      have heq' : (LinearMap.range X.toLinearMap).principalSines U =
          (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues := by
        simpa only [ContinuousLinearMap.toLinearMap_comp,
          LinearIsometry.toLinearMap_toContinuousLinearMap] using heq
      rw [heq']

/-- The pairing of a sine left singular vector with the Ritz residual of the matching right
singular vector is the sine times the gap between the two Rayleigh quotients. -/
private theorem re_inner_leftSingularVector_ritzResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) (i : Fin (finrank 𝕜 F)) :
    RCLike.re ⟪LinearMap.leftSingularVector (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i,
        (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
          (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)⟫_𝕜 =
      (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i *
        (RCLike.re ⟪A (LinearMap.leftSingularVector
            (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i),
          LinearMap.leftSingularVector (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i⟫_𝕜 -
          RCLike.re ⟪(X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)
            (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i),
            LinearMap.rightSingularBasis
              (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i⟫_𝕜) := by
  let S := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)
  let M := (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)
  let R := (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
  let σ := S.singularValues i
  let v := LinearMap.rightSingularBasis S i
  let y := LinearMap.leftSingularVector S i
  have hSv : S v = ((σ : ℝ) : 𝕜) • y := by
    simpa [S, σ, v, y] using LinearMap.apply_rightSingularBasis S i
  have hSadj : S.adjoint y = ((σ : ℝ) : 𝕜) • v := by
    simpa only [S, σ, v, y] using LinearMap.adjoint_leftSingularVector S i
  have hyUperp : y ∈ Uᗮ := by
    dsimp [y]
    rw [LinearMap.leftSingularVector_def]
    exact Uᗮ.smul_mem _ (Uᗮ.starProjection_apply_mem (X v))
  have hSyl := LinearMap.congr_fun
    (hA.sylvester_starProjection_orthogonal_comp hU X.toLinearMap M) v
  have hright :
      ⟪y, Uᗮ.starProjection.toLinearMap (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜 := by
    -- Expand composition so the projection can move across the inner product.
    change ⟪y, Uᗮ.starProjection (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜
    rw [← Uᗮ.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hyUperp]
  have hsyl' : A (S v) - S (M v) = Uᗮ.starProjection.toLinearMap (R v) := by
    simpa [S, M, R] using hSyl
  have hSM : ⟪y, S (M v)⟫_𝕜 = ⟪S.adjoint y, M v⟫_𝕜 :=
    (LinearMap.adjoint_inner_left S (M v) y).symm
  have hpairComplex :
      ⟪y, R v⟫_𝕜 = (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by
    calc
      ⟪y, R v⟫_𝕜 = ⟪y, A (S v) - S (M v)⟫_𝕜 := by rw [hsyl', hright]
      _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) - (((σ : ℝ) : 𝕜) * ⟪v, M v⟫_𝕜) := by
        rw [inner_sub_right, hSv, map_smul, inner_smul_right, hSM, hSadj, inner_smul_left,
          RCLike.conj_ofReal]
      _ = _ := by ring
  have hAy : RCLike.re ⟪y, A y⟫_𝕜 = RCLike.re ⟪A y, y⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  have hMv : RCLike.re ⟪v, M v⟫_𝕜 = RCLike.re ⟪M v, v⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  rw [hpairComplex, RCLike.re_ofReal_mul, map_sub, hAy, hMv]

/-- At a nonzero sine, the pairing of the residual witness with the Ritz residual of the matching
right singular vector is that of the sine left singular vector, divided by the cosine. -/
private theorem re_inner_tanThetaResidualWitness_ritzResidual
    (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    {i : Fin (finrank 𝕜 F)}
    (h : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i ≠ 0) :
    RCLike.re ⟪tanThetaResidualWitness U X i,
        (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
          (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)⟫_𝕜 =
      (Real.sqrt
          (1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2))⁻¹ *
        RCLike.re ⟪LinearMap.leftSingularVector
            (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i,
          (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
            (LinearMap.rightSingularBasis
              (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)⟫_𝕜 := by
  rw [tanThetaResidualWitness_of_singularValues_ne_zero U X h]
  simp only [inner_smul_left, inner_sub_left, LinearMap.inner_map_ritzResidual_eq_zero, mul_zero,
    sub_zero, map_inv₀, RCLike.conj_ofReal]
  rw [← RCLike.ofReal_inv, RCLike.re_ofReal_mul]

/-- The scalar spectral-gap estimate for one principal tangent.

This is the analytic core of equation (6.6), expressed without direct-rotation coordinates.
The left singular vector of the sine block is projected away from the Ritz space; Galerkin
orthogonality removes that projection from the residual pairing, while its norm supplies the
cosine denominator. -/
private theorem tanThetaResidualWitness_scalar
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {α δ : ℝ} (hδ : 0 < δ)
    (hgap : (Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α) ∧
      Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      (LinearMap.range X.toLinearMap).principalTangents U)
    (i : Fin (finrank 𝕜 F)) :
    δ * tanTheta0.singularValues i ≤
      RCLike.re ⟪tanThetaResidualWitness U X i,
        (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
          (LinearMap.rightSingularBasis ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)) i)⟫_𝕜
          := by
  have htrans := isTransverse_of_tanThetaSpectralGap hA hU X hδ hgap
  have hσlt := Submodule.singularValues_starProjection_orthogonal_comp_lt_one_of_disjoint
    U X htrans i
  have hσnonneg := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues_nonneg i
  have hgal := LinearMap.inner_map_ritzResidual_eq_zero A X
    (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)
  rw [singularValues_eq_div_sqrt_of_singularValues_eq_principalTangents U X tanTheta0 htan i]
  by_cases hσzero : (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i = 0
  · rw [tanThetaResidualWitness_of_singularValues_eq_zero U X hσzero, hσzero, zero_div, mul_zero,
      hgal, map_zero]
  · have hcpos : 0 < Real.sqrt
        (1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2) :=
      Real.sqrt_pos.2 (by nlinarith)
    have hy : LinearMap.leftSingularVector
        (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i ∈ Uᗮ := by
      rw [LinearMap.leftSingularVector_def]
      exact Uᗮ.smul_mem _ (Uᗮ.starProjection_apply_mem _)
    have hynorm : ‖LinearMap.leftSingularVector
        (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i‖ = 1 :=
      (LinearMap.orthonormal_leftSingularVector _).norm_eq_one ⟨i, hσzero⟩
    have hvnorm : ‖LinearMap.rightSingularBasis
        (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i‖ = 1 :=
      (LinearMap.rightSingularBasis _).orthonormal.norm_eq_one i
    have hMupper := re_inner_ritz_le_of_pointSpectrumIn hA X hgap.1
      (LinearMap.rightSingularBasis (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) i)
    have hAlower := le_re_inner_of_pointSpectrumIn_orthogonal hA hU hgap.2 hy
    rw [hvnorm] at hMupper
    rw [hynorm] at hAlower
    have hpair := re_inner_leftSingularVector_ritzResidual hA hU X i
    rw [re_inner_tanThetaResidualWitness_ritzResidual A U X hσzero]
    calc
      _ = (Real.sqrt
            (1 - ((Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) ^ 2))⁻¹ *
          (δ * (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap).singularValues i) := by
        rw [div_eq_inv_mul]; ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcpos.le)
        rw [hpair]
        nlinarith

/-- Ky Fan domination up to the full trial-space dimension. -/
private theorem kyFan_tanTheta0_ritzResidual_le_of_le_finrank
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {α δ : ℝ} (hδ : 0 < δ)
    (hgap : (Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α) ∧
      Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      (LinearMap.range X.toLinearMap).principalTangents U)
    {k : ℕ} (hk : k ≤ finrank 𝕜 F) :
    δ * tanTheta0.kyFanSum k ≤
      ((A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ
        X.toLinearMap))).kyFanSum k := by
  let S := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)
  let castIndex : Fin k → Fin (finrank 𝕜 F) := fun i => Fin.castLE hk i
  have htrans := isTransverse_of_tanThetaSpectralGap hA hU X hδ hgap
  have huFull := orthonormal_tanThetaResidualWitness U X htrans
  have hu : Orthonormal 𝕜
      (fun i : Fin k => tanThetaResidualWitness U X (castIndex i)) :=
    huFull.comp castIndex (Fin.castLE_injective hk)
  have hv : Orthonormal 𝕜
      (fun i : Fin k => LinearMap.rightSingularBasis S (castIndex i)) :=
    (LinearMap.rightSingularBasis S).orthonormal.comp castIndex (Fin.castLE_injective hk)
  have hnorm := ((A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ
    X.toLinearMap))).norm_sum_inner_le_kyFanSum hu hv
  simp only [Fintype.card_fin] at hnorm
  have hreal := (RCLike.re_le_norm _).trans hnorm
  rw [map_sum] at hreal
  have hsum := (Finset.sum_le_sum fun i _ =>
    tanThetaResidualWitness_scalar hA hU X hδ hgap tanTheta0 htan (castIndex i)).trans hreal
  rw [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  exact hsum

/-- **The source Ky Fan root for the finite `tan Θ` theorem.**

For every prefix length, `δ` times the sum of the first principal tangents is bounded by
the corresponding singular-value prefix of the Ritz residual.  The proof is
the finite version of Davis--Kahan equation (6.6): choose singular vectors of
the directed sine block, construct the complementary cosine vectors, derive
the scalar gap inequalities, sum, and invoke the rectangular Ky Fan
variational principle.

The operator `tanTheta0` is intentionally arbitrary, as in the paper; only its
singular values are prescribed.  This private theorem is the single hard
geometric/majorization seam. -/
private theorem kyFan_tanTheta0_ritzResidual_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {α δ : ℝ} (hδ : 0 < δ)
    (hgap : (Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α) ∧
      Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      (LinearMap.range X.toLinearMap).principalTangents U) (k : ℕ) :
    δ * tanTheta0.kyFanSum k ≤
      ((A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ
        X.toLinearMap))).kyFanSum k := by
  by_cases hk : k ≤ finrank 𝕜 F
  · exact kyFan_tanTheta0_ritzResidual_le_of_le_finrank hA hU X hδ hgap
      tanTheta0 htan hk
  · have hk' : finrank 𝕜 F ≤ k := Nat.le_of_not_ge hk
    let R := A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)
    -- Both singular-value sums stabilize once the prefix reaches the source dimension.
    change δ * tanTheta0.kyFanSum k ≤ R.kyFanSum k
    rw [(tanTheta0.kyFanSum_eq_nuclear ((LinearMap.finrank_range_le tanTheta0).trans hk')).trans
        (tanTheta0.kyFanSum_eq_nuclear (LinearMap.finrank_range_le tanTheta0)).symm,
      (R.kyFanSum_eq_nuclear ((LinearMap.finrank_range_le R).trans hk')).trans
        (R.kyFanSum_eq_nuclear (LinearMap.finrank_range_le R)).symm]
    exact kyFan_tanTheta0_ritzResidual_le_of_le_finrank hA hU X hδ hgap
      tanTheta0 htan le_rfl

/-- **Paper-exact Davis--Kahan `tan Θ`, residual form, every UI norm.**

This is the first conclusion in the 1970 theorem:

`δ * N (tan Θ₀) ≤ N R`.

As in the paper, `tanTheta0` may be any rectangular operator whose singular
values are the principal tangents.  The spectral assumptions themselves force
transversality. -/
private theorem mul_map_le_map_ritzResidual_of_singularValues_eq_principalTangents
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {α δ : ℝ} (hδ : 0 < δ)
    (hgap : Module.End.PointSpectrumIn
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) ⊤ (Set.Iic α) ∧
      Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ)))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      (LinearMap.range X.toLinearMap).principalTangents U) :
    δ * N tanTheta0 ≤ N (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)) := by
  have hprefix : ∀ k,
      (((δ : ℝ) : 𝕜) • tanTheta0).kyFanSum k ≤
        (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)).kyFanSum k := by
    intro k
    rw [LinearMap.kyFanSum_smul, RCLike.norm_of_nonneg hδ.le]
    exact kyFan_tanTheta0_ritzResidual_le hA hU X hδ hgap
      tanTheta0 htan k
  have hN := N.map_le_of_kyFanSum_le (hprefix)
  rw [map_smul_eq_mul N] at hN
  simpa [RCLike.norm_ofReal, abs_of_pos hδ] using hN

/-- A one-sided spectral gap between the Ritz compression on `Z` and the exact
operator on `Uᗮ` excludes right-angle poles, with no equality of ranks required. -/
theorem _root_.Submodule.directedProjectionGap_lt_one_of_pointSpectrumIn_compression
    (Z U : Submodule 𝕜 E) [U.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hM : Module.End.PointSpectrumIn (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype) ⊤ (Set.Iic α))
    (hperp : Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))) :
    Z.directedProjectionGap U < 1 := by
  apply (Z.directedProjectionGap_lt_one_iff U).mpr
  have h := isTransverse_of_tanThetaSpectralGap hA hU Z.subtypeₗᵢ hδ ⟨hM, hperp⟩
  simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using h

/-- **Ritz-residual tangent bound in every unitarily invariant seminorm.**
If the Ritz compression of a symmetric `A` to `Z` has spectrum at most `α` and
`A` on the invariant complement `Uᗮ` has spectrum above `α + δ`, then the native
directed tangent representative satisfies `δ N(tan Θ) ≤ N(R)`, where
`R = A ι_Z - ι_Z (ι_Z† A ι_Z)`. The gap itself forces all tangents to be finite.
No equality of dimensions between `Z` and `U` is assumed. -/
theorem mul_map_tanThetaMap_le_map_ritzResidual
    {Z U : Submodule 𝕜 E} [U.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (N : UnitarilyInvariantSeminorm 𝕜 Z E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hM : Module.End.PointSpectrumIn (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype) ⊤ (Set.Iic α))
    (hperp : Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))) :
    δ * N (Z.tanThetaMap U) ≤
      N (A ∘ₗ Z.subtype - Z.subtype ∘ₗ (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype)) := by
  have hgap := Z.directedProjectionGap_lt_one_of_pointSpectrumIn_compression U hA hU hδ hM hperp
  apply mul_map_le_map_ritzResidual_of_singularValues_eq_principalTangents
    N hA hU Z.subtypeₗᵢ hδ ⟨hM, hperp⟩ (Z.tanThetaMap U)
  simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using
    Z.singularValues_tanThetaMap U hgap

end

end TauCeti.UnitarilyInvariantSeminorm
