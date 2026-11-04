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
  have hUperpRed : (Uᗮ ∈ Module.End.invtSubmodule A) :=
      LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA hU
  have hxyUperp : X.toLinearMap y ∈ Uᗮ := hxperp
  have hTopRed : (⊤ ∈ Module.End.invtSubmodule ((X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))) :=
    by
    intro z _
    exact Submodule.mem_top
  have hMupper :
      RCLike.re ⟪(X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap) y, y⟫_𝕜 ≤ α * ‖y‖ ^ 2 :=
    (hA.adjoint_conj X.toLinearMap).re_inner_apply_self_le_of_pointSpectrumIn
      hTopRed hgap.1 Submodule.mem_top
  have hAlower :
      (α + δ) * ‖X.toLinearMap y‖ ^ 2 ≤
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 :=
    hA.le_re_inner_apply_self_of_pointSpectrumIn hUperpRed hgap.2 hxyUperp
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

/-- The residual witnesses form an orthonormal family once the tangent has no pole. -/
private theorem orthonormal_tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : Disjoint (LinearMap.range X.toLinearMap) Uᗮ) :
    Orthonormal 𝕜 (tanThetaResidualWitness U X) := by
  classical
  let S := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)
  rw [orthonormal_iff_ite]
  intro i j
  -- On the diagonal, zero sines use Ritz vectors; positive sines require cosine normalization.
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    let σ := S.singularValues i
    let v := LinearMap.rightSingularBasis S i
    have hvv : ⟪v, v⟫_𝕜 = 1 := by
      simp [v]
    by_cases hσ : σ = 0
    · have hw : tanThetaResidualWitness U X i = X.toLinearMap v := by
        simp [tanThetaResidualWitness, S, σ, v, hσ]
      rw [hw]
      calc
        ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = ⟪v, v⟫_𝕜 :=
          X.inner_map_map v v
        _ = 1 := hvv
    · let y := LinearMap.leftSingularVector S i
      have hXadj : X.toLinearMap.adjoint y = ((σ : ℝ) : 𝕜) • v := by
        simpa [S, σ, v, y] using
          Submodule.adjoint_apply_leftSingularVector_starProjection_orthogonal_comp
            U X.toLinearMap (i := i)
      have hyy : ⟪y, y⟫_𝕜 = 1 := by
        simpa [y] using
          (orthonormal_iff_ite.mp (LinearMap.orthonormal_leftSingularVector S)
            ⟨i, hσ⟩ ⟨i, hσ⟩)
      have hXv_y : ⟪X.toLinearMap v, y⟫_𝕜 = ((σ : ℝ) : 𝕜) := by
        calc
          ⟪X.toLinearMap v, y⟫_𝕜 = ⟪v, X.toLinearMap.adjoint y⟫_𝕜 :=
            (LinearMap.adjoint_inner_right X.toLinearMap v y).symm
          _ = ⟪v, ((σ : ℝ) : 𝕜) • v⟫_𝕜 := by rw [hXadj]
          _ = ((σ : ℝ) : 𝕜) := by rw [inner_smul_right, hvv, mul_one]
      have hy_Xv : ⟪y, X.toLinearMap v⟫_𝕜 = ((σ : ℝ) : 𝕜) := by
        calc
          ⟪y, X.toLinearMap v⟫_𝕜 = ⟪X.toLinearMap.adjoint y, v⟫_𝕜 :=
            (LinearMap.adjoint_inner_left X.toLinearMap v y).symm
          _ = ⟪((σ : ℝ) : 𝕜) • v, v⟫_𝕜 := by rw [hXadj]
          _ = ((σ : ℝ) : 𝕜) := by
            rw [inner_smul_left, RCLike.conj_ofReal, hvv, mul_one]
      have hXX : ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = 1 := by
        calc
          ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = ⟪v, v⟫_𝕜 :=
            X.inner_map_map v v
          _ = 1 := hvv
      have hraw :
          ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v,
            y - ((σ : ℝ) : 𝕜) • X.toLinearMap v⟫_𝕜 =
            (((1 - σ ^ 2 : ℝ) : 𝕜)) := by
        simp only [inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, RCLike.conj_ofReal, hyy, hy_Xv, hXv_y, hXX]
        push_cast
        ring
      have hσnonneg : 0 ≤ σ := S.singularValues_nonneg i
      have hσlt : σ < 1 := by
        simpa [S, σ] using
          Submodule.singularValues_starProjection_orthogonal_comp_lt_one_of_disjoint U X htrans i
      let c := Real.sqrt (1 - σ ^ 2)
      have hcpos : 0 < c := by
        dsimp [c]
        exact Real.sqrt_pos.2 (by nlinarith)
      have hcne : c ≠ 0 := ne_of_gt hcpos
      have hw :
          tanThetaResidualWitness U X i =
            ((((c : ℝ) : 𝕜)⁻¹) •
              (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)) := by
        simp [tanThetaResidualWitness, S, σ, v, y, c, hσ]
      have hc_sq : c ^ 2 = 1 - σ ^ 2 := by
        dsimp [c]
        exact Real.sq_sqrt (by nlinarith)
      have hnormalize : c⁻¹ * (c⁻¹ * (1 - σ ^ 2)) = 1 := by
        field_simp [hcne]
        nlinarith
      rw [hw]
      simp only [inner_smul_left, inner_smul_right, map_inv₀,
        RCLike.conj_ofReal, hraw]
      exact_mod_cast hnormalize
  -- Off the diagonal, right singular vectors are orthogonal. The adjoint relation
  -- kills mixed Ritz/left-singular pairings, including both zero-sine branches.
  · rw [ite_eq_right hij]
    let σi := S.singularValues i
    let σj := S.singularValues j
    let vi := LinearMap.rightSingularBasis S i
    let vj := LinearMap.rightSingularBasis S j
    have hvv : ⟪vi, vj⟫_𝕜 = 0 := by
      simp [vi, vj, hij,
        orthonormal_iff_ite.mp (LinearMap.rightSingularBasis S).orthonormal i j]
    have hXX : ⟪X.toLinearMap vi, X.toLinearMap vj⟫_𝕜 = 0 := by
      calc
        ⟪X.toLinearMap vi, X.toLinearMap vj⟫_𝕜 = ⟪vi, vj⟫_𝕜 :=
          X.inner_map_map vi vj
        _ = 0 := hvv
    by_cases hi : σi = 0
    · have hwi : tanThetaResidualWitness U X i = X.toLinearMap vi := by
        simp [tanThetaResidualWitness, S, σi, vi, hi]
      by_cases hj : σj = 0
      · have hwj : tanThetaResidualWitness U X j = X.toLinearMap vj := by
          simp [tanThetaResidualWitness, S, σj, vj, hj]
        rw [hwi, hwj, hXX]
      · let yj := LinearMap.leftSingularVector S j
        have hXadjj : X.toLinearMap.adjoint yj = ((σj : ℝ) : 𝕜) • vj := by
          simpa [S, σj, vj, yj] using
            Submodule.adjoint_apply_leftSingularVector_starProjection_orthogonal_comp
            U X.toLinearMap (i := j)
        have hXvi_yj :
            ⟪X.toLinearMap vi, yj⟫_𝕜 = ((σj : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          by rw [← LinearMap.adjoint_inner_right, hXadjj, inner_smul_right]
        have hraw :
            ⟪X.toLinearMap vi,
              yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj⟫_𝕜 = 0 := by
          rw [inner_sub_right, inner_smul_right, hXvi_yj, hXX, hvv]
          simp
        let cj := Real.sqrt (1 - σj ^ 2)
        have hwj :
            tanThetaResidualWitness U X j =
              ((((cj : ℝ) : 𝕜)⁻¹) •
                (yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj)) := by
          simp [tanThetaResidualWitness, S, σj, vj, yj, cj, hj]
        rw [hwi, hwj, inner_smul_right, hraw, mul_zero]
    · let yi := LinearMap.leftSingularVector S i
      have hXadji : X.toLinearMap.adjoint yi = ((σi : ℝ) : 𝕜) • vi := by
        simpa [S, σi, vi, yi] using
          Submodule.adjoint_apply_leftSingularVector_starProjection_orthogonal_comp
            U X.toLinearMap (i := i)
      by_cases hj : σj = 0
      · have hyi_Xvj :
            ⟪yi, X.toLinearMap vj⟫_𝕜 = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 := by
          calc
            ⟪yi, X.toLinearMap vj⟫_𝕜 =
                ⟪X.toLinearMap.adjoint yi, vj⟫_𝕜 :=
              (LinearMap.adjoint_inner_left X.toLinearMap vj yi).symm
            _ = ⟪((σi : ℝ) : 𝕜) • vi, vj⟫_𝕜 := by rw [hXadji]
            _ = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 := by
              rw [inner_smul_left, RCLike.conj_ofReal]
        have hraw :
            ⟪yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi,
              X.toLinearMap vj⟫_𝕜 = 0 := by
          rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
            hyi_Xvj, hXX, hvv]
          simp
        let ci := Real.sqrt (1 - σi ^ 2)
        have hwi :
            tanThetaResidualWitness U X i =
              ((((ci : ℝ) : 𝕜)⁻¹) •
                (yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi)) := by
          simp [tanThetaResidualWitness, S, σi, vi, yi, ci, hi]
        have hwj : tanThetaResidualWitness U X j = X.toLinearMap vj := by
          simp [tanThetaResidualWitness, S, σj, vj, hj]
        rw [hwi, hwj, inner_smul_left, hraw, mul_zero]
      · let yj := LinearMap.leftSingularVector S j
        have hXadjj : X.toLinearMap.adjoint yj = ((σj : ℝ) : 𝕜) • vj := by
          simpa [S, σj, vj, yj] using
            Submodule.adjoint_apply_leftSingularVector_starProjection_orthogonal_comp
            U X.toLinearMap (i := j)
        have hyy : ⟪yi, yj⟫_𝕜 = 0 := by
          simpa [yi, yj, hij] using
            (orthonormal_iff_ite.mp (LinearMap.orthonormal_leftSingularVector S)
              ⟨i, hi⟩ ⟨j, hj⟩)
        have hyi_Xvj :
            ⟪yi, X.toLinearMap vj⟫_𝕜 = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          by rw [← LinearMap.adjoint_inner_left, hXadji, inner_smul_left, RCLike.conj_ofReal]
        have hXvi_yj :
            ⟪X.toLinearMap vi, yj⟫_𝕜 = ((σj : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          by rw [← LinearMap.adjoint_inner_right, hXadjj, inner_smul_right]
        have hraw :
            ⟪yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi,
              yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj⟫_𝕜 = 0 := by
          simp only [inner_sub_left, inner_sub_right, inner_smul_left,
            inner_smul_right, RCLike.conj_ofReal,
            hyy, hyi_Xvj, hXvi_yj, hXX, hvv]
          ring
        let ci := Real.sqrt (1 - σi ^ 2)
        let cj := Real.sqrt (1 - σj ^ 2)
        have hwi :
            tanThetaResidualWitness U X i =
              ((((ci : ℝ) : 𝕜)⁻¹) •
                (yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi)) := by
          simp [tanThetaResidualWitness, S, σi, vi, yi, ci, hi]
        have hwj :
            tanThetaResidualWitness U X j =
              ((((cj : ℝ) : 𝕜)⁻¹) •
                (yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj)) := by
          simp [tanThetaResidualWitness, S, σj, vj, yj, cj, hj]
        simp only [hwi, hwj, inner_smul_left, inner_smul_right,
          hraw, mul_zero, mul_zero]

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
  let S := (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap)
  let M := (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)
  let R := (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap))
  let σ := S.singularValues i
  let v := LinearMap.rightSingularBasis S i
  have hvnorm : ‖v‖ = 1 := (LinearMap.rightSingularBasis S).orthonormal.norm_eq_one i
  have hσnonneg : 0 ≤ σ := S.singularValues_nonneg i
  have htrans := isTransverse_of_tanThetaSpectralGap hA hU X hδ hgap
  have hσlt : σ < 1 :=
    Submodule.singularValues_starProjection_orthogonal_comp_lt_one_of_disjoint U X htrans i
  have hcpos : 0 < Real.sqrt (1 - σ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  -- Convert the accepted principal-tangent formula to the sine/cosine quotient.
  have htan_i : tanTheta0.singularValues i = σ / Real.sqrt (1 - σ ^ 2) := by
    calc
      tanTheta0.singularValues i = (LinearMap.range X.toLinearMap).principalTangents U i :=
        congrArg (fun z : ℕ →₀ ℝ => z (i : ℕ)) htan
      _ = σ / Real.sqrt (1 - σ ^ 2) := by
        rw [Submodule.principalTangents_apply_eq_div]
        have heq := U.principalSines_range_eq_singularValues
          (X := X.toContinuousLinearMap) X.isometry
        have heq' : (LinearMap.range X.toLinearMap).principalSines U = S.singularValues := by
          simpa only [ContinuousLinearMap.toLinearMap_comp,
            LinearIsometry.toLinearMap_toContinuousLinearMap] using heq
        rw [heq']
  by_cases hσzero : σ = 0
  · have hgal := LinearMap.congr_fun (LinearMap.adjoint_comp_ritzResidual_eq_zero A X) v
    -- Express Galerkin orthogonality with the local residual map R.
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have horth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hwitness : tanThetaResidualWitness U X i = X.toLinearMap v := by
      simp [tanThetaResidualWitness, S, σ, v, hσzero]
    rw [htan_i, hσzero, zero_div, mul_zero, hwitness]
    -- At a zero sine, the chosen witness is the corresponding Ritz vector.
    change 0 ≤ RCLike.re ⟪X.toLinearMap v, R v⟫_𝕜
    rw [horth]
    simp
  · let y := LinearMap.leftSingularVector S i
    have hynorm : ‖y‖ = 1 := by
      simpa [y] using (LinearMap.orthonormal_leftSingularVector S).norm_eq_one ⟨i, hσzero⟩
    have hSv : S v = ((σ : ℝ) : 𝕜) • y := by
      simpa [S, σ, v, y] using LinearMap.apply_rightSingularBasis S i
    have hSadj : S.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa only [S, σ, v, y] using LinearMap.adjoint_leftSingularVector S i
    have hyUperp : y ∈ Uᗮ := by
      dsimp [y]
      rw [LinearMap.leftSingularVector_def]
      exact Uᗮ.smul_mem _ (Uᗮ.starProjection_apply_mem (X v))
    have hXadj : X.toLinearMap.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa [S, σ, v, y] using
        Submodule.adjoint_apply_leftSingularVector_starProjection_orthogonal_comp
            U X.toLinearMap (i := i)
    have hMupper : RCLike.re ⟪M v, v⟫_𝕜 ≤ α := by
      have hTopRed : (⊤ ∈ Module.End.invtSubmodule M) := fun z _ => Submodule.mem_top
      have hbound : RCLike.re ⟪M v, v⟫_𝕜 ≤ α * ‖v‖ ^ 2 :=
        (hA.adjoint_conj X.toLinearMap).re_inner_apply_self_le_of_pointSpectrumIn
          hTopRed hgap.1 Submodule.mem_top
      simpa [hvnorm] using hbound
    have hAlower : α + δ ≤ RCLike.re ⟪A y, y⟫_𝕜 := by
      have hUperpRed : (Uᗮ ∈ Module.End.invtSubmodule A) :=
          LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA hU
      have hbound : (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
        hA.le_re_inner_apply_self_of_pointSpectrumIn hUperpRed hgap.2 hyUperp
      simpa [hynorm] using hbound
    have hSyl := LinearMap.congr_fun
      (hA.sylvester_starProjection_orthogonal_comp hU X.toLinearMap M) v
    -- Pair the projected Sylvester identity with the sine left singular vector;
    -- the ordered form bounds supply the gap times its singular value.
    have hpair :
        RCLike.re ⟪y, R v⟫_𝕜 =
          σ * (RCLike.re ⟪A y, y⟫_𝕜 - RCLike.re ⟪M v, v⟫_𝕜) := by
      have hright :
          ⟪y, Uᗮ.starProjection.toLinearMap (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜 := by
        -- Expand composition so the projection can move across the inner product.
        change ⟪y, Uᗮ.starProjection (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜
        rw [← Uᗮ.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hyUperp]
      have hsyl' : A (S v) - S (M v) = Uᗮ.starProjection.toLinearMap (R v) := by
        simpa [S, M, R] using hSyl
      have hSM : ⟪y, S (M v)⟫_𝕜 = ⟪S.adjoint y, M v⟫_𝕜 := by
        exact (LinearMap.adjoint_inner_left S (M v) y).symm
      have hpairComplex :
          ⟪y, R v⟫_𝕜 =
            (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by
        calc
          ⟪y, R v⟫_𝕜 = ⟪y, Uᗮ.starProjection.toLinearMap (R v)⟫_𝕜 := hright.symm
          _ = ⟪y, A (S v) - S (M v)⟫_𝕜 := by rw [hsyl']
          _ = ⟪y, A (S v)⟫_𝕜 - ⟪y, S (M v)⟫_𝕜 := inner_sub_right _ _ _
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) - ⟪y, S (M v)⟫_𝕜 := by
            rw [hSv, map_smul, inner_smul_right]
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) -
              (((σ : ℝ) : 𝕜) * ⟪v, M v⟫_𝕜) := by
            rw [hSM, hSadj, inner_smul_left, RCLike.conj_ofReal]
          _ = (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by ring
      have hAy : RCLike.re ⟪y, A y⟫_𝕜 = RCLike.re ⟪A y, y⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      have hMv : RCLike.re ⟪v, M v⟫_𝕜 = RCLike.re ⟪M v, v⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      rw [hpairComplex, RCLike.re_ofReal_mul, map_sub, hAy, hMv]
    have hpair_lower : δ * σ ≤ RCLike.re ⟪y, R v⟫_𝕜 := by
      rw [hpair]
      nlinarith
    -- Galerkin orthogonality removes the Ritz component of the normalized witness.
    have hgal := LinearMap.congr_fun (LinearMap.adjoint_comp_ritzResidual_eq_zero A X) v
    -- Express Galerkin orthogonality with the local residual map R.
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have hXorth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hrawComplex :
        ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          ⟪y, R v⟫_𝕜 := by
      rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, hXorth,
        mul_zero, sub_zero]
    have hraw :
        RCLike.re ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 := congrArg RCLike.re hrawComplex
    let c := Real.sqrt (1 - σ ^ 2)
    have hcpos' : 0 < c := by simpa [c] using hcpos
    have hscale :
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 / c := by
      calc
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
            c⁻¹ * RCLike.re
              ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 := by
                rw [inner_smul_left, map_inv₀, RCLike.conj_ofReal,
                  ← RCLike.ofReal_inv, RCLike.re_ofReal_mul]
        _ = c⁻¹ * RCLike.re ⟪y, R v⟫_𝕜 := by rw [hraw]
        _ = RCLike.re ⟪y, R v⟫_𝕜 / c := by
          simp [div_eq_mul_inv, mul_comm]
    rw [htan_i]
    -- Unfold the witness using the local complementary cosine c.
    change δ * (σ / c) ≤
      RCLike.re ⟪
        (if σ = 0 then X.toLinearMap v else
          ((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v))),
        R v⟫_𝕜
    rw [ite_eq_right hσzero, hscale]
    simpa [div_eq_mul_inv, mul_assoc] using
      (div_le_div_iff_of_pos_right hcpos').2 hpair_lower

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
