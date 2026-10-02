/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# The Poincaré Riemannian metric

The canonical tensor on the upper half-plane is the Euclidean inner product divided by the
square of the imaginary coordinate. We construct it as a smooth real Riemannian metric, so that
it can be used by the Riemannian volume construction.

The convention is the upper half-plane model in J. M. Lee, *Introduction to Riemannian
Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
-/

public section

open Bundle FiberBundle Set Topology
open scoped Manifold ContDiff UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-- The singleton complex chart also gives the upper half-plane its smooth real manifold
structure. -/
instance instIsManifoldReal : IsManifold 𝓘(ℝ, ℂ) ω ℍ :=
  _root_.UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

private theorem poincare_symmL (α z : ℍ) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α).symmL ℝ z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).symm v := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by simp)]
  -- The singleton atlas makes this change of coordinates a self transition.
  exact tangentCoordChange_self (x := z) (I := 𝓘(ℝ, ℂ)) (by simp)

private theorem poincare_symm (α z : ℍ) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α).symm z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).symm v := by
  simpa only [Trivialization.symmL_apply (R := ℝ)
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α) (by simp)] using
    poincare_symmL α z v

/-- The smooth Poincaré metric, whose tensor is the Euclidean tensor divided by `im²`. -/
def poincareRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) where
  inner z := by
    -- Defining a foundational tangent metric uses the explicit identification with its model.
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    exact (z.im ^ 2)⁻¹ •
      ((e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
        (innerSL ℝ (E := ℂ)))
  symm z v w := by
    simp only [smul_apply, smul_eq_mul, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply]
    congr 1
    exact real_inner_comm (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) |>.symm
  pos z v hv := by
    simp only [smul_apply, smul_eq_mul, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply]
    exact mul_pos (inv_pos.mpr (sq_pos_of_pos z.im_pos))
      (real_inner_self_pos.mpr ((tangentSpaceCastModel 𝓘(ℝ, ℂ) z).map_ne_zero_iff.mpr hv))
  isVonNBounded z := by
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    have hb := (NormedSpace.isVonNBounded_ball ℝ ℂ z.im).image e.symm.toContinuousLinearMap
    apply Bornology.IsVonNBounded.subset (s₂ := e.symm '' Metric.ball (0 : ℂ) z.im) ?_ hb
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp at hv
    simp only [smul_apply, smul_eq_mul, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply] at hv
    erw [innerSL_apply_apply, real_inner_self_eq_norm_sq] at hv
    have hsq : ‖e v‖ ^ 2 < z.im ^ 2 := by
      simpa only [mul_one, e] using
        (inv_mul_lt_iff₀ (sq_pos_of_pos z.im_pos)).mp hv
    nlinarith [norm_nonneg (e v), z.im_pos]
  contMDiff := by
    intro α
    rw [contMDiffAt_section]
    have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe α :=
      contMDiffAt_extChartAt
    have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ _root_.UpperHalfPlane.im α :=
      Complex.imCLM.contMDiff.contMDiffAt.comp α hcoe
    let euclidean : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
    have hconst : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
        (fun _ : ℍ ↦ euclidean) α :=
      contMDiffAt_const
    have h : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
        (fun z : ℍ ↦ (z.im ^ 2)⁻¹ • euclidean) α :=
      ((him.pow 2).inv₀ (by positivity)).smul hconst
    convert h using 1
    ext z v w
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
    simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      poincare_symm, euclidean, ContinuousLinearEquiv.arrowCongr_apply]

/-- The Poincaré tensor in the tangent coordinates of the inclusion chart. -/
@[simp]
theorem poincareRiemannianMetric_inner (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    poincareRiemannianMetric.inner z v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 := by
  simp only [poincareRiemannianMetric, smul_apply, smul_eq_mul,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.refl_apply]
  erw [innerSL_apply_apply]
  rw [div_eq_mul_inv, mul_comm]

/-- The tangent bundle of the upper half-plane carries the Poincaré tensor. -/
instance instRiemannianBundle : RiemannianBundle (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  ⟨poincareRiemannianMetric.toRiemannianMetric⟩

/-- The Poincaré tensor is smooth as a real Riemannian bundle. -/
instance instIsContMDiffRiemannianBundle : IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ
    (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  Bundle.instIsContMDiffRiemannianBundle poincareRiemannianMetric

/-- Continuity of the Poincaré tensor makes the Riemannian volume construction applicable. -/
instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle ℂ (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  Bundle.instIsContinuousRiemannianBundle poincareRiemannianMetric.toContinuousRiemannianMetric

end TauCeti.UpperHalfPlane
