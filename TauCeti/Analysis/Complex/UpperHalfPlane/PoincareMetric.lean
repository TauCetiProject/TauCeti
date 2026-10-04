/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# The Poincaré Riemannian metric

The canonical tensor on the upper half-plane is the Euclidean inner product divided by the
square of the imaginary coordinate. We construct it as a smooth real Riemannian metric, the
Euclidean metric rescaled by `im⁻²` through `Bundle.ContMDiffRiemannianMetric.rescale`, so that it
can be used by the Riemannian volume construction.

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

/-- The flat metric on the upper half-plane: the Euclidean tensor of `ℂ`, read through the
inclusion chart. -/
private def euclideanMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) where
  inner z := by
    -- Defining a foundational tangent metric uses the explicit identification with its model.
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    exact (e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
      (innerSL ℝ (E := ℂ))
  symm z v w := by
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply]
    exact real_inner_comm (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) |>.symm
  pos z v hv := by
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply]
    exact real_inner_self_pos.mpr ((tangentSpaceCastModel 𝓘(ℝ, ℂ) z).map_ne_zero_iff.mpr hv)
  isVonNBounded z := by
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    have hb := (NormedSpace.isVonNBounded_ball ℝ ℂ 1).image e.symm.toContinuousLinearMap
    apply Bornology.IsVonNBounded.subset (s₂ := e.symm '' Metric.ball (0 : ℂ) 1) ?_ hb
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp at hv
    erw [innerSL_apply_apply, real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg (e v)]
  contMDiff := by
    intro α
    rw [contMDiffAt_section]
    let euclidean : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
    have hconst : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
        (fun _ : ℍ ↦ euclidean) α :=
      contMDiffAt_const
    convert hconst using 1
    ext z v w
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
    simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      poincare_symm, euclidean, ContinuousLinearEquiv.arrowCongr_apply]

private theorem euclideanMetric_inner (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    euclideanMetric.inner z v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) := by
  simp only [euclideanMetric, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply]
  erw [innerSL_apply_apply]

/-- The factor `im⁻²` of the Poincaré metric is smooth on the upper half-plane. -/
private theorem contMDiff_inv_im_sq :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ fun z : ℍ ↦ (z.im ^ 2)⁻¹ := by
  intro α
  have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe α :=
    contMDiffAt_extChartAt
  have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ _root_.UpperHalfPlane.im α :=
    Complex.imCLM.contMDiff.contMDiffAt.comp α hcoe
  exact (him.pow 2).inv₀ (by positivity)

/-- The smooth Poincaré metric: the Euclidean tensor rescaled by `im⁻²`. -/
def poincareRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  euclideanMetric.rescale (fun z : ℍ ↦ (z.im ^ 2)⁻¹) contMDiff_inv_im_sq
    fun z ↦ inv_pos.mpr (sq_pos_of_pos z.im_pos)

/-- The Poincaré tensor in the tangent coordinates of the inclusion chart. -/
@[simp]
theorem _root_.UpperHalfPlane.poincareRiemannianMetric_inner (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    poincareRiemannianMetric.inner z v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 := by
  rw [poincareRiemannianMetric, Bundle.ContMDiffRiemannianMetric.rescale_inner,
    euclideanMetric_inner, div_eq_inv_mul]

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
