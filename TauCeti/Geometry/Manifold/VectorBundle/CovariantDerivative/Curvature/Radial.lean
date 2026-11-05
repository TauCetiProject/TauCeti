/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Scalar curvature of radial conformal metrics

Let `F` be a finite-dimensional real inner product space of dimension `N`. In polar coordinates
`y = e^s u`, the Euclidean metric is `e^(2 s) (ds² + g_(S^(N - 1)))`, so the metric
`e^(2 w(s)) (ds² + g_(S^(N - 1)))` is the Euclidean metric multiplied by `e^(2 φ)` with the radial
exponent `φ(z) = w(log ‖z‖) - log ‖z‖`. From the Laplacian and the gradient of that exponent
(`TauCeti.laplacian_comp_log_norm_sub_log_norm` and
`TauCeti.norm_gradient_comp_log_norm_sub_log_norm`), the conformal change of scalar curvature gives
the scalar curvature

`(N - 1) e^(-2 w(s)) ((N - 2) (1 - w'(s)²) - 2 w''(s))`

away from the origin.

## Main results

* `TauCeti.scalarCurvature_rescale_exp_radial`: the scalar curvature of the Euclidean metric
  multiplied by `e^(2 (w(log ‖y‖) - log ‖y‖))`, away from the origin.
-/

public section

noncomputable section

open Real Module Bundle Filter InnerProductSpace Laplacian
open scoped ContDiff Manifold Topology Gradient

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Scalar curvature of a radial conformal metric.** Let `φ` be a smooth function on a real inner
product space of dimension `N` which, near a point `y ≠ 0`, is `w(log ‖z‖) - log ‖z‖` for a
function `w` that is `C²` at `s = log ‖y‖`. Then the Euclidean metric multiplied by `e^(2 φ)` has
scalar curvature `(N - 1) e^(-2 w(s)) ((N - 2) (1 - w'(s)²) - 2 w''(s))` at `y`. In polar
coordinates `y = e^s u` this metric is `e^(2 w(s)) (ds² + g_(S^(N - 1)))`. -/
theorem scalarCurvature_rescale_exp_radial {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) {w : ℝ → ℝ} {y : F}
    (hy : y ≠ 0) (hw : ContDiffAt ℝ 2 w (log ‖y‖))
    (heq : φ =ᶠ[𝓝 y] fun z ↦ w (log ‖z‖) - log ‖z‖) :
    (((riemannianMetricVectorSpace F).ofLE le_top).rescale (fun z ↦ exp (2 * φ z))
        (contDiff_const.mul hφ).exp.contMDiff fun _ ↦ exp_pos _).scalarCurvature y =
      (finrank ℝ F - 1) * exp (-2 * w (log ‖y‖)) *
        ((finrank ℝ F - 2) * (1 - deriv w (log ‖y‖) ^ 2) - 2 * deriv (deriv w) (log ‖y‖)) := by
  have hgrad : DifferentiableAt ℝ (∇ φ) y :=
    ((hφ.gradient_right (m := 1) (by simp)).differentiable (by simp)) y
  -- The conformal change formula, applied to the flat Euclidean metric `g`, involves only the
  -- Laplacian and the gradient of `φ` for `g`. The formula installs `g` with lowered
  -- smoothness; the flat identifications are transported along `toRiemannianMetric_ofLE`.
  rw [ContMDiffRiemannianMetric.scalarCurvature_rescale _ _ _ (φ := φ) (fun _ ↦ rfl) y]
  have hscal : ((riemannianMetricVectorSpace F).ofLE
      (le_top : (∞ : WithTop ℕ∞) ≤ ω)).scalarCurvature y = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection _
      -- Mathlib's `RiemannianBundle` instance on the tangent spaces of `F` is defined to be the
      -- standard metric `(riemannianMetricVectorSpace F).toRiemannianMetric`, so this is `rfl`.
      (by rw [ContMDiffRiemannianMetric.toRiemannianMetric_ofLE]; rfl),
      TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space]
  have hm := ContMDiffRiemannianMetric.toRiemannianMetric_ofLE (riemannianMetricVectorSpace F)
    (le_top : (∞ : WithTop ℕ∞) ≤ ω)
  have hΔ : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      Manifold.laplaceBeltrami 𝓘(ℝ, F) φ y) = Δ φ y :=
    TauCeti.Manifold.laplaceBeltrami_eq_laplacian_of_eq
      (inst := ⟨((riemannianMetricVectorSpace F).ofLE le_top).toRiemannianMetric⟩) hm hgrad
  have hG : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      ‖Manifold.mgradient 𝓘(ℝ, F) φ y‖) = ‖∇ φ y‖ :=
    TauCeti.Manifold.norm_mgradient_eq_norm_gradient_of_eq
      (inst := ⟨((riemannianMetricVectorSpace F).ofLE le_top).toRiemannianMetric⟩) hm _ y
  have hexp : (exp (2 * φ y))⁻¹ = exp (-2 * w (log ‖y‖)) * ‖y‖ ^ 2 := by
    have harg : -(2 * (w (log ‖y‖) - log ‖y‖)) = -2 * w (log ‖y‖) + log (‖y‖ ^ 2) := by
      rw [log_pow]
      push_cast
      ring
    rw [heq.eq_of_nhds, ← exp_neg, harg, exp_add, exp_log (by positivity)]
  rw [hscal, hΔ, hG, hexp, (laplacian_congr_nhds heq).eq_of_nhds,
    laplacian_comp_log_norm_sub_log_norm hy hw, heq.gradient_eq,
    norm_gradient_comp_log_norm_sub_log_norm hy (hw.differentiableAt (by simp)), mul_pow, sq_abs]
  have hρ : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  field_simp
  ring

end TauCeti
