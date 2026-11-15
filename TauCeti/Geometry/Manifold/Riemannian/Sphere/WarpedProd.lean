/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Scalar curvature of warped round spheres over the real line

On any open subset of `ℝ`, the metric `dr² + f(r)² g_(Sⁿ)` has scalar curvature
`n(n-1)(1-f'²)/f² - 2n f''/f`. The warping function need only be smooth and
nowhere zero on that open set. In particular, no standard-cap assumptions enter
this computation.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43.
-/

public noncomputable section

open Bundle TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

/-- Scalar curvature of `dr² + f(r)² g_(Sⁿ)` on an arbitrary open subset of
`ℝ` times the unit sphere. Smoothness and nonvanishing are required only on the
open set; the sign of `f` is irrelevant. -/
theorem scalarCurvature_warpedProdTangentSpace_real_sphere
    (U : Opens ℝ) {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
    (hf₀ : ∀ r : U, f r ≠ 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (p : U × Metric.sphere (0 : V) 1) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    ((g.restrictOpenTangentSpace U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
      ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).scalarCurvature p =
      (n : ℝ) * (n - 1) * (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 -
        2 * n * deriv (deriv f) p.1 / f p.1 := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  have hg : g.scalarCurvature (p.1 : ℝ) = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hf₂ : ContDiffAt ℝ 2 f (p.1 : ℝ) :=
    (contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1
      hf.contMDiffAt)).of_le (by simp)
  rw [ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace,
    ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace,
    scalarCurvature_sphereRoundMetric_ofLE, hg,
    laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂,
    sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num))]
  simp only [finrank_euclideanSpace_fin]
  ring

end TauCeti
