/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Nonnegative
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Curvature of warped round spheres over the real line

On any open subset of `ℝ`, the metric `dr² + f(r)² g_(Sⁿ)` has scalar curvature
`n(n-1)(1-f'²)/f² - 2n f''/f`. The warping function need only be smooth and
nowhere zero on that open set. In particular, no standard-cap assumptions enter
these computations. The sectional curvature is nonnegative when `f f'' ≤ 0` and
`f'² ≤ 1` at the point.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43.
-/

public noncomputable section

open Bundle CovariantDerivative TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold

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

/-- The metric `dr² + f(r)² g_(Sⁿ)` has nonnegative sectional curvature when
`f f'' ≤ 0` and `f'² ≤ 1` at the radial coordinate. The warping function need
only be smooth and nonzero on the open set; its sign is irrelevant. -/
theorem sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg
    (U : Opens ℝ) {f : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : U ↦ f r))
    (hf₀ : ∀ r : U, f r ≠ 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (p : U × Metric.sphere (0 : V) 1)
    (hdd : f p.1 * deriv (deriv f) p.1 ≤ 0) (hd : deriv f p.1 ^ 2 ≤ 1)
    (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
    letI : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨((g.restrictOpenTangentSpace U).warpedProdTangentSpace (fun r ↦ f r) hf hf₀
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top)).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (U × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p u v := by
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let g₁ := g.restrictOpenTangentSpace U
  let g₂ := (sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : U ↦ TangentSpace 𝓘(ℝ) r) := ⟨g₁.toRiemannianMetric⟩
  let : RiemannianBundle (fun s : Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓡 n) s) :=
    ⟨g₂.toRiemannianMetric⟩
  let : RiemannianBundle (fun q : U × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(g₁.warpedProdTangentSpace (fun r ↦ f r) hf hf₀ g₂).toRiemannianMetric⟩
  have h : IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1) (fun r : U ↦ f r) :=
    ⟨fun q a b ↦ ContMDiffRiemannianMetric.warpedProdTangentSpace_inner _ _ _ _ _ q a b⟩
  have hf₂ : ContDiffAt ℝ 2 f (p.1 : ℝ) :=
    (contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1
      hf.contMDiffAt)).of_le (by simp)
  apply h.sectionalCurvature_nonneg_of_finrank_le_one hf (by simp) p
  · rwa [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv U hf₂]
  · intro a b
    have hR := g₂.isConstantCurvatureTensor_iff 1 |>.mp
      isConstantCurvatureTensor_sphereRoundMetric_ofLE p.2 a b b
    rw [hR, one_smul]
    simp only [inner_sub_left, real_inner_smul_left]
    rw [sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv U
      (hf₂.differentiableAt (by norm_num)), Matrix.real_det_gram_fin_two]
    have hgram := (Matrix.posSemidef_gram ℝ ![a, b]).det_nonneg
    rw [Matrix.real_det_gram_fin_two] at hgram
    have hbound := mul_le_mul_of_nonneg_right hd hgram
    simp only [real_inner_comm b a] at *
    nlinarith

end TauCeti
