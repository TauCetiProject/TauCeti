/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# First-order quantities under a conformal change of metric

Let `g` be a Riemannian metric on `M` and `f` a positive function, and let `ĝ = f g` be the
conformally rescaled metric `Bundle.ContMDiffRiemannianMetric.rescale`. The two metrics live on the
copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`, so that each carries its own
`RiemannianBundle` instance. This file compares the quantities of first order in the metric:

* the inner product: `⟪v, w⟫_ĝ = f ⟪v, w⟫_g`;
* the gradient, through the inverse metric: `grad_ĝ u = f⁻¹ grad_g u`, and hence
  `⟪grad_ĝ u, grad_ĝ w⟫_ĝ = f⁻¹ ⟪grad_g u, grad_g w⟫_g`;
* the chart Gram matrix, `G_ĝ = f G_g`, and the Riemannian volume density,
  `dV_ĝ = f ^ (n / 2) dV_g` in real dimension `n`.

Tangent vectors of the copies are compared with tangent vectors of `M` through the differential of
`TauCeti.WithMetric.ofWithMetric`, which is the identity of the model space.

For the Yamabe problem, `f = u ^ (4 / (n - 2))` with `u` positive, so that
`f ^ (n / 2) = u ^ (2 n / (n - 2))`.

## Main results

* `TauCeti.WithMetric.inner_rescale`: the inner product of the rescaled metric.
* `TauCeti.WithMetric.mfderiv_ofWithMetric_mgradient_rescale`: the gradient for the rescaled
  metric is `f⁻¹` times the gradient for `g`.
* `Bundle.ContMDiffRiemannianMetric.mgradient_rescale`: the same gradient law with each metric
  installed in turn as the `RiemannianBundle` instance of the tangent bundle of `M` itself, the
  form used with the Levi-Civita connection law.
* `TauCeti.WithMetric.inner_mgradient_rescale`: the corresponding identity for the pointwise
  Dirichlet energy density.
* `TauCeti.WithMetric.chartVolumeDensity_rescale`: the volume density of the rescaled metric is
  `f ^ (n / 2)` times that of `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (conformal metrics, gradient and volume form).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.WithMetric

open Riemannian.Tensor TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x}

/-- The inner product of the rescaled metric `f g` is `f` times that of `g`. -/
theorem inner_rescale (x : WithMetric (g.rescale f hf hf_pos)) (v w : TangentSpace I x) :
    inner ℝ v w = f x.ofWithMetric *
      g.inner x.ofWithMetric (mfderiv I I ofWithMetric x v) (mfderiv I I ofWithMetric x w) := by
  rw [inner_def, ContMDiffRiemannianMetric.rescale_inner]

/-- **Gradient under conformal change.** The gradient of a function for the rescaled metric
`f g` is `f⁻¹` times its gradient for `g`, both read as tangent vectors of `M`. -/
theorem mfderiv_ofWithMetric_mgradient_rescale (u : M → ℝ) (x : M) :
    mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)
        (mgradient I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x)) =
      (f x)⁻¹ • mfderiv I I ofWithMetric (toWithMetric g x)
        (mgradient I (u ∘ ofWithMetric) (toWithMetric g x)) := by
  set c : TangentSpace I x := (f x)⁻¹ • mfderiv I I ofWithMetric (toWithMetric g x)
    (mgradient I (u ∘ ofWithMetric) (toWithMetric g x))
  suffices h : mfderiv I I (toWithMetric (g.rescale f hf hf_pos)) x c =
      mgradient I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x) by
    rw [← h, mfderiv_ofWithMetric_mfderiv_toWithMetric]
  rw [eq_mgradient_iff]
  intro w
  have hg := inner_mgradient (I := I) (f := u ∘ ofWithMetric) (x := toWithMetric g x)
    (mfderiv I I (toWithMetric g) x
      (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x) w))
  rw [inner_def, mvfderiv_comp_ofWithMetric_apply, mfderiv_ofWithMetric_mfderiv_toWithMetric]
    at hg
  rw [inner_rescale, mvfderiv_comp_ofWithMetric_apply, mfderiv_ofWithMetric_mfderiv_toWithMetric,
    ofWithMetric_toWithMetric, ← hg]
  simp only [c, map_smul, smul_apply, smul_eq_mul]
  field_simp [(hf_pos x).ne']

/-- The inner product of two gradients for the rescaled metric `f g` is `f⁻¹` times the inner
product of the gradients for `g`. With `u = w`, this is the pointwise Dirichlet energy
density `|du|²_{f g} = f⁻¹ |du|²_g`. -/
theorem inner_mgradient_rescale (u w : M → ℝ) (x : M) :
    inner ℝ (mgradient I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x))
        (mgradient I (w ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x)) =
      (f x)⁻¹ * inner ℝ (mgradient I (u ∘ ofWithMetric) (toWithMetric g x))
        (mgradient I (w ∘ ofWithMetric) (toWithMetric g x)) := by
  rw [inner_rescale, mfderiv_ofWithMetric_mgradient_rescale,
    mfderiv_ofWithMetric_mgradient_rescale, inner_def]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp [(hf_pos x).ne']

/-- The chart Gram matrix of the rescaled metric `f g` is `f` times that of `g`. -/
theorem chartGramMatrix_rescale (α x : M) :
    chartGramMatrix (I := I) (toWithMetric (g.rescale f hf hf_pos) α)
        (toWithMetric (g.rescale f hf hf_pos) x) =
      f x • chartGramMatrix (I := I) (toWithMetric g α) (toWithMetric g x) := by
  ext i j
  rw [Matrix.smul_apply, chartGramMatrix_apply, chartGramMatrix_apply, inner_rescale, inner_def,
    mfderiv_ofWithMetric_chartLocalFrame, mfderiv_ofWithMetric_chartLocalFrame,
    mfderiv_ofWithMetric_chartLocalFrame, mfderiv_ofWithMetric_chartLocalFrame]
  simp only [smul_eq_mul]

/-- **Volume density under conformal change.** In real dimension `n`, the volume density of the
rescaled metric `f g` in any chart is `f ^ (n / 2)` times that of `g`. -/
theorem chartVolumeDensity_rescale (α x : M) :
    chartVolumeDensity (I := I) (toWithMetric (g.rescale f hf hf_pos) α)
        (toWithMetric (g.rescale f hf hf_pos) x) =
      f x ^ ((Module.finrank ℝ E : ℝ) / 2) *
        chartVolumeDensity (I := I) (toWithMetric g α) (toWithMetric g x) := by
  rw [chartVolumeDensity_def, chartVolumeDensity_def, chartGramMatrix_rescale, Matrix.det_smul,
    Fintype.card_fin, Real.sqrt_mul (pow_nonneg (hf_pos x).le _),
    Real.sqrt_pow_eq_rpow (hf_pos x).le]

end TauCeti.WithMetric

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- **Gradient under conformal change.** The gradient of a function for the rescaled metric
`f g` is `f⁻¹` times its gradient for `g`. -/
theorem mgradient_rescale [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x) (u : M → ℝ) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      mgradient I u x) =
    (f x)⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      mgradient I u x) := by
  have hg (v : TangentSpace I x) :
      g.inner x (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩; mgradient I u x) v = mvfderiv I u x v := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact inner_mgradient v
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
  rw [inner_riemannianBundle, rescale_inner, map_smul, smul_apply, hg, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (hf_pos x).ne', one_mul]

end Bundle.ContMDiffRiemannianMetric
