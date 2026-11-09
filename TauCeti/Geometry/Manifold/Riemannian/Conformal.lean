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
* the inverse metric on arbitrary covectors: raising an index and pairing covectors scale by
  `f⁻¹`, and the covector operator norm scales by `1 / √f`;
* the gradient, through the inverse metric: `grad_ĝ u = f⁻¹ grad_g u`, and hence
  `⟪grad_ĝ u, grad_ĝ w⟫_ĝ = f⁻¹ ⟪grad_g u, grad_g w⟫_g`;
* the chart Gram matrix and its inverse, `G_ĝ = f G_g` and `G_ĝ⁻¹ = f⁻¹ G_g⁻¹`, and the
  volume density, `dV_ĝ = f ^ (n / 2) dV_g` in real dimension `n`.

Tangent vectors of the copies are compared with tangent vectors of `M` through the differential of
`TauCeti.WithMetric.ofWithMetric`, which is the identity of the model space. Covectors on `M`
are pulled back by that same differential, so each copy carries its own metric norm. Index raising
uses `Riemannian.Tensor.rieszDual`. The inverse-metric laws hold for `Cⁿ` metrics and positive
`Cⁿ` factors, including `n = 0`.

For the Yamabe problem, `f = u ^ (4 / (n - 2))` with `u` positive, so that
`f ^ (n / 2) = u ^ (2 n / (n - 2))`.

## Main results

* `TauCeti.WithMetric.inner_rescale`: the inner product of the rescaled metric.
* `TauCeti.WithMetric.mfderiv_ofWithMetric_rieszDual_rescale`: raising a covector's index
  for the rescaled metric multiplies its transported Riesz dual by `f⁻¹`.
* `TauCeti.WithMetric.apply_rieszDual_rescale`: the inverse-metric pairing scales by `f⁻¹`.
* `TauCeti.WithMetric.norm_sq_covector_rescale` and `TauCeti.WithMetric.norm_covector_rescale`:
  the squared covector norm scales by `f⁻¹`, and the norm by `1 / √f`.
* `TauCeti.WithMetric.mfderiv_ofWithMetric_mgradient_rescale`: the gradient for the rescaled
  metric is `f⁻¹` times the gradient for `g`.
* `TauCeti.WithMetric.inner_mgradient_rescale`: the corresponding identity for the pointwise
  Dirichlet energy density.
* `TauCeti.WithMetric.chartGramMatrix_rescale` and
  `TauCeti.WithMetric.chartInvGramMatrix_rescale`: the chart Gram matrix scales by `f`, and its
  inverse by `f⁻¹`.
* `TauCeti.WithMetric.chartVolumeDensity_rescale`: the volume density of the rescaled metric is
  `f ^ (n / 2)` times that of `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (conformal metrics, dual metric, gradient and volume form).
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

/-- Raising the index of a covector for `f g` gives `f⁻¹` times its Riesz dual for `g`,
with both vectors transported to the underlying manifold. -/
theorem mfderiv_ofWithMetric_rieszDual_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)
        (rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
          (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))) =
      (f x)⁻¹ • mfderiv I I ofWithMetric (toWithMetric g x)
        (rieszDual (I := I) (toWithMetric g x)
          (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))) := by
  set v := mfderiv I I ofWithMetric (toWithMetric g x)
    (rieszDual (I := I) (toWithMetric g x)
      (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))))
  suffices h : mfderiv I I (toWithMetric (g.rescale f hf hf_pos)) x ((f x)⁻¹ • v) =
      rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
        (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))) by
    rw [← h, mfderiv_ofWithMetric_mfderiv_toWithMetric]
  rw [eq_rieszDual_iff_inner_eq]
  intro w
  have h := inner_rieszDual
    (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))
    (mfderiv I I (toWithMetric g) x
      (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x) w))
  rw [inner_def, mfderiv_ofWithMetric_mfderiv_toWithMetric] at h
  rw [inner_rescale, mfderiv_ofWithMetric_mfderiv_toWithMetric]
  simp only [v, map_smul, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply] at h ⊢
  rw [mul_inv_cancel_left₀ (hf_pos x).ne', h]
  rw [mfderiv_ofWithMetric_apply, mfderiv_toWithMetric_apply]

/-- The inverse-metric pairing `φ(ψ♯)` of two covectors scales by `f⁻¹` under `g ↦ f g`. -/
theorem apply_rieszDual_rescale (x : M) (φ ψ : TangentSpace I x →L[ℝ] ℝ) :
    (φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))
        (rieszDual (I := I) (toWithMetric (g.rescale f hf hf_pos) x)
          (ψ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)))) =
      (f x)⁻¹ * (φ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))
        (rieszDual (I := I) (toWithMetric g x)
          (ψ.comp (mfderiv I I ofWithMetric (toWithMetric g x)))) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_ofWithMetric_rieszDual_rescale (g := g) (hf := hf) (hf_pos := hf_pos),
    map_smul, smul_eq_mul]

/-- The squared operator norm of an arbitrary covector scales by `f⁻¹` under `g ↦ f g`. -/
theorem norm_sq_covector_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ ^ 2 =
      (f x)⁻¹ * ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ ^ 2 := by
  simp only [norm_sq_eq_apply_rieszDual]
  exact apply_rieszDual_rescale x φ φ

/-- The operator norm of a covector for `f g` is its norm for `g` divided by `√f`. -/
theorem norm_covector_rescale (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ =
      (Real.sqrt (f x))⁻¹ * ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ := by
  have h := congrArg Real.sqrt (norm_sq_covector_rescale (g := g) (hf := hf) (hf_pos := hf_pos) x φ)
  -- Use operator-norm positivity directly: each domain carries its own metric norm.
  have h₁ : 0 ≤ ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have h₂ : 0 ≤ ‖φ.comp (mfderiv I I ofWithMetric (toWithMetric g x))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  simpa only [Real.sqrt_mul (inv_nonneg.mpr (hf_pos x).le), Real.sqrt_inv,
    Real.sqrt_sq h₁, Real.sqrt_sq h₂] using h

/-- **Gradient under conformal change.** The gradient of a function for the rescaled metric
`f g` is `f⁻¹` times its gradient for `g`, both read as tangent vectors of `M`. -/
theorem mfderiv_ofWithMetric_mgradient_rescale (u : M → ℝ) (x : M) :
    mfderiv I I ofWithMetric (toWithMetric (g.rescale f hf hf_pos) x)
        (mgradient I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x)) =
      (f x)⁻¹ • mfderiv I I ofWithMetric (toWithMetric g x)
        (mgradient I (u ∘ ofWithMetric) (toWithMetric g x)) := by
  -- The chain rule pulls back the differential defining each gradient.
  simpa only [mgradient_def, mvfderiv_comp_ofWithMetric, ofWithMetric_toWithMetric] using
    (mfderiv_ofWithMetric_rieszDual_rescale (g := g) (hf := hf) (hf_pos := hf_pos)
      x (mvfderiv I u x))

/-- The inner product of two gradients for the rescaled metric `f g` is `f⁻¹` times the inner
product of the gradients for `g`. With `u = w`, this is the pointwise Dirichlet energy
density `|du|²_{f g} = f⁻¹ |du|²_g`. -/
theorem inner_mgradient_rescale (u w : M → ℝ) (x : M) :
    inner ℝ (mgradient I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x))
        (mgradient I (w ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x)) =
      (f x)⁻¹ * inner ℝ (mgradient I (u ∘ ofWithMetric) (toWithMetric g x))
        (mgradient I (w ∘ ofWithMetric) (toWithMetric g x)) := by
  -- Identify the gradient pairing with the inverse-metric pairing of the pulled-back differentials.
  simpa only [mgradient_def, inner_rieszDual, mvfderiv_comp_ofWithMetric,
    ofWithMetric_toWithMetric] using
    (apply_rieszDual_rescale (g := g) (hf := hf) (hf_pos := hf_pos)
      x (mvfderiv I u x) (mvfderiv I w x))

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

/-- In chart coordinates, the inverse Gram matrix of `f g` is `f⁻¹` times that of `g`. -/
theorem chartInvGramMatrix_rescale (α x : M) :
    chartInvGramMatrix (I := I) (toWithMetric (g.rescale f hf hf_pos) α)
        (toWithMetric (g.rescale f hf hf_pos) x) =
      (f x)⁻¹ • chartInvGramMatrix (I := I) (toWithMetric g α) (toWithMetric g x) := by
  rw [chartInvGramMatrix_def, chartInvGramMatrix_def, chartGramMatrix_rescale]
  by_cases h : IsUnit (chartGramMatrix (I := I) (toWithMetric g α) (toWithMetric g x)).det
  · simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] using
      Matrix.inv_smul' _ (Units.mk0 (f x) (hf_pos x).ne') h
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ ?_,
      Matrix.nonsing_inv_apply_not_isUnit _ h, smul_zero]
    rw [Matrix.det_smul, IsUnit.mul_iff]
    exact fun hdet ↦ h hdet.2

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
