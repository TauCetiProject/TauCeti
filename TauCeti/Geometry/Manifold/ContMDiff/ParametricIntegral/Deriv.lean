/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic

/-!
# Differentiating an integral over a compact manifold under the integral sign

Let `f : ℝ → N → F` be a function of a real parameter `t` and of a point of a compact manifold `N`
carrying a finite measure `μ`. If `(t, a) ↦ f t a` is `C^1` at every point `(t₀, a)`, then

`d/dt ∫ a, f t a ∂μ = ∫ a, ∂_t f t a ∂μ` at `t = t₀`,

where `∂_t f t a = deriv (fun s ↦ f s a) t` is the partial derivative in the parameter. The partial
derivative of a `C^n` function is `C^m` jointly in `(t, a)` whenever `m + 1 ≤ n`
(`ContMDiffAt.deriv_uncurry`). Applying the first statement to `∂_t f` gives the second derivative
of the integral under a `C^2` hypothesis.

The proof finds a neighbourhood `U × N` of `{t₀} × N` on which `f` is `C^1` and applies Mathlib's
`hasFDerivAt_integral_of_continuousOn_fderiv` on the compact set `N`. The manifold `N` may have
boundary and corners, and no orientation is involved.

## Main results

* `TauCeti.hasDerivAt_parametric_integral`: differentiation under the integral sign over a compact
  manifold.
* `TauCeti.hasDerivAt_deriv_parametric_integral`: the second derivative of the integral is the
  integral of the second partial derivative.
-/

public section

open Set Filter MeasureTheory Function Metric
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℝ → N → F}

variable [IsManifold J 1 N] [CompactSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N} [IsFiniteMeasure μ] {t₀ : ℝ}

/-- **Differentiation under the integral sign over a compact manifold.** If `(t, a) ↦ f t a` is
`C^1` at every point `(t₀, a)`, then `t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at
`t₀`. -/
theorem hasDerivAt_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a)) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ := by
  -- A neighbourhood `U × N` of `{t₀} × N` on which `f` is `C^1`.
  obtain ⟨U, V, hU, -, ht₀U, hV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ).prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry f) isCompact_univ (by simp) fun a _ ↦ hf a
  rw [univ_subset_iff.1 hV] at hfU
  have hfat : ∀ p ∈ U ×ˢ univ, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) p :=
    fun p hp ↦ hfU.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
  -- The partial derivative in the parameter, as a linear map, is continuous on `U × N`.
  have hD : ContinuousOn (fun p : ℝ × N ↦ fderiv ℝ (fun s ↦ f s p.2) p.1) (U ×ˢ univ) :=
    fun p hp ↦ by
      simp_rw [← toSpanSingleton_deriv]
      exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).continuous.continuousAt
        |>.comp_continuousWithinAt
          ((hfat p hp).deriv_uncurry (n := 0) (by simp)).continuousAt.continuousWithinAt
  -- Each slice in the parameter is differentiable on `U`.
  have hdiff : ∀ a ∈ (univ : Set N), DifferentiableOn ℝ (fun t ↦ f t a) U := fun a _ t ht ↦
    (((hfat (t, a) ⟨ht, mem_univ a⟩).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
      |>.differentiableAt one_ne_zero).differentiableWithinAt
  have h := hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) (hU.mem_nhds ht₀U) isCompact_univ
    MeasurableSet.univ (measure_ne_top μ univ) subset_rfl hfU.continuousOn hdiff hD
  simp only [Measure.restrict_univ] at h
  -- Evaluate the integrated derivative at `1`.
  have hint : Integrable (fun a ↦ fderiv ℝ (fun s ↦ f s a) t₀) μ :=
    integrableOn_univ.1 <| ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ <|
      hD.comp (continuous_const.prodMk continuous_id).continuousOn fun a _ ↦ ⟨ht₀U, mem_univ a⟩
  simpa only [ContinuousLinearMap.integral_apply hint, fderiv_apply_one_eq_deriv] using h.hasDerivAt

/-- **The second derivative of an integral over a compact manifold.** If `(t, a) ↦ f t a` is
`C^2` at every point `(t₀, a)`, then the derivative of `t ↦ ∫ a, f t a ∂μ` has derivative
`∫ a, ∂_t² f t₀ a ∂μ` at `t₀`. -/
theorem hasDerivAt_deriv_parametric_integral [IsManifold J 2 N]
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 2 (uncurry f) (t₀, a)) :
    HasDerivAt (deriv fun t ↦ ∫ a, f t a ∂μ)
      (∫ a, deriv (fun s ↦ deriv (fun r ↦ f r a) s) t₀ ∂μ) t₀ := by
  obtain ⟨U, V, hU, -, ht₀U, hV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ).prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry f) isCompact_univ (by simp) fun a _ ↦ hf a
  rw [univ_subset_iff.1 hV] at hfU
  have hfat : ∀ t ∈ U, ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 2 (uncurry f) (t, a) :=
    fun t ht a ↦ hfU.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ a⟩)
  -- Near `t₀` the first derivative of the integral is the integral of `∂_t f`.
  have hderiv : (deriv fun t ↦ ∫ a, f t a ∂μ) =ᶠ[𝓝 t₀]
      fun t ↦ ∫ a, deriv (fun s ↦ f s a) t ∂μ :=
    eventually_of_mem (hU.mem_nhds ht₀U) fun t ht ↦
      (hasDerivAt_parametric_integral (J := J) fun a ↦ (hfat t ht a).of_le (by norm_num)).deriv
  refine (hasDerivAt_parametric_integral (J := J) (f := fun t a ↦ deriv (fun s ↦ f s a) t)
    fun a ↦ ?_).congr_of_eventuallyEq hderiv
  exact (hfat t₀ ht₀U a).deriv_uncurry (by norm_num)

end TauCeti
