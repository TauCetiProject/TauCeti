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

More generally, for a parameter `z` in a normed space the Fréchet derivative of the integral is
the integral of the Fréchet derivatives. The proof finds a neighbourhood `U × N` of `{z₀} × N` on
which the integrand is `C^1` and applies `TauCeti.hasFDerivAt_integral_of_contMDiffOn`. The
manifold `N` may have boundary and corners, and no orientation is involved.

## Main results

* `TauCeti.hasFDerivAt_integral_of_contMDiffAt`: differentiation under the integral sign over a
  compact manifold, for a parameter in a normed space.
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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℝ → N → F}

variable [IsManifold J 1 N] [CompactSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N} [IsFiniteMeasure μ] {t₀ : ℝ}

/-- **Differentiation under the integral sign over a compact manifold.** If `(z, a) ↦ g z a` is
`C^1` at every point `(z₀, a)`, for a parameter `z` in a normed space, then the derivative of
`z ↦ ∫ a, g z a ∂μ` at `z₀` is the integral of the derivatives of the functions `z ↦ g z a`. -/
theorem hasFDerivAt_integral_of_contMDiffAt {g : E' → N → F} {z₀ : E'}
    (hg : ∀ a, ContMDiffAt (𝓘(ℝ, E').prod J) 𝓘(ℝ, F) 1 (uncurry g) (z₀, a)) :
    HasFDerivAt (fun z ↦ ∫ a, g z a ∂μ) (∫ a, fderiv ℝ (fun z ↦ g z a) z₀ ∂μ) z₀ := by
  -- A neighbourhood `U × N` of `{z₀} × N` on which `g` is `C^1`.
  obtain ⟨U, V, hU, -, hz₀U, hV, hgU⟩ := exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ, E').prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry g) isCompact_univ (by simp) fun a _ ↦ hg a
  rw [univ_subset_iff.1 hV] at hgU
  exact hasFDerivAt_integral_of_contMDiffOn hU hz₀U hgU

/-- **Differentiation under the integral sign over a compact manifold.** If `(t, a) ↦ f t a` is
`C^1` at every point `(t₀, a)`, then `t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at
`t₀`. -/
theorem hasDerivAt_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a)) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ := by
  -- Evaluating the integrated derivative at `1` commutes with the integral.
  have e := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).symm.integral_comp_comm
    (μ := μ) (fun a ↦ fderiv ℝ (fun s ↦ f s a) t₀)
  simp only [ContinuousLinearMap.toSpanSingletonCLE_symm_apply, fderiv_apply_one_eq_deriv] at e
  rw [e]
  exact (hasFDerivAt_integral_of_contMDiffAt (μ := μ) hf).hasDerivAt

/-- **The second derivative of an integral over a compact manifold.** If `(t, a) ↦ f t a` is
`C^2` at every point `(t₀, a)`, then the derivative of `t ↦ ∫ a, f t a ∂μ` has derivative
`∫ a, ∂_t² f t₀ a ∂μ` at `t₀`. -/
theorem hasDerivAt_deriv_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 2 (uncurry f) (t₀, a)) :
    HasDerivAt (deriv fun t ↦ ∫ a, f t a ∂μ)
      (∫ a, deriv (fun s ↦ deriv (fun r ↦ f r a) s) t₀ ∂μ) t₀ := by
  -- A neighbourhood `U × N` of `{t₀} × N` on which `f` is `C^1`.
  obtain ⟨U, V, hU, -, ht₀U, hV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ).prod J)
    (J := 𝓘(ℝ, F)) (n := 1) (f := uncurry f) isCompact_univ (by simp)
    fun a _ ↦ (hf a).of_le (by norm_num)
  rw [univ_subset_iff.1 hV] at hfU
  have hfat : ∀ t ∈ U, ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t, a) :=
    fun t ht a ↦ hfU.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ a⟩)
  -- Near `t₀` the first derivative of the integral is the integral of `∂_t f`.
  have hderiv : (deriv fun t ↦ ∫ a, f t a ∂μ) =ᶠ[𝓝 t₀]
      fun t ↦ ∫ a, deriv (fun s ↦ f s a) t ∂μ :=
    eventually_of_mem (hU.mem_nhds ht₀U) fun t ht ↦
      (hasDerivAt_parametric_integral (J := J) (hfat t ht)).deriv
  refine (hasDerivAt_parametric_integral (J := J) (f := fun t a ↦ deriv (fun s ↦ f s a) t)
    fun a ↦ ?_).congr_of_eventuallyEq hderiv
  exact (hf a).deriv_uncurry (by norm_num)

end TauCeti
