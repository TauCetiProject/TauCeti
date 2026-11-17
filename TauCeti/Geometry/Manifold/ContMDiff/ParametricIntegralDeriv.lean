/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral

/-!
# Differentiating an integral over a compact manifold under the integral sign

Let `f : ℝ → N → F` be a function of a real parameter `t` and of a point of a compact manifold `N`
carrying a finite measure `μ`. If `(t, a) ↦ f t a` is `C^1` at every point `(t₀, a)`, then

`d/dt ∫ a, f t a ∂μ = ∫ a, ∂_t f t a ∂μ` at `t = t₀`,

where `∂_t f t a = deriv (fun s ↦ f s a) t` is the partial derivative in the parameter. The partial
derivative of a `C^n` function is `C^m` jointly in `(t, a)` whenever `m + 1 ≤ n`; this is
`ContMDiffAt.fderiv_right`, the regularity of the derivative in a vector-space variable of a
family, evaluated at `1`.
Applying the first statement to `∂_t f` gives the second derivative of the integral under a `C^2`
hypothesis.

The proof bounds `∂_t f` on `[t₀ - ε, t₀ + ε] × N` by compactness and applies Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The manifold `N` may have boundary and
corners, and no orientation is involved.

## Main results

* `TauCeti.contMDiffAt_deriv_uncurry`: the partial derivative in the parameter of a `C^n`
  function is `C^m` jointly, for `m + 1 ≤ n`.
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

/-- **Regularity of the partial derivative in a real parameter.** If `(t, a) ↦ f t a` is `C^n` at
`p₀` and `m + 1 ≤ n`, then the partial derivative `(t, a) ↦ ∂_t f t a` is `C^m` at `p₀`. -/
theorem contMDiffAt_deriv_uncurry [IsManifold J 1 N] {n m : ℕ∞ω} {p₀ : ℝ × N}
    (hf : ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) n (uncurry f) p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) m (fun p : ℝ × N ↦ deriv (fun s ↦ f s p.2) p.1) p₀ := by
  -- Swap the factors to use the derivative in the vector-space variable of a family.
  have hswap : ContMDiffAt (J.prod 𝓘(ℝ)) 𝓘(ℝ, F) n (uncurry fun (a : N) (s : ℝ) ↦ f s a)
      (p₀.2, p₀.1) :=
    hf.comp (p₀.2, p₀.1) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hswap.fderiv_right hmn).comp p₀ (contMDiffAt_snd.prodMk contMDiffAt_fst)
  exact ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).contMDiff.contMDiffAt.comp p₀ h :)

variable [IsManifold J 1 N] [CompactSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N} [IsFiniteMeasure μ] {t₀ : ℝ}

/-- **Differentiation under the integral sign over a compact manifold.** If `(t, a) ↦ f t a` is
`C^1` at every point `(t₀, a)`, then `t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at
`t₀`. -/
theorem hasDerivAt_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a)) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ := by
  -- A neighbourhood `U × N` of `{t₀} × N` on which `f` is `C^1`, and a closed ball inside `U`.
  obtain ⟨U, V, hU, -, ht₀U, hV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ).prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry f) isCompact_univ (by simp) fun a _ ↦ hf a
  rw [univ_subset_iff.1 hV] at hfU
  have hfat : ∀ p ∈ U ×ˢ univ, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) p :=
    fun p hp ↦ hfU.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU t₀ ht₀U
  set D : ℝ → N → F := fun t a ↦ deriv (fun s ↦ f s a) t
  -- The partial derivative is continuous on `U × N`, hence bounded on a compact slab.
  have hDc : ContinuousOn (uncurry D) (U ×ˢ univ) := fun p hp ↦
    (contMDiffAt_deriv_uncurry (m := 0) (hfat p hp) (by simp)).continuousAt.continuousWithinAt
  have hslab : closedBall t₀ (ε / 2) ×ˢ (univ : Set N) ⊆ U ×ˢ univ :=
    prod_mono (fun t ht ↦ hεU (Metric.closedBall_subset_ball (by linarith) ht)) subset_rfl
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ (ε / 2)).prod
    isCompact_univ).exists_bound_of_continuousOn (hDc.mono hslab)
  -- Each slice in the parameter is differentiable on `U`.
  have hslice : ∀ t ∈ U, ∀ a, HasDerivAt (fun s ↦ f s a) (D t a) t := fun t ht a ↦ by
    have h : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, F) 1 (fun s ↦ f s a) t :=
      (hfat (t, a) ⟨ht, mem_univ a⟩).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (h.contDiffAt.differentiableAt one_ne_zero).hasDerivAt
  have hcont : ∀ {g : ℝ → N → F} {t : ℝ}, ContinuousOn (uncurry g) (U ×ˢ univ) → t ∈ U →
      ContinuousOn (g t) univ := fun {g t} hg ht ↦
    hg.comp (continuous_const.prodMk continuous_id).continuousOn fun a _ ↦ ⟨ht, mem_univ a⟩
  have hmeas : ∀ {g : ℝ → N → F} {t : ℝ}, ContinuousOn (uncurry g) (U ×ˢ univ) → t ∈ U →
      AEStronglyMeasurable (g t) μ := fun hg ht ↦ by
    simpa only [Measure.restrict_univ] using (hcont hg ht).aestronglyMeasurable_of_isCompact
      (μ := μ) isCompact_univ MeasurableSet.univ
  have hballU : ball t₀ (ε / 2) ⊆ U := fun t ht ↦ hεU (Metric.ball_subset_ball (by linarith) ht)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ ↦ C)
    (Metric.ball_mem_nhds t₀ (half_pos hε))
    (eventually_of_mem (hU.mem_nhds ht₀U) fun t ht ↦ hmeas hfU.continuousOn ht) ?_
    (hmeas hDc ht₀U) ?_ (integrable_const C) ?_).2
  · obtain ⟨C₀, hC₀⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont hfU.continuousOn ht₀U)
    exact .of_bound (hmeas hfU.continuousOn ht₀U) C₀ (ae_of_all _ fun a ↦ hC₀ a (mem_univ a))
  · exact ae_of_all _ fun a t ht ↦ hC (t, a) ⟨Metric.ball_subset_closedBall ht, mem_univ a⟩
  · exact ae_of_all _ fun a t ht ↦ hslice t (hballU ht) a

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
  exact contMDiffAt_deriv_uncurry (f := f) (hfat t₀ ht₀U a) (by norm_num)

end TauCeti
