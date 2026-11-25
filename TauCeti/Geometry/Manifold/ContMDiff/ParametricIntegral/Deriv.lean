/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic

/-!
# Differentiating an integral over a manifold under the integral sign

Let `g : E' → N → F` be a function of a parameter `z` in a normed space and of a point of a
manifold `N` carrying a measure `μ`. If `(z, a) ↦ g z a` is `C¹` on `u × v` for open subsets `u`
of `E'` and `v` of `N`, its derivative in `z` is jointly continuous there
(`TauCeti.continuousOn_fderiv_of_contMDiffOn`). When `N` is compact and `μ` is finite, Mathlib's
`hasFDerivAt_integral_of_continuousOn_fderiv` computes the derivative of `z ↦ ∫ a, g z a ∂μ` as
the integral of the derivatives (`TauCeti.hasFDerivAt_integral_of_contMDiffOn`). Since the flat
exterior derivative `extDeriv` is the alternation of the derivative, a continuous linear
operation, the same holds for it (`TauCeti.extDeriv_integral_of_contMDiffOn`).

The manifold `N` need not be compact if, for `z` near `z₀`, the function `g z` vanishes outside
one compact measurable set `K` of finite measure, as for a variation with fixed compact support
of a noncompact submanifold. It then suffices that `(z, a) ↦ g z a` is `C¹` at every point
`(z₀, a)` with `a ∈ K`: the tube lemma finds a neighbourhood `U × V` of `{z₀} × K` on which it is
`C¹`, and the integral is the integral over `K`. Taking `K = N` recovers the compact case. For a
real parameter `t` this gives

`d/dt ∫ a, f t a ∂μ = ∫ a, ∂_t f t a ∂μ` at `t = t₀`,

where `∂_t f t a = deriv (fun s ↦ f s a) t` is the partial derivative in the parameter. The partial
derivative of a `C^n` function is `C^m` jointly in `(t, a)` whenever `m + 1 ≤ n`
(`ContMDiffAt.deriv_uncurry`), and it also vanishes outside `K` near `t₀`. Applying the first
statement to `∂_t f` gives the second derivative of the integral under a `C^2` hypothesis. The
manifold `N` may have boundary and corners, and no orientation is involved.

## Main results

* `TauCeti.hasFDerivAt_integral_of_contMDiffOn`: differentiation under the integral sign over a
  compact manifold, for an integrand that is `C¹` on `u × N`.
* `TauCeti.extDeriv_integral_of_contMDiffOn`: the exterior derivative of an integral of flat
  differential forms is the integral of their exterior derivatives.
* `IsCompact.hasFDerivAt_integral_of_contMDiffAt`: differentiation under the integral sign for an
  integrand vanishing outside a fixed compact set, for a parameter in a normed space.
* `IsCompact.hasDerivAt_parametric_integral`, `IsCompact.hasDerivAt_deriv_parametric_integral`:
  the first and second derivatives for a real parameter and an integrand vanishing outside a fixed
  compact set.
* `TauCeti.hasFDerivAt_integral_of_contMDiffAt`: differentiation under the integral sign over a
  compact manifold, for a parameter in a normed space and an integrand that is `C¹` along the
  slice of the base parameter.
* `TauCeti.hasDerivAt_parametric_integral`: differentiation under the integral sign over a compact
  manifold, for a real parameter.
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

variable [IsManifold J 1 N] [MeasurableSpace N] [OpensMeasurableSpace N] {μ : Measure N}

section OpenSet

variable [CompactSpace N] [IsFiniteMeasure μ]

-- Cache the canonical alternating-map instances: instance search for the measure-theoretic
-- structure on the nested operator space `E' →L[ℝ] E' [⋀^Fin k]→L[ℝ] F` otherwise fails.
private noncomputable local instance {k : ℕ} : NormedAddCommGroup (E' [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedAddCommGroup
private noncomputable local instance {k : ℕ} : NormedSpace ℝ (E' [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedSpace

variable {g : E' → N → F} {u : Set E'} {z₀ : E'}

omit [MeasurableSpace N] [OpensMeasurableSpace N] [CompactSpace N] in
/-- The derivative in the first variable of a function on `E' × N` that is `C¹` on `u × v`, for
open sets `u` and `v`, is jointly continuous on `u × v`. -/
theorem continuousOn_fderiv_of_contMDiffOn {v : Set N} (hu : IsOpen u) (hv : IsOpen v)
    (hg : ContMDiffOn (𝓘(ℝ, E').prod J) 𝓘(ℝ, F) 1 (uncurry g) (u ×ˢ v)) :
    ContinuousOn (fun p : E' × N ↦ fderiv ℝ (fun z ↦ g z p.2) p.1) (u ×ˢ v) := by
  intro p hp
  have hg' : ContMDiffAt (J.prod 𝓘(ℝ, E')) 𝓘(ℝ, F) 1 (uncurry fun (a : N) (z : E') ↦ g z a)
      p.swap :=
    (hg.contMDiffAt ((hu.prod hv).mem_nhds hp)).comp p.swap
      (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hg'.fderiv_right (n := 0) (by norm_num)).continuousAt.comp
    continuous_swap.continuousAt
  exact h.continuousWithinAt

/-- **Differentiation under the integral sign over a compact manifold of parameters.** If
`(z, a) ↦ g z a` is `C¹` on `u × N` for an open set `u ∋ z₀`, with the parameter `a` ranging over a
compact manifold carrying a finite measure `μ`, then the derivative of `z ↦ ∫ a, g z a ∂μ` at `z₀`
is the integral of the derivatives of the functions `z ↦ g z a`. -/
theorem hasFDerivAt_integral_of_contMDiffOn (hu : IsOpen u) (hz₀ : z₀ ∈ u)
    (hg : ContMDiffOn (𝓘(ℝ, E').prod J) 𝓘(ℝ, F) 1 (uncurry g) (u ×ˢ univ)) :
    HasFDerivAt (fun z ↦ ∫ a, g z a ∂μ) (∫ a, fderiv ℝ (fun z ↦ g z a) z₀ ∂μ) z₀ := by
  have hdiff (a : N) : DifferentiableOn ℝ (fun z ↦ g z a) u := by
    have h : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F) 1 (fun z ↦ g z a) u :=
      hg.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun z hz ↦ ⟨hz, mem_univ a⟩
    exact (contMDiffOn_iff_contDiffOn.1 h).differentiableOn one_ne_zero
  simpa only [Measure.restrict_univ] using
    hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) (hu.mem_nhds hz₀) isCompact_univ
      MeasurableSet.univ (measure_ne_top μ univ) subset_rfl hg.continuousOn
      (fun a _ ↦ hdiff a) (continuousOn_fderiv_of_contMDiffOn hu isOpen_univ hg)

/-- **Exterior derivative under the integral sign.** For a family of flat differential forms
`φ · a` on a normed space, depending on a parameter `a` in a compact manifold carrying a finite
measure `μ`, and jointly `C¹` in the point and the parameter on `u × N` for an open set `u ∋ z₀`,
the exterior derivative of `z ↦ ∫ a, φ z a ∂μ` at `z₀` is the integral of the exterior derivatives
of the forms `φ · a`. -/
theorem extDeriv_integral_of_contMDiffOn [CompleteSpace F] {k : ℕ}
    {φ : E' → N → E' [⋀^Fin k]→L[ℝ] F} (hu : IsOpen u) (hz₀ : z₀ ∈ u)
    (hφ : ContMDiffOn (𝓘(ℝ, E').prod J) 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F) 1 (uncurry φ) (u ×ˢ univ)) :
    extDeriv (fun z ↦ ∫ a, φ z a ∂μ) z₀ = ∫ a, extDeriv (fun z ↦ φ z a) z₀ ∂μ := by
  have hint : Integrable (fun a ↦ fderiv ℝ (fun z ↦ φ z a) z₀) μ :=
    integrableOn_univ.1 <| ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ <|
      (continuousOn_fderiv_of_contMDiffOn hu isOpen_univ hφ).comp
        (continuousOn_const.prodMk continuousOn_id) fun a _ ↦ ⟨hz₀, mem_univ a⟩
  simp only [extDeriv, (hasFDerivAt_integral_of_contMDiffOn hu hz₀ hφ).fderiv,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  exact (ContinuousLinearMap.integral_comp_comm
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E' F) hint).symm

end OpenSet

section CompactSupport

variable {K : Set N}

/-- **Differentiation under the integral sign with compact support in the parameter.** Let `K` be
a compact measurable set of finite measure such that, for `z` near `z₀`, the function `g z`
vanishes outside `K`. If `(z, a) ↦ g z a` is `C¹` at every point `(z₀, a)` with `a ∈ K`, for a
parameter `z` in a normed space, then the derivative of `z ↦ ∫ a, g z a ∂μ` at `z₀` is the
integral of the derivatives of the functions `z ↦ g z a`. -/
theorem _root_.IsCompact.hasFDerivAt_integral_of_contMDiffAt {g : E' → N → F} {z₀ : E'}
    (hK : IsCompact K) (hKm : MeasurableSet K) (hμK : μ K ≠ ⊤)
    (hg : ∀ a ∈ K, ContMDiffAt (𝓘(ℝ, E').prod J) 𝓘(ℝ, F) 1 (uncurry g) (z₀, a))
    (hgK : ∀ᶠ z in 𝓝 z₀, ∀ a ∉ K, g z a = 0) :
    HasFDerivAt (fun z ↦ ∫ a, g z a ∂μ) (∫ a, fderiv ℝ (fun z ↦ g z a) z₀ ∂μ) z₀ := by
  -- A tube `U × V` around `{z₀} × K` on which `g` is `C¹`.
  obtain ⟨U, V, hU, hV, hz₀U, hKV, hgU⟩ := exists_isOpen_prod_contMDiffOn
    (I' := 𝓘(ℝ, E').prod J) (J := 𝓘(ℝ, F)) (f := uncurry g) hK (by simp) hg
  have hdiff (a : N) (ha : a ∈ K) : DifferentiableOn ℝ (fun z ↦ g z a) U := by
    have h : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F) 1 (fun z ↦ g z a) U :=
      hgU.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun z hz ↦ ⟨hz, hKV ha⟩
    exact (contMDiffOn_iff_contDiffOn.1 h).differentiableOn one_ne_zero
  have hset := hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) (𝕜 := ℝ)
    (hU.mem_nhds hz₀U) hK hKm hμK subset_rfl
    (hgU.continuousOn.mono (prod_mono subset_rfl hKV)) hdiff
    ((continuousOn_fderiv_of_contMDiffOn hU hV hgU).mono (prod_mono subset_rfl hKV))
  -- Off `K` the derivative vanishes, since `g z a = 0` for `z` near `z₀`.
  have hzero (a : N) (ha : a ∉ K) : fderiv ℝ (fun z ↦ g z a) z₀ = 0 := by
    have hev : (fun z ↦ g z a) =ᶠ[𝓝 z₀] fun _ ↦ (0 : F) := hgK.mono fun z hz ↦ hz a ha
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hint : (fun z ↦ ∫ a in K, g z a ∂μ) =ᶠ[𝓝 z₀] fun z ↦ ∫ a, g z a ∂μ :=
    hgK.mono fun z hz ↦ setIntegral_eq_integral_of_forall_compl_eq_zero hz
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hset
  exact hset.congr_of_eventuallyEq hint.symm

variable {f : ℝ → N → F} {t₀ : ℝ}

/-- **Differentiation under the integral sign with compact support in the parameter.** Let `K` be
a compact measurable set of finite measure such that, for `t` near `t₀`, the function `f t`
vanishes outside `K`. If `(t, a) ↦ f t a` is `C¹` at every point `(t₀, a)` with `a ∈ K`, then
`t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at `t₀`. -/
theorem _root_.IsCompact.hasDerivAt_parametric_integral (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ K ≠ ⊤)
    (hf : ∀ a ∈ K, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a))
    (hfK : ∀ᶠ t in 𝓝 t₀, ∀ a ∉ K, f t a = 0) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ := by
  -- Evaluating the integrated derivative at `1` commutes with the integral.
  have e := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).symm.integral_comp_comm
    (μ := μ) (fun a ↦ fderiv ℝ (fun s ↦ f s a) t₀)
  simp only [ContinuousLinearMap.toSpanSingletonCLE_symm_apply, fderiv_apply_one_eq_deriv] at e
  rw [e]
  exact (hK.hasFDerivAt_integral_of_contMDiffAt hKm hμK hf hfK).hasDerivAt

/-- **The second derivative of an integral with compact support in the parameter.** Let `K` be a
compact measurable set of finite measure such that, for `t` near `t₀`, the function `f t`
vanishes outside `K`. If `(t, a) ↦ f t a` is `C²` at every point `(t₀, a)` with `a ∈ K`, then the
derivative of `t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t² f t₀ a ∂μ` at `t₀`. -/
theorem _root_.IsCompact.hasDerivAt_deriv_parametric_integral (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ K ≠ ⊤)
    (hf : ∀ a ∈ K, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 2 (uncurry f) (t₀, a))
    (hfK : ∀ᶠ t in 𝓝 t₀, ∀ a ∉ K, f t a = 0) :
    HasDerivAt (deriv fun t ↦ ∫ a, f t a ∂μ)
      (∫ a, deriv (fun s ↦ deriv (fun r ↦ f r a) s) t₀ ∂μ) t₀ := by
  -- A tube `U × V` around `{t₀} × K` on which `f` is `C¹`.
  obtain ⟨U, V, hU, hV, ht₀U, hKV, hfU⟩ := exists_isOpen_prod_contMDiffOn
    (I' := 𝓘(ℝ).prod J) (J := 𝓘(ℝ, F)) (f := uncurry f) hK (by simp)
    fun a ha ↦ (hf a ha).of_le one_le_two
  have hfat : ∀ t ∈ U, ∀ a ∈ K, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t, a) :=
    fun t ht a ha ↦ hfU.contMDiffAt ((hU.prod hV).mem_nhds ⟨ht, hKV ha⟩)
  -- Near `t₀`, the vanishing off `K` holds near every parameter.
  have hfK' := hfK.eventually_nhds
  -- Near `t₀` the first derivative of the integral is the integral of `∂_t f`.
  have hderiv : (deriv fun t ↦ ∫ a, f t a ∂μ) =ᶠ[𝓝 t₀]
      fun t ↦ ∫ a, deriv (fun s ↦ f s a) t ∂μ := by
    filter_upwards [hU.mem_nhds ht₀U, hfK'] with t ht htK
    exact (hK.hasDerivAt_parametric_integral (J := J) hKm hμK (hfat t ht) htK).deriv
  -- The derivative `∂_t f` also vanishes off `K` near `t₀`.
  have hgK : ∀ᶠ t in 𝓝 t₀, ∀ a ∉ K, deriv (fun s ↦ f s a) t = 0 := by
    filter_upwards [hfK'] with t htK a ha
    have hev : (fun s ↦ f s a) =ᶠ[𝓝 t] fun _ ↦ (0 : F) := htK.mono fun s hs ↦ hs a ha
    rw [hev.deriv_eq, deriv_const]
  refine (hK.hasDerivAt_parametric_integral (J := J) hKm hμK
    (f := fun t a ↦ deriv (fun s ↦ f s a) t) (fun a ha ↦ ?_) hgK).congr_of_eventuallyEq hderiv
  exact (hf a ha).deriv_uncurry (by norm_num)

end CompactSupport

section Slice

variable [CompactSpace N] [IsFiniteMeasure μ]

/-- **Differentiation under the integral sign over a compact manifold.** If `(z, a) ↦ g z a` is
`C^1` at every point `(z₀, a)`, for a parameter `z` in a normed space, then the derivative of
`z ↦ ∫ a, g z a ∂μ` at `z₀` is the integral of the derivatives of the functions `z ↦ g z a`. -/
theorem hasFDerivAt_integral_of_contMDiffAt {g : E' → N → F} {z₀ : E'}
    (hg : ∀ a, ContMDiffAt (𝓘(ℝ, E').prod J) 𝓘(ℝ, F) 1 (uncurry g) (z₀, a)) :
    HasFDerivAt (fun z ↦ ∫ a, g z a ∂μ) (∫ a, fderiv ℝ (fun z ↦ g z a) z₀ ∂μ) z₀ :=
  isCompact_univ.hasFDerivAt_integral_of_contMDiffAt MeasurableSet.univ (measure_ne_top μ univ)
    (fun a _ ↦ hg a) (by simp)

variable {f : ℝ → N → F} {t₀ : ℝ}

/-- **Differentiation under the integral sign over a compact manifold.** If `(t, a) ↦ f t a` is
`C^1` at every point `(t₀, a)`, then `t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at
`t₀`. -/
theorem hasDerivAt_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a)) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ :=
  isCompact_univ.hasDerivAt_parametric_integral MeasurableSet.univ (measure_ne_top μ univ)
    (fun a _ ↦ hf a) (by simp)

/-- **The second derivative of an integral over a compact manifold.** If `(t, a) ↦ f t a` is
`C^2` at every point `(t₀, a)`, then the derivative of `t ↦ ∫ a, f t a ∂μ` has derivative
`∫ a, ∂_t² f t₀ a ∂μ` at `t₀`. -/
theorem hasDerivAt_deriv_parametric_integral
    (hf : ∀ a, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 2 (uncurry f) (t₀, a)) :
    HasDerivAt (deriv fun t ↦ ∫ a, f t a ∂μ)
      (∫ a, deriv (fun s ↦ deriv (fun r ↦ f r a) s) t₀ ∂μ) t₀ :=
  isCompact_univ.hasDerivAt_deriv_parametric_integral MeasurableSet.univ (measure_ne_top μ univ)
    (fun a _ ↦ hf a) (by simp)

end Slice

end TauCeti
