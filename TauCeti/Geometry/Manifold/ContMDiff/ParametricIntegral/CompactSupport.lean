/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv

/-!
# Differentiation under the integral sign with compact support in the parameter

Let `f t a` depend on a real parameter `t` and a point `a` of a manifold `N`, which need not be
compact, and suppose that for `t` near `t₀` the function `f t` vanishes outside one compact set
`K` of finite measure. If `(t, a) ↦ f t a` is `C¹` at the points `(t₀, a)` with `a ∈ K`, then
`t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at `t₀`
(`IsCompact.hasDerivAt_parametric_integral`), and similarly for the second derivative when the
function is `C²` (`IsCompact.hasDerivAt_deriv_parametric_integral`). This extends
`TauCeti.hasDerivAt_parametric_integral` and `TauCeti.hasDerivAt_deriv_parametric_integral`,
stated over a compact manifold, to variations with
fixed compact support, as in the first variation of the volume of a noncompact submanifold.
-/

public section

open Filter MeasureTheory Set Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 1 N] [T2Space N]
  [MeasurableSpace N] [OpensMeasurableSpace N] {μ : Measure N}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [T2Space N] [MeasurableSpace N] [OpensMeasurableSpace N] in
/-- The derivative in the parameter of a function on `ℝ × N` that is `C¹` on `U × V`, for open
`U` and `V`, is jointly continuous on `U × V`. -/
private theorem continuousOn_fderiv_of_contMDiffOn_prod {f : ℝ → N → F} {U : Set ℝ}
    {V : Set N} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (U ×ˢ V)) :
    ContinuousOn (fun p : ℝ × N ↦ fderiv ℝ (fun t ↦ f t p.2) p.1) (U ×ˢ V) := by
  intro p hp
  have hf' : ContMDiffAt (J.prod 𝓘(ℝ)) 𝓘(ℝ, F) 1 (uncurry fun (a : N) (t : ℝ) ↦ f t a)
      p.swap :=
    (hf.contMDiffAt ((hU.prod hV).mem_nhds hp)).comp p.swap
      (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hf'.fderiv_right (n := 0) (by norm_num)).continuousAt.comp
    continuous_swap.continuousAt
  exact h.continuousWithinAt

/-- **Differentiation under the integral sign with compact support in the parameter.** Let `K` be
a compact set of finite measure such that, for `t` near `t₀`, the function `f t` vanishes outside
`K`. If `(t, a) ↦ f t a` is `C¹` at every point `(t₀, a)` with `a ∈ K`, then
`t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t f t₀ a ∂μ` at `t₀`. -/
theorem _root_.IsCompact.hasDerivAt_parametric_integral {f : ℝ → N → F} {t₀ : ℝ} {K : Set N}
    (hK : IsCompact K) (hμK : μ K ≠ ⊤)
    (hf : ∀ a ∈ K, ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ, F) 1 (uncurry f) (t₀, a))
    (hfK : ∀ᶠ t in 𝓝 t₀, ∀ a ∉ K, f t a = 0) :
    HasDerivAt (fun t ↦ ∫ a, f t a ∂μ) (∫ a, deriv (fun s ↦ f s a) t₀ ∂μ) t₀ := by
  -- A tube `U × V` around `{t₀} × K` on which `f` is `C¹`.
  obtain ⟨U, V, hU, hV, ht₀U, hKV, hfU⟩ := exists_isOpen_prod_contMDiffOn
    (I' := 𝓘(ℝ).prod J) (J := 𝓘(ℝ, F)) (f := uncurry f) hK (by simp) hf
  have hdiff (a : N) (ha : a ∈ K) : DifferentiableOn ℝ (fun t ↦ f t a) U := by
    have h : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, F) 1 (fun t ↦ f t a) U :=
      hfU.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun t ht ↦ ⟨ht, hKV ha⟩
    exact (contMDiffOn_iff_contDiffOn.1 h).differentiableOn one_ne_zero
  have hset := hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) (𝕜 := ℝ)
    (hU.mem_nhds ht₀U) hK hK.measurableSet hμK subset_rfl
    (hfU.continuousOn.mono (prod_mono subset_rfl hKV)) hdiff
    ((continuousOn_fderiv_of_contMDiffOn_prod hU hV hfU).mono (prod_mono subset_rfl hKV))
  -- Off `K` the derivative vanishes, since `f t a = 0` for `t` near `t₀`.
  have hzero (a : N) (ha : a ∉ K) : fderiv ℝ (fun t ↦ f t a) t₀ = 0 := by
    have hev : (fun t ↦ f t a) =ᶠ[𝓝 t₀] fun _ ↦ (0 : F) := hfK.mono fun t ht ↦ ht a ha
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hint : (fun t ↦ ∫ a in K, f t a ∂μ) =ᶠ[𝓝 t₀] fun t ↦ ∫ a, f t a ∂μ :=
    hfK.mono fun t ht ↦ setIntegral_eq_integral_of_forall_compl_eq_zero ht
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hset
  have hfd := (hset.congr_of_eventuallyEq hint.symm).hasDerivAt
  -- Evaluating the integrated derivative at `1` commutes with the integral.
  have e := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).symm.integral_comp_comm
    (μ := μ) (fun a ↦ fderiv ℝ (fun s ↦ f s a) t₀)
  simp only [ContinuousLinearMap.toSpanSingletonCLE_symm_apply, fderiv_apply_one_eq_deriv] at e
  rw [e]
  exact hfd


/-- **The second derivative of an integral with compact support in the parameter.** Let `K` be a
compact set of finite measure such that, for `t` near `t₀`, the function `f t` vanishes outside
`K`. If `(t, a) ↦ f t a` is `C²` at every point `(t₀, a)` with `a ∈ K`, then the derivative of
`t ↦ ∫ a, f t a ∂μ` has derivative `∫ a, ∂_t² f t₀ a ∂μ` at `t₀`. -/
theorem _root_.IsCompact.hasDerivAt_deriv_parametric_integral {f : ℝ → N → F} {t₀ : ℝ}
    {K : Set N} (hK : IsCompact K) (hμK : μ K ≠ ⊤)
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
    exact (hK.hasDerivAt_parametric_integral (J := J) hμK (hfat t ht) htK).deriv
  -- The derivative `∂_t f` also vanishes off `K` near `t₀`.
  have hgK : ∀ᶠ t in 𝓝 t₀, ∀ a ∉ K, deriv (fun s ↦ f s a) t = 0 := by
    filter_upwards [hfK'] with t htK a ha
    have hev : (fun s ↦ f s a) =ᶠ[𝓝 t] fun _ ↦ (0 : F) := htK.mono fun s hs ↦ hs a ha
    rw [hev.deriv_eq, deriv_const]
  refine (hK.hasDerivAt_parametric_integral (J := J) hμK (f := fun t a ↦ deriv (fun s ↦ f s a) t)
    (fun a ha ↦ ?_) hgK).congr_of_eventuallyEq hderiv
  exact (hf a ha).deriv_uncurry (by norm_num)

end TauCeti
