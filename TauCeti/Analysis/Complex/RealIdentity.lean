/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Holomorphic functions and their values on the real line

Two holomorphic functions on a preconnected open set `Ω` meeting the real axis—in particular two
entire functions—with values in a complex normed space that agree frequently in a punctured real
neighborhood of a real point `t₀ ∈ Ω`—in particular on an open real ray `(a, ∞)` or on the whole
real line—are equal (`DifferentiableOn.eqOn_of_frequently_ofReal_eq`,
`Differentiable.eq_of_frequently_ofReal_eq`, `Differentiable.eq_of_ofReal_gt_eq`,
`Differentiable.eq_of_ofReal_eq`). Likewise, a holomorphic function on `Ω` vanishing on `Ω ∩ ℝ`
vanishes identically on `Ω` (`DifferentiableOn.eqOn_zero_of_zero_on_real_axis`). This is the
identity principle `AnalyticOnNhd.eq_of_frequently_eq`, applied at an accumulation point on the real
axis. It is the uniqueness statement behind analytic continuation of real one-parameter orbits to
complex time. On the complex slit plane, agreement on the positive real axis likewise determines a
holomorphic function uniquely (`AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq`), and on the
reflected slit plane `{z : ℂ | -z ∈ Complex.slitPlane}`, agreement on the cut unit ball
`{z : ℂ | ‖z‖ < 1 ∧ -z ∈ Complex.slitPlane}` determines a holomorphic function uniquely
(`AnalyticOnNhd.eqOn_neg_slitPlane_of_eqOn_cut_ball`).

At a real point, the order of vanishing of a holomorphic function equals the order of vanishing
of its restriction to the real line (`AnalyticAt.analyticOrderAt_comp_ofReal`). This lets the
order of a real analytic function be read off any holomorphic extension of it.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Two holomorphic functions on a preconnected open set `Ω` meeting the real axis at `t₀` that
agree frequently in a punctured real neighborhood of `t₀` agree throughout `Ω`. -/
theorem DifferentiableOn.eqOn_of_frequently_ofReal_eq {f g : ℂ → E} {Ω : Set ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) {t₀ : ℝ} (ht₀ : (t₀ : ℂ) ∈ Ω)
    (h : ∃ᶠ t : ℝ in 𝓝[≠] t₀, f t = g t) : Set.EqOn f g Ω := by
  -- `DifferentiableOn.analyticOnNhd` needs a complete codomain, so work in the completion of `E`
  let ι : E →ₗᵢ[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  -- real points other than `t₀` accumulate at `t₀` in `ℂ`
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] t₀) (𝓝[≠] (t₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ ht =>
      Complex.ofReal_inj.not.mpr ht
  have hιfg : Set.EqOn (ι ∘ f) (ι ∘ g) Ω :=
    ((ι.toContinuousLinearMap.differentiable.comp_differentiableOn hf).analyticOnNhd
      hΩopen).eqOn_of_preconnected_of_frequently_eq
      ((ι.toContinuousLinearMap.differentiable.comp_differentiableOn hg).analyticOnNhd hΩopen)
      hΩconn ht₀ (hreal.frequently (h.mono fun _ ht => congrArg ι ht))
  exact fun z hz => ι.injective (hιfg hz)

/-- A holomorphic function on a preconnected open set `Ω` meeting the real axis at `t₀` that
vanishes on `Ω ∩ ℝ` vanishes identically on `Ω`. -/
theorem DifferentiableOn.eqOn_zero_of_zero_on_real_axis {f : ℂ → E} {Ω : Set ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    {t₀ : ℝ} (ht₀ : (t₀ : ℂ) ∈ Ω) (hzero : ∀ z ∈ Ω, z.im = 0 → f z = 0) :
    Set.EqOn f 0 Ω := by
  refine hf.eqOn_of_frequently_ofReal_eq (differentiableOn_const 0) hΩopen hΩconn ht₀ ?_
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] t₀, f t = 0 := by
    filter_upwards [nhdsWithin_le_nhds <| Complex.continuous_ofReal.continuousAt.preimage_mem_nhds
      (hΩopen.mem_nhds ht₀)] with t ht
    exact hzero _ ht (Complex.ofReal_im t)
  exact hev.frequently

/-- Two entire functions agreeing frequently in a punctured real neighborhood of a real point `t₀`
are equal. -/
theorem Differentiable.eq_of_frequently_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {t₀ : ℝ} (h : ∃ᶠ t : ℝ in 𝓝[≠] t₀, f t = g t) : f = g :=
  funext fun z =>
    hf.differentiableOn.eqOn_of_frequently_ofReal_eq hg.differentiableOn isOpen_univ
      isPreconnected_univ (Set.mem_univ _) h (Set.mem_univ z)

/-- Two entire functions agreeing on an open real ray `(a, ∞)` are equal. -/
theorem Differentiable.eq_of_ofReal_gt_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {a : ℝ} (h : ∀ t : ℝ, a < t → f t = g t) : f = g :=
  hf.eq_of_frequently_ofReal_eq hg (t₀ := a + 1)
    (eventually_nhdsWithin_of_eventually_nhds ((lt_mem_nhds (lt_add_one a)).mono h)).frequently

/-- Two entire functions agreeing on the real line are equal. -/
theorem Differentiable.eq_of_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ t : ℝ, f t = g t) : f = g :=
  hf.eq_of_ofReal_gt_eq hg (a := 0) fun t _ => h t

/-- Two holomorphic functions on the slit plane agreeing on the positive real axis agree
throughout the slit plane. -/
theorem AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq {f g : ℂ → E}
    (hf : AnalyticOnNhd ℂ f Complex.slitPlane) (hg : AnalyticOnNhd ℂ g Complex.slitPlane)
    (h : ∀ t : ℝ, 0 < t → f t = g t) : Set.EqOn f g Complex.slitPlane := by
  have hpre := (Complex.starConvex_one_slitPlane.isPathConnected
    Complex.one_mem_slitPlane).isConnected.isPreconnected
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hpre Complex.one_mem_slitPlane ?_
  -- real points near `1` are positive, and those other than `1` accumulate at `1` in `ℂ`
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    simpa using Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (x := 1)
      fun _ _ ↦ by simp_all
  exact hreal.frequently (eventually_nhdsWithin_of_eventually_nhds
    ((lt_mem_nhds one_pos).mono h)).frequently

/-- Two holomorphic functions on the reflected slit plane `{z : ℂ | -z ∈ Complex.slitPlane}`
that agree on the cut unit ball `{z : ℂ | ‖z‖ < 1 ∧ -z ∈ Complex.slitPlane}` agree throughout
`{z : ℂ | -z ∈ Complex.slitPlane}`. -/
theorem AnalyticOnNhd.eqOn_neg_slitPlane_of_eqOn_cut_ball {f g : ℂ → E}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | -z ∈ Complex.slitPlane})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | -z ∈ Complex.slitPlane})
    (hEq : Set.EqOn f g {z : ℂ | ‖z‖ < 1 ∧ -z ∈ Complex.slitPlane}) :
    Set.EqOn f g {z : ℂ | -z ∈ Complex.slitPlane} := by
  have hpre_slit : IsPreconnected Complex.slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected
      Complex.one_mem_slitPlane).isConnected.isPreconnected
  have himg : Neg.neg '' Complex.slitPlane = {z : ℂ | -z ∈ Complex.slitPlane} := by
    ext z; simp
  have hpre : IsPreconnected {z : ℂ | -z ∈ Complex.slitPlane} :=
    himg ▸ hpre_slit.image _ continuous_neg.continuousOn
  have hopen : IsOpen {z : ℂ | ‖z‖ < 1 ∧ -z ∈ Complex.slitPlane} :=
    (isOpen_lt continuous_norm continuous_const).inter
      (Complex.isOpen_slitPlane.preimage continuous_neg)
  have hz₀ : (-1 / 2 : ℂ) ∈ {z : ℂ | ‖z‖ < 1 ∧ -z ∈ Complex.slitPlane} := by
    refine ⟨by norm_num, ?_⟩
    rw [neg_div, neg_neg]
    simpa using Complex.ofReal_mem_slitPlane.2 (by norm_num : (0 : ℝ) < 1 / 2)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpre hz₀.2
    (Filter.eventually_of_mem (hopen.mem_nhds hz₀) hEq)

/-- At a real point `t`, a holomorphic function `f` and its restriction `s ↦ f s` to the real line
vanish to the same order. -/
theorem AnalyticAt.analyticOrderAt_comp_ofReal {f : ℂ → E} {t : ℝ} (hf : AnalyticAt ℂ f t) :
    analyticOrderAt (fun s : ℝ => f s) t = analyticOrderAt f t := by
  have hT : Tendsto ((↑) : ℝ → ℂ) (𝓝 t) (𝓝 t) := Complex.continuous_ofReal.tendsto t
  by_cases htop : analyticOrderAt f t = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    exact hT.eventually (analyticOrderAt_eq_top.1 htop)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.1 hn.symm
  have hr : AnalyticAt ℝ (fun s : ℝ => f s) t :=
    (hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  rw [← hn, hr.analyticOrderAt_eq_natCast]
  refine ⟨fun s : ℝ => g s, (hg.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t),
    hg0, ?_⟩
  filter_upwards [hT.eventually hfg] with s hs
  rw [hs, ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.coe_smul]
