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

Two entire functions with values in a complex normed space that agree frequently in a punctured
real neighborhood of a real point—in particular on an open real ray `(a, ∞)` or on the whole real
line—are equal (`Differentiable.eq_of_frequently_ofReal_eq`, `Differentiable.eq_of_ofReal_gt_eq`,
`Differentiable.eq_of_ofReal_eq`). This is the identity principle
`AnalyticOnNhd.eq_of_frequently_eq`, applied at an accumulation point on the real axis. It is the
uniqueness statement behind analytic continuation of real one-parameter orbits to complex time.
Every point of a real open interval `(a, b)` (or any neighborhood in `ℝ`) is an accumulation point
in `ℂ` of its real image (`Complex.accPt_ofReal_Ioo`, `Complex.accPt_ofReal_of_mem_nhds`). On the
complex slit plane, agreement on the positive real axis likewise determines a holomorphic function
uniquely.

At a real point, the order of vanishing of a holomorphic function equals the order of vanishing
of its restriction to the real line (`AnalyticAt.analyticOrderAt_comp_ofReal`). This lets the
order of a real analytic function be read off any holomorphic extension of it.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Two entire functions agreeing frequently in a punctured real neighborhood of a real point `t₀`
are equal. -/
theorem Differentiable.eq_of_frequently_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {t₀ : ℝ} (h : ∃ᶠ t : ℝ in 𝓝[≠] t₀, f t = g t) : f = g := by
  -- `Differentiable.analyticAt` needs a complete codomain, so work in the completion of `E`
  let ι : E →ₗᵢ[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  -- real points other than `t₀` accumulate at `t₀` in `ℂ`
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] t₀) (𝓝[≠] (t₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ ht =>
      Complex.ofReal_inj.not.mpr ht
  have hιfg : ι ∘ f = ι ∘ g := AnalyticOnNhd.eq_of_frequently_eq
    (fun z _ => (ι.toContinuousLinearMap.differentiable.comp hf).analyticAt z)
    (fun z _ => (ι.toContinuousLinearMap.differentiable.comp hg).analyticAt z)
    (hreal.frequently (h.mono fun _ ht => congrArg ι ht))
  exact ι.injective.comp_left hιfg

/-- Two entire functions agreeing on an open real ray `(a, ∞)` are equal. -/
theorem Differentiable.eq_of_ofReal_gt_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {a : ℝ} (h : ∀ t : ℝ, a < t → f t = g t) : f = g :=
  hf.eq_of_frequently_ofReal_eq hg (t₀ := a + 1)
    (eventually_nhdsWithin_of_eventually_nhds ((lt_mem_nhds (lt_add_one a)).mono h)).frequently

/-- Two entire functions agreeing on the real line are equal. -/
theorem Differentiable.eq_of_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ t : ℝ, f t = g t) : f = g :=
  hf.eq_of_ofReal_gt_eq hg (a := 0) fun t _ => h t

/-- Every point of a real set whose interior contains `t₀` (more generally, any neighborhood of `t₀`
in `ℝ`) has `(t₀ : ℂ)` as an accumulation point of its image under `Complex.ofReal`. -/
theorem Complex.accPt_ofReal_of_mem_nhds {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀) :
    AccPt (t₀ : ℂ) (𝓟 ((↑) '' s)) := by
  rw [accPt_iff_frequently_nhdsNE]
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] t₀) (𝓝[≠] (t₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ ht =>
      Complex.ofReal_inj.not.mpr ht
  exact hreal.frequently
    ((eventually_nhdsWithin_of_eventually_nhds hs).frequently.mono fun x hx => ⟨x, hx, rfl⟩)

/-- Every point of a real open interval `(a, b)` is an accumulation point in `ℂ` of the interval's
image under `Complex.ofReal`. -/
theorem Complex.accPt_ofReal_Ioo {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    AccPt (t₀ : ℂ) (𝓟 ((↑) '' Set.Ioo a b)) :=
  Complex.accPt_ofReal_of_mem_nhds (isOpen_Ioo.mem_nhds ht₀)

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
