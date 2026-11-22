/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Convex

/-!
# Holomorphic functions and their values on the real line

Two entire functions with values in a complex normed space that agree frequently in a punctured
real neighborhood of a real point—in particular on an open real ray `(a, ∞)` or on the whole real
line—are equal (`Differentiable.eq_of_frequently_ofReal_eq`, `Differentiable.eq_of_ofReal_gt_eq`,
`Differentiable.eq_of_ofReal_eq`). This is the identity principle
`AnalyticOnNhd.eq_of_frequently_eq`, applied at an accumulation point on the real axis. It is the
uniqueness statement behind analytic continuation of real one-parameter orbits to complex time.
On the complex slit plane, agreement on the positive real axis likewise determines a
holomorphic function uniquely.

At a real point, the order of vanishing of a holomorphic function equals the order of vanishing
of its restriction to the real line (`AnalyticAt.analyticOrderAt_comp_ofReal`). This lets the
order of a real analytic function be read off any holomorphic extension of it.

Moreover, a function holomorphic on an open subset of `ℂ` that agrees with `(g · : ℂ)` on a real
subset (or open real set) restricts to a `C^∞` real function whose real iterated derivatives coerce
to the complex iterated derivatives of the holomorphic extension
(`DifferentiableOn.contDiffOn_ofReal`, `DifferentiableOn.iteratedDeriv_ofReal`).
-/

public section

open Filter Topology
open scoped ContDiff

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

/-- A function holomorphic on an open set `U ⊆ ℂ` that agrees with `(g · : ℂ)` on a real subset
`s` with `(↑) '' s ⊆ U` restricts to a `C^n` real function `g` on `s`. -/
theorem DifferentiableOn.contDiffOn_ofReal {f : ℂ → ℂ} {g : ℝ → ℝ} {U : Set ℂ} {s : Set ℝ}
    {n : WithTop ℕ∞} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hmaps : Set.MapsTo ((↑) : ℝ → ℂ) s U) (hfg : ∀ x ∈ s, f (x : ℂ) = (g x : ℂ)) :
    ContDiffOn ℝ n g s := by
  have hf_cd : ContDiffOn ℝ n f U := (hf.contDiffOn hU).restrict_scalars ℝ
  have hcomp : ContDiffOn ℝ n (fun x : ℝ ↦ Complex.reCLM (f (Complex.ofRealCLM x))) s :=
    Complex.reCLM.contDiff.contDiffOn.comp
      (hf_cd.comp Complex.ofRealCLM.contDiff.contDiffOn hmaps) (Set.mapsTo_univ _ _)
  exact hcomp.congr fun x hx ↦ by
    simp only [Complex.reCLM_apply, Complex.ofRealCLM_apply, hfg x hx, Complex.ofReal_re]

/-- If `f : ℂ → ℂ` is holomorphic on an open set `U ⊆ ℂ` and agrees with `(g · : ℂ)` on an open
real set `s` mapped into `U`, then every complex iterated derivative of `f` on `s` is the coercion
of the real iterated derivative of `g`. -/
theorem DifferentiableOn.iteratedDeriv_ofReal {f : ℂ → ℂ} {g : ℝ → ℝ} {U : Set ℂ} {s : Set ℝ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hs : IsOpen s)
    (hmaps : Set.MapsTo ((↑) : ℝ → ℂ) s U) (hfg : ∀ x ∈ s, f (x : ℂ) = (g x : ℂ))
    (k : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv k f (x : ℂ) = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  have hdiff : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m f) U := by
    intro m
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  induction k generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using hfg x hx
  | succ k ih =>
    have hfk : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f (x : ℂ)) (x : ℂ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff k).differentiableAt (hU.mem_nhds (hmaps hx))).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ ↦ ((iteratedDeriv k g t : ℝ) : ℂ))
        (iteratedDeriv (k + 1) f (x : ℂ)) x := by
      refine hfk.comp_ofReal.congr_of_eventuallyEq ?_
      filter_upwards [hs.mem_nhds hx] with t ht
      exact (ih ht).symm
    have hre : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) f (x : ℂ)).re x := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    have him : HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) (iteratedDeriv (k + 1) f (x : ℂ)).im x := by
      simpa only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] using
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    have hre_eq : iteratedDeriv (k + 1) g x = (iteratedDeriv (k + 1) f (x : ℂ)).re := by
      rw [iteratedDeriv_succ, hre.deriv]
    have him_eq : (iteratedDeriv (k + 1) f (x : ℂ)).im = 0 :=
      him.unique (hasDerivAt_const x (0 : ℝ))
    exact Complex.ext (by simp [hre_eq]) (by simp [him_eq])
