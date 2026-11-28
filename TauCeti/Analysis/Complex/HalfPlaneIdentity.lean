/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Identity theorem on a right half-plane

Functions holomorphic on the right half-plane `Re s > a` that agree on some right half-plane
`Re s > b` agree throughout `Re s > a`. Likewise, two functions holomorphic on a punctured
neighbourhood of `a` that agree on the `Re z > a.re` side of a neighbourhood of `a` agree on a
punctured neighbourhood of `a`. The codomain is any complete complex normed space.
-/

public section

open Filter Set
open scoped Topology

/-- **Identity theorem on a right half-plane.** Two functions holomorphic on `Re s > a` that
agree on some right half-plane `Re s > b` agree throughout `Re s > a`. -/
theorem DifferentiableOn.eqOn_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {a b : ℝ}
    (hf : DifferentiableOn ℂ f {s | a < s.re}) (hg : DifferentiableOn ℂ g {s | a < s.re})
    (hfg : EqOn f g {s | b < s.re}) : EqOn f g {s | a < s.re} := by
  have hopen (c : ℝ) : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd (hopen a)).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd (hopen a)) (convex_halfSpace_re_gt a).isPreconnected
    (z₀ := ((max a b + 1 : ℝ) : ℂ)) ?_ (hfg.eventuallyEq_of_mem ((hopen b).mem_nhds ?_)) <;>
    simp <;> grind

namespace TauCeti

/-- **Punctured-neighbourhood identity theorem on a right half-plane boundary.** Two functions
differentiable on a punctured neighbourhood of `a` that agree on the `Re z > a.re` side of a
neighbourhood of `a` agree on a punctured neighbourhood of `a`. -/
theorem eventuallyEq_of_differentiableAt_nhdsNE_of_eventuallyEq_re_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F H : ℂ → E} {a : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ F z)
    (hH : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ H z)
    (hFH : F =ᶠ[𝓝[{z : ℂ | a.re < z.re}] a] H) :
    F =ᶠ[𝓝[≠] a] H := by
  obtain ⟨r₁, hr₁, hFr₁⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hF)
  obtain ⟨r₂, hr₂, hHr₂⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hH)
  obtain ⟨r₃, hr₃, hFHr₃⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hFH)
  set r : ℝ := min r₁ (min r₂ r₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  set V : Set ℂ := Metric.ball a r \ {a}
  have hVopen : IsOpen V := Metric.isOpen_ball.sdiff isClosed_singleton
  have hFV : AnalyticOnNhd ℂ F V := DifferentiableOn.analyticOnNhd
    (fun s hs ↦ (hFr₁ ((Metric.mem_ball.mp hs.1).trans_le (min_le_left _ _)) hs.2
      ).differentiableWithinAt) hVopen
  have hHV : AnalyticOnNhd ℂ H V := DifferentiableOn.analyticOnNhd
    (fun s hs ↦ (hHr₂ ((Metric.mem_ball.mp hs.1).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))) hs.2
      ).differentiableWithinAt) hVopen
  have hVconn : IsPreconnected V :=
    (TauCeti.isConnected_ball_sdiff_singleton (by rw [Complex.rank_real_complex]; norm_num)
      a hr).isPreconnected
  set z₀ : ℂ := a + ((r / 2 : ℝ) : ℂ)
  have hz₀_ball : dist z₀ a < r := by
    rw [Complex.dist_eq]
    simpa [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using half_lt_self hr
  have hz₀V : z₀ ∈ V :=
    ⟨Metric.mem_ball.mpr hz₀_ball,
      fun h ↦ by have := congrArg Complex.re h; simp [z₀] at this; linarith⟩
  have hnhds : Metric.ball a r₃ ∩ {z : ℂ | a.re < z.re} ∈ 𝓝 z₀ :=
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds
      ⟨Metric.mem_ball.mpr (hz₀_ball.trans_le ((min_le_right _ _).trans (min_le_right _ _))),
        by simp [z₀, half_pos hr]⟩
  have hEqV : Set.EqOn F H V :=
    hFV.eqOn_of_preconnected_of_eventuallyEq hHV hVconn hz₀V
      (Filter.eventuallyEq_of_mem hnhds fun s hs ↦ hFHr₃ (Metric.mem_ball.mp hs.1) hs.2)
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds a hr)] with s hs
  exact hEqV ⟨hs.2, hs.1⟩

end TauCeti
