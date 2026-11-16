/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex

/-!
# Identity theorems on right half-planes and balls meeting a right half-plane

* `DifferentiableOn.eqOn_of_eqOn_re_gt`: two functions into a complete complex normed space that
  are complex differentiable on `Re s > a` and agree on some right half-plane `Re s > b` agree
  throughout `Re s > a`.
* `AnalyticOnNhd.eqOn_ball_of_eqOn_re_gt`: two functions into any complex normed space that are
  analytic on `Metric.ball z₀ r` (`a < z₀.re + r`) and agree on `Metric.ball z₀ r ∩ {s | a < s.re}`
  agree throughout `Metric.ball z₀ r`.
-/

public section

open Set

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

/-- **Identity theorem on a ball meeting a right half-plane.** Two functions analytic on
`Metric.ball z₀ r` (`a < z₀.re + r`) that agree on `Metric.ball z₀ r ∩ {s | a < s.re}` agree
throughout `Metric.ball z₀ r`. -/
theorem AnalyticOnNhd.eqOn_ball_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℂ → E} {z₀ : ℂ} {r a : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball z₀ r)) (hg : AnalyticOnNhd ℂ g (Metric.ball z₀ r))
    (ha : a < z₀.re + r) (hfg : EqOn f g (Metric.ball z₀ r ∩ {s | a < s.re})) :
    EqOn f g (Metric.ball z₀ r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.mpr hr]
  · let t : ℝ := (max 0 (a - z₀.re) + r) / 2
    have ht0 : 0 < t := by positivity
    have htr : t < r := by
      have : max 0 (a - z₀.re) < r := max_lt hr (by linarith)
      simp only [t]
      linarith
    let w₀ : ℂ := z₀ + t
    have hw₀_ball : w₀ ∈ Metric.ball z₀ r := by
      simp [w₀, dist_eq_norm, abs_of_pos ht0, htr]
    have hw₀_re : a < w₀.re := by
      have : a - z₀.re ≤ max 0 (a - z₀.re) := le_max_right _ _
      simp only [w₀, t, Complex.add_re, Complex.ofReal_re]
      linarith
    have hopen : IsOpen (Metric.ball z₀ r ∩ {s : ℂ | a < s.re}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball z₀ r).isPreconnected hw₀_ball
      (hfg.eventuallyEq_of_mem (hopen.mem_nhds ⟨hw₀_ball, hw₀_re⟩))
