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
# Identity theorem on a right half-plane

Holomorphic functions on `Re s > a` that agree on a smaller right half-plane `Re s > b`,
where `a < b`, agree throughout `Re s > a`.
-/

public section

namespace TauCeti

open Filter Topology

/-- Two functions holomorphic on `Re s > a` that agree on `Re s > b`, for `a < b`,
agree throughout `Re s > a`. -/
theorem eq_of_differentiableOn_of_eq_on_halfPlane {f g : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : DifferentiableOn ℂ f {s | a < s.re})
    (hg : DifferentiableOn ℂ g {s | a < s.re})
    (hfg : ∀ s : ℂ, b < s.re → f s = g s) {s : ℂ}
    (hs : a < s.re) : f s = g s := by
  have hUopen : IsOpen {s : ℂ | a < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUopen)
    (convex_halfSpace_re_gt a).isPreconnected (z₀ := ((b + 1 : ℝ) : ℂ)) ?_ ?_ hs
  · change a < ((b + 1 : ℝ) : ℂ).re
    simp only [Complex.ofReal_re]
    linarith
  · have hb : b < ((b + 1 : ℝ) : ℂ).re := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hb] with z hz
    exact hfg z hz

end TauCeti
