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

Functions holomorphic on the right half-plane `Re s > a` that agree on some right half-plane
`Re s > b` agree throughout `Re s > a`. The codomain is any complete complex normed space.
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
