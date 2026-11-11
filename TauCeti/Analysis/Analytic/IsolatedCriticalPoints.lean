/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Critical points of analytic maps

For a map `f : 𝕜 → F` (with `𝕜 = ℝ` or `ℂ`) that is analytic on a preconnected set `U` and not
constant there, every critical point of `f` in `U` is isolated: the derivative of `f` does not
vanish on a punctured neighborhood of any point of `U`. For `𝕜 = ℂ` this is the familiar fact
about nonconstant holomorphic maps on a domain, used in the local theory of holomorphic curves.
-/

public section

open Filter Metric
open scoped Topology

namespace AnalyticOnNhd

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : 𝕜 → F} {U : Set 𝕜}

/-- **Critical points of a nonconstant analytic map are isolated.** Let `f` be analytic on a
preconnected set `U`, and suppose it is not constant there. At each `z ∈ U`, its derivative is
nonzero on a punctured neighborhood of `z`. In particular, every critical point of `f` in `U` is
isolated. -/
theorem eventually_deriv_ne_zero_of_not_eqOn_const (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (hnc : ¬ ∃ c, Set.EqOn f (fun _ : 𝕜 ↦ c) U) {z : 𝕜} (hz : z ∈ U) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  refine (hf z hz).deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦ hnc ?_
  obtain ⟨r, hr, hball⟩ :=
    eventually_nhds_iff_ball.1 (hzero.and (hf z hz).eventually_analyticAt)
  have hloc : f =ᶠ[𝓝 z] fun _ ↦ f z :=
    eventually_of_mem (ball_mem_nhds z hr) fun _ hw ↦
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
        (fun y hy ↦ (hball y hy).2.differentiableAt.differentiableWithinAt)
        (fun y hy ↦ (hball y hy).1) hw (mem_ball_self hr)
  exact ⟨f z, hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz hloc⟩

end AnalyticOnNhd

end
