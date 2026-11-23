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

Locally: if `f` is analytic at `z₀` and `z₀` is an isolated solution of `f z = f z₀`, then every
small enough closed ball about `z₀` is a disc on which `f` is analytic, `z₀` is the only solution
of `f z = f z₀`, and `z₀` is the only possible critical point
(`AnalyticAt.eventually_analyticOnNhd_closedBall_and_ne_and_deriv_ne_zero`).
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

namespace AnalyticAt

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : 𝕜 → F} {z₀ : 𝕜}

/-- **Small balls about an isolated point of a fibre.** If `f` is analytic at `z₀` and `z₀` is an
isolated solution of `f z = f z₀`, then for every small enough radius `r > 0`, `f` is analytic on
`closedBall z₀ r`, `z₀` is the only solution of `f z = f z₀` there, and `f'` vanishes nowhere on
`ball z₀ r` except possibly at `z₀`. For `𝕜 = ℂ` these are the hypotheses of the local degree
count `TauCeti.localDegree_card`. -/
theorem eventually_analyticOnNhd_closedBall_and_ne_and_deriv_ne_zero (hf : AnalyticAt 𝕜 f z₀)
    (hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ f z₀) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), AnalyticOnNhd 𝕜 f (closedBall z₀ r) ∧
      (∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀) ∧
      (∀ z ∈ ball z₀ r, z ≠ z₀ → deriv f z ≠ 0) := by
  -- `f` is analytic on a ball about `z₀` and not constant there, so `z₀` is an isolated critical
  -- point at most.
  obtain ⟨ε, hε, hA⟩ := eventually_nhds_iff_ball.1 hf.eventually_analyticAt
  have hderiv : ∀ᶠ z in 𝓝[≠] z₀, deriv f z ≠ 0 :=
    AnalyticOnNhd.eventually_deriv_ne_zero_of_not_eqOn_const hA (convex_ball z₀ ε).isPreconnected
      (fun ⟨c, hc⟩ ↦ by
        obtain ⟨z, hz, hzb⟩ :=
          (hne.and (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hε))).exists
        exact hz ((hc hzb).trans (hc (mem_ball_self hε)).symm))
      (mem_ball_self hε)
  have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt 𝕜 f z ∧ (z ≠ z₀ → f z ≠ f z₀) ∧
      (z ≠ z₀ → deriv f z ≠ 0) := by
    filter_upwards [hf.eventually_analyticAt, eventually_nhdsWithin_iff.mp hne,
      eventually_nhdsWithin_iff.mp hderiv] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [(eventually_closedBall_subset hall).filter_mono nhdsWithin_le_nhds] with r hr
  exact ⟨fun z hz ↦ (hr hz).1, fun z hz ↦ (hr hz).2.1,
    fun z hz ↦ (hr (ball_subset_closedBall hz)).2.2⟩

end AnalyticAt

end
