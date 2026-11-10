/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform positivity after a boundary zero

Let `φ : E × ℝ → ℝ` be a family of real functions of a time `t`, indexed by a parameter `s` in a
real normed space. Suppose that `φ (s, a) = 0` for all `s` near `s₀`, that `φ` is `C¹` at
`(s₀, a)`, and that its partial derivative in `t` at `(s₀, a)` is positive. Then there is a common
`τ > 0` such that `φ (s, t) > 0` for all `s` near `s₀` and all `t ∈ (a, a + τ]`. The partial
derivative in `t` stays positive near `(s₀, a)` by continuity of the derivative, so each `φ (s, ·)`
is strictly increasing on `[a, a + τ]` by the mean value theorem.

For instance, if `φ (s, t)` is a defining function of a domain evaluated along a family of curves
starting on the boundary at `t = a`, this says that all the curves of the family close to the
central one enter the domain at once and stay inside on a common initial time interval.

## Main results

* `TauCeti.eventually_pos_on_initial_interval_of_partial_deriv_pos`: positivity on `(a, a + τ]`.
* `TauCeti.eventually_nonneg_on_initial_interval_of_partial_deriv_pos`: nonnegativity on
  `[a, a + τ]`.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E × ℝ → ℝ} {s₀ : E}
  {a b : ℝ}

/-- If `φ (s, a) = 0` for all `s` near `s₀`, `φ` is `C¹` at `(s₀, a)` and its partial derivative
in the second variable is positive there, then for some `τ > 0`, with `a + τ ≤ b`, the function
`φ (s, ·)` is positive on `(a, a + τ]` for all `s` near `s₀`. -/
theorem eventually_pos_on_initial_interval_of_partial_deriv_pos (hab : a < b)
    (hφ : ContDiffAt ℝ 1 φ (s₀, a)) (hpos : 0 < fderiv ℝ φ (s₀, a) (0, 1))
    (hzero : ∀ᶠ s in 𝓝 s₀, φ (s, a) = 0) :
    ∃ τ > 0, a + τ ≤ b ∧ ∀ᶠ s in 𝓝 s₀, ∀ t ∈ Ioc a (a + τ), 0 < φ (s, t) := by
  obtain ⟨A, ⟨U, hU, hD⟩, hDc⟩ := (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mp hφ
  have hD0 : A (s₀, a) = fderiv ℝ φ (s₀, a) := (hD _ (mem_of_mem_nhds hU)).fderiv.symm
  have hApos : ∀ᶠ z in 𝓝 (s₀, a), 0 < A z (0, 1) := by
    have hc : ContinuousAt (fun z ↦ A z (0, 1)) (s₀, a) :=
      hDc.continuousAt.clm_apply continuousAt_const
    refine hc.eventually (lt_mem_nhds ?_)
    simpa only [hD0] using hpos
  obtain ⟨δ, hδ, hδU⟩ :=
    Metric.eventually_nhds_iff_ball.mp ((eventually_mem_set.mpr hU).and hApos)
  let τ := min (δ / 2) ((b - a) / 2)
  have hτ : 0 < τ := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hab))
  have hτb : a + τ ≤ b := by linarith [min_le_right (δ / 2) ((b - a) / 2)]
  have hlocal : ∀ s ∈ Metric.ball s₀ (δ / 2), ∀ t ∈ Icc a (a + τ),
      HasDerivAt (fun t ↦ φ (s, t)) (A (s, t) (0, 1)) t ∧ 0 < A (s, t) (0, 1) := by
    intro s hs t ht
    have hnear : dist (s, t) (s₀, a) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact ⟨(Metric.mem_ball.mp hs).trans (half_lt_self hδ),
        by linarith [ht.2, min_le_left (δ / 2) ((b - a) / 2)]⟩
    have hgood := hδU _ hnear
    have hline : HasDerivAt (fun t : ℝ ↦ (s, t)) ((0 : E), (1 : ℝ)) t :=
      (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
    exact ⟨(hD _ hgood.1).comp_hasDerivAt t hline, hgood.2⟩
  refine ⟨τ, hτ, hτb, ?_⟩
  filter_upwards [Metric.ball_mem_nhds s₀ (half_pos hδ), hzero] with s hs hs0 t ht
  have hmono : StrictMonoOn (fun t ↦ φ (s, t)) (Icc a (a + τ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a (a + τ))
      (fun u hu ↦ (hlocal s hs u hu).1.continuousAt.continuousWithinAt) fun u hu ↦ ?_
    have hu' : u ∈ Icc a (a + τ) := interior_subset hu
    rw [(hlocal s hs u hu').1.deriv]
    exact (hlocal s hs u hu').2
  simpa only [hs0] using hmono (left_mem_Icc.mpr (by linarith)) (Ioc_subset_Icc_self ht) ht.1

/-- If `φ (s, a) = 0` for all `s` near `s₀`, `φ` is `C¹` at `(s₀, a)` and its partial derivative
in the second variable is positive there, then for some `τ > 0`, with `a + τ ≤ b`, the function
`φ (s, ·)` is nonnegative on `[a, a + τ]` for all `s` near `s₀`. -/
theorem eventually_nonneg_on_initial_interval_of_partial_deriv_pos (hab : a < b)
    (hφ : ContDiffAt ℝ 1 φ (s₀, a)) (hpos : 0 < fderiv ℝ φ (s₀, a) (0, 1))
    (hzero : ∀ᶠ s in 𝓝 s₀, φ (s, a) = 0) :
    ∃ τ > 0, a + τ ≤ b ∧ ∀ᶠ s in 𝓝 s₀, ∀ t ∈ Icc a (a + τ), 0 ≤ φ (s, t) := by
  obtain ⟨τ, hτ, hτb, hφpos⟩ :=
    eventually_pos_on_initial_interval_of_partial_deriv_pos hab hφ hpos hzero
  refine ⟨τ, hτ, hτb, ?_⟩
  filter_upwards [hφpos, hzero] with s hs hs0 t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · exact hs0.ge
  · exact (hs t ⟨hat, ht.2⟩).le

end TauCeti
