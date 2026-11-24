/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.BumpFunction.Basic

/-!
# Bump functions localized along a path

Let `γ : ℝ → E` be a continuous path in a finite-dimensional real normed space that passes
through the point `γ s₀` only once, in the sense that `γ s → γ s₀` forces `s → s₀`. A smooth bump
function `ψ` at `γ s₀` with small enough support then meets `γ` only at times close to `s₀`. So for
a continuous weight `q` with `q s₀ > 0`, the integral of `ψ (γ s) * q s` is positive
(`TauCeti.exists_contDiff_tsupport_subset_integral_comp_mul_pos`).

This is the localization step in the proofs that the cokernel of a linearized trajectory operator
is killed by variations of the equation supported near one point of the trajectory: a variation
`ψ • e` pairs with a path `w` as `∫ s, ψ (γ s) * ⟪e, w s⟫`.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace TauCeti

/-- **A bump function along a once-visited point of a path.** Let `γ` be a continuous path passing
through `γ s₀` only once, in the sense that `γ s → γ s₀` forces `s → s₀`, let `U` be a
neighbourhood of `γ s₀`, and let `q` be a continuous weight with `q s₀ > 0`. Some smooth compactly
supported function `ψ` with support in `U` meets `γ` in a compact set of times and integrates
positively against `q` along `γ`. It is a bump function at `γ s₀` so small that `γ` meets it only
at times where `q > 0`. -/
theorem exists_contDiff_tsupport_subset_integral_comp_mul_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {γ : ℝ → E} (hγ : Continuous γ) {s₀ : ℝ}
    (hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀) {U : Set E} (hU : U ∈ 𝓝 (γ s₀)) {q : ℝ → ℝ}
    (hq : Continuous q) (hq₀ : 0 < q s₀) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      HasCompactSupport (fun s ↦ ψ (γ s)) ∧ 0 < ∫ s, ψ (γ s) * q s := by
  obtain ⟨δ, hδ, hqδ⟩ := eventually_nhds_iff_ball.1 (hq.continuousAt.eventually (lt_mem_nhds hq₀))
  -- A small ball around `γ s₀` inside `U` meets `γ` only at times within `δ` of `s₀`.
  obtain ⟨V, hV, hVδ⟩ := mem_comap.1 (hvisit (ball_mem_nhds s₀ hδ))
  obtain ⟨r, hr, hrUV⟩ := Metric.mem_nhds_iff.1 (inter_mem hU hV)
  obtain ⟨ψ, hψr⟩ := exists_contDiffBump_tsupport_subset_ball (γ s₀) hr
  have hψγ {s : ℝ} (hs : ψ (γ s) ≠ 0) : s ∈ ball s₀ δ :=
    hVδ (hrUV (hψr (subset_tsupport _ (Function.mem_support.2 hs)))).2
  have hψsupp : HasCompactSupport fun s ↦ ψ (γ s) :=
    HasCompactSupport.of_support_subset_isCompact (K := closedBall s₀ δ) (isCompact_closedBall s₀ δ)
      fun s hs ↦ ball_subset_closedBall (hψγ hs)
  refine ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, fun x hx ↦ (hrUV (hψr hx)).1, hψsupp, ?_⟩
  -- The integrand is nonnegative, and positive at `s₀`.
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := s₀)
    (((ψ.contDiff (n := 0)).continuous.comp hγ).mul hq)
    (hψsupp.mono fun s hs h ↦ hs (by simp [h])) (fun s ↦ ?_) ?_
  · by_cases hs : ψ (γ s) = 0
    · simp [hs]
    · exact mul_nonneg ψ.nonneg (hqδ s (hψγ hs)).le
  · rw [ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_mul]
    exact hq₀.ne'

end TauCeti
