/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Uniform distance from an avoided point to a continuous curve

For a curve `γ : ℝ → ℂ` continuous on a compact interval `[a, b]` and avoiding a point `w`, the
image `γ '' [a, b]` is compact and misses `w`, so `w` stays a positive distance from it; this gives
a uniform positive lower bound `ρ` on `‖γ t - w‖` over `[a, b]`.

## Main results

* `TauCeti.Contour.exists_curve_dist_lower_bound` — the uniform positive distance lower bound.
* `TauCeti.Contour.exists_ball_dist_curve_lower_bound` — the same lower bound made uniform over a
  whole ball of points around the avoided point.

These small support lemmas are shared by the argument-lift partition
(`exists_uniform_modulus_avoiding`, feeding the integer-valuedness of the winding number) and by the
continuity of the winding number in the point (`continuousAt_windingNumber_of_avoidance`) — both
prerequisites for the homology form of Cauchy's theorem (roadmap `homologyCauchyTheorem`).
-/

public section

open Set

namespace TauCeti.Contour

/-- **Uniform positive distance from an avoided point to a curve.** If `γ` is continuous on the
interval with endpoints `a`, `b` and avoids `w` there, then there is `ρ > 0` with `ρ ≤ ‖γ t - w‖`
for every `t ∈ Set.uIcc a b` (one may take `ρ = Metric.infDist w (γ '' Set.uIcc a b)`). Stated on
the oriented interval `Set.uIcc a b`, matching the winding-number API. -/
theorem exists_curve_dist_lower_bound {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ ρ > 0, ∀ t ∈ uIcc a b, ρ ≤ ‖γ t - w‖ := by
  have h_image_compact : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ
  have h_image_nonempty : (γ '' uIcc a b).Nonempty := ⟨γ a, mem_image_of_mem _ left_mem_uIcc⟩
  have h_w_not_mem : w ∉ γ '' uIcc a b := fun ⟨t, ht, heq⟩ ↦ h_avoid t ht heq
  refine ⟨Metric.infDist w (γ '' uIcc a b),
    (h_image_compact.isClosed.notMem_iff_infDist_pos h_image_nonempty).mp h_w_not_mem,
    fun t ht ↦ ?_⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := w) (mem_image_of_mem γ ht)
  rwa [Complex.dist_eq, norm_sub_rev] at h1

/-- **Uniform distance to the curve on a neighbourhood of an avoided point.** If `γ` is continuous
on the interval with endpoints `a`, `b` and avoids `w₀` there, then there is a radius `ε > 0` such
that every `w` within `ε` of `w₀` stays at distance at least `ε` from the whole curve: for all
`t ∈ Set.uIcc a b`, `ε ≤ ‖γ t - w‖`. Stated on the oriented interval `Set.uIcc a b`. -/
theorem exists_ball_dist_curve_lower_bound {γ : ℝ → ℂ} {w₀ : ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ uIcc a b, ε ≤ ‖γ t - w‖ := by
  obtain ⟨ρ, hρ_pos, h_dist_lb⟩ := exists_curve_dist_lower_bound hγ h_avoid
  refine ⟨ρ / 2, half_pos hρ_pos, fun w hw t ht ↦ ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq] at hw
  have htri : ‖γ t - w₀‖ - ‖w - w₀‖ ≤ ‖γ t - w‖ := by
    have h := norm_sub_norm_le (γ t - w₀) (w - w₀)
    rwa [sub_sub_sub_cancel_right] at h
  linarith [h_dist_lb t ht]

end TauCeti.Contour
