/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bounded and power-bounded elements of normed rings

In a seminormed ring the balls about zero form a neighbourhood basis of zero, so boundedness in
the sense of `TauCeti.Huber.IsBounded` can be read off from the norm. For a normed division ring
this identifies the power-bounded elements with the closed unit ball and shows that the ring is
uniform; for instance `ℚ_[p]` is uniform, and its power-bounded elements are those of `ℤ_[p]`.

## Main results

* `TauCeti.Huber.isBounded_closedBall_zero`: closed balls about zero are bounded.
* `TauCeti.Huber.isPowerBounded_iff_norm_le_one`: in a normed division ring an element is
  power-bounded exactly when its norm is at most one.
* `TauCeti.Huber.IsUniform.of_normedDivisionRing`: normed division rings are uniform.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27.
-/

public section

open Filter Topology

namespace TauCeti.Huber

/-- **Closed balls about zero are bounded** in a seminormed ring. -/
theorem isBounded_closedBall_zero {R : Type*} [SeminormedRing R] (r : ℝ) :
    IsBounded (Metric.closedBall (0 : R) r) := by
  rw [isBounded_iff]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hr : 0 < |r| + 1 := by positivity
  refine ⟨Metric.ball 0 (ε / (|r| + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨v, hv, s, hs, rfl⟩
  rw [mem_ball_zero_iff] at hv
  rw [mem_closedBall_zero_iff] at hs
  refine hεU (mem_ball_zero_iff.mpr ?_)
  calc ‖v * s‖ ≤ ‖v‖ * ‖s‖ := norm_mul_le v s
    _ ≤ ‖v‖ * (|r| + 1) := by gcongr; linarith [le_abs_self r]
    _ < ε / (|r| + 1) * (|r| + 1) := by gcongr
    _ = ε := div_mul_cancel₀ ε hr.ne'

variable {K : Type*} [NormedDivisionRing K]

/-- **In a normed division ring the power-bounded elements are the closed unit ball.** -/
theorem isPowerBounded_iff_norm_le_one {x : K} : IsPowerBounded x ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · by_contra! hlt
    have hx0 : x ≠ 0 := norm_pos_iff.mp (one_pos.trans hlt)
    obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp (isPowerBounded_iff.mp hx) (Metric.ball 0 1)
      (Metric.ball_mem_nhds 0 one_pos)
    have hinv : ‖x⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv).eventually_mem hV).exists
    have hone : x⁻¹ ^ m * x ^ m = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hx0)]
    have hmem := hVU (Set.mul_mem_mul hm ⟨m, rfl⟩)
    rw [hone, mem_ball_zero_iff, norm_one] at hmem
    exact lt_irrefl _ hmem
  · refine isPowerBounded_iff.mpr ((isBounded_closedBall_zero (R := K) 1).subset ?_)
    rintro _ ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff, norm_pow]
    exact pow_le_one₀ (norm_nonneg x) hx

/-- **Normed division rings are uniform.** -/
instance (priority := 100) IsUniform.of_normedDivisionRing : IsUniform K :=
  ⟨(isBounded_closedBall_zero (R := K) 1).subset fun _ hx ↦
    mem_closedBall_zero_iff.mpr (isPowerBounded_iff_norm_le_one.mp hx)⟩

end TauCeti.Huber
