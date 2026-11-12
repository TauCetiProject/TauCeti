/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Order.PointSelection
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

/-!
# Controlled point selection on metric spaces

A bound on a size function on the closed ball encloses the search. The
selected point has at least the original size, stays within half the distance to a basepoint,
and has a controlled ball with a fixed size-radius product. No global bound or nonnegativity
assumption on the field is needed. For a square-root curvature field the doubling estimate
gives a factor-four curvature estimate.

Formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set

namespace Metric

/-- A field bounded above on the enclosing closed ball admits a controlled ball,
with the original distance and size-scale budgets retained. -/
theorem exists_doubling_controlled_point_of_bddAbove
    {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (p x : X)
    (hbound : BddAbove (f '' Metric.closedBall x (dist p x / 2)))
    (hd : 0 < dist p x) (hx : 0 < f x) :
    ∃ q : X, ∃ r : ℝ, q ∈ Metric.ball x (dist p x / 2) ∧
      0 < r ∧ f x ≤ f q ∧ dist p x / 2 ≤ dist p q ∧
      r * f q = dist p x * f x / 4 ∧
      Metric.ball q r ⊆ Metric.ball x (dist p x / 2) ∧
      ∀ y ∈ Metric.ball q r, f y ≤ 2 * f q := by
  let S := Metric.closedBall x (dist p x / 2)
  let L : ℝ := dist p x * f x / 4
  have hfx : 0 < f x := hx
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨q, _, _, hscore, hmargin, hcontrol⟩ :=
    TauCeti.exists_point_with_doubling_bound S f (dist x)
      (fun _ ↦ 0) hbound hL.le (Metric.mem_closedBall_self (by positivity)) hfx
  have hfq : 0 < f q := hfx.trans_le hscore
  let r : ℝ := L / f q
  have hr : 0 < r := div_pos hL hfq
  have hbudget : dist x q + 2 * r ≤ dist p x / 2 := by
    have hcancel : 2 * L / f x = dist p x / 2 := by
      dsimp [L]
      field_simp
      ring
    simpa only [dist_self, zero_add, hcancel, mul_div_assoc] using hmargin
  have hq : q ∈ Metric.ball x (dist p x / 2) := by
    rw [Metric.mem_ball, dist_comm]
    linarith
  have hsubset : Metric.ball q r ⊆ Metric.ball x (dist p x / 2) :=
    Metric.ball_subset_ball' (by rw [dist_comm q x]; linarith)
  refine ⟨q, r, hq, hr, ?_, ?_, ?_, hsubset, ?_⟩
  · exact hscore
  · have htri := dist_triangle p q x
    have hqx := Metric.mem_ball.mp hq
    linarith
  · dsimp [r, L]
    rw [div_mul_cancel₀ _ hfq.ne']
  · intro y hy
    have hqy : dist q y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hyS : y ∈ S := Metric.ball_subset_closedBall (hsubset hy)
    have hfy : f y ≤ 2 * f q := hcontrol y hyS le_rfl (by
      have htri := dist_triangle x q y
      dsimp [r] at hqy
      linarith)
    exact hfy

/-- Continuous fields on a proper metric space admit a controlled ball,
with the original distance and size-scale budgets retained. -/
theorem exists_doubling_controlled_point_of_continuous
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (f : X → ℝ) (hcontinuous : Continuous f)
    (p x : X) (hd : 0 < dist p x) (hx : 0 < f x) :
    ∃ q : X, ∃ r : ℝ, q ∈ Metric.ball x (dist p x / 2) ∧
      0 < r ∧ f x ≤ f q ∧ dist p x / 2 ≤ dist p q ∧
      r * f q = dist p x * f x / 4 ∧
      Metric.ball q r ⊆ Metric.ball x (dist p x / 2) ∧
      ∀ y ∈ Metric.ball q r, f y ≤ 2 * f q :=
  exists_doubling_controlled_point_of_bddAbove f p x
    ((isCompact_closedBall x (dist p x / 2)).bddAbove_image hcontinuous.continuousOn) hd hx

end Metric
