/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Point picking on compact balls

A continuous real-valued function that is positive at a point admits a nearby point where it is
controlled by twice its value on a smaller ball, without losing the radius-times-value bound.
Applied to a derivative norm, this selects centres and scales for bubbling arguments.

The argument maximizes distance to the boundary times the function, a compact-ball version of
the point-picking argument in McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 4.2.
-/

public section

open Metric Set

namespace TauCeti

/-- Point picking with a radius-times-value bound. The selected ball lies in the original
closed ball, and the function is at most twice its selected value throughout that ball. -/
theorem exists_pos_mul_le_and_forall_le_two_mul
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {f : X → ℝ} {x : X} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedBall x (2 * r)))
    (hx : 0 < f x) :
    ∃ c ∈ closedBall x (2 * r), ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      r * f x ≤ δ * f c ∧ 0 < f c ∧
      closedBall c δ ⊆ closedBall x (2 * r) ∧
      ∀ y ∈ closedBall c δ, f y ≤ 2 * f c := by
  have hxmem : x ∈ closedBall x (2 * r) := mem_closedBall_self (by positivity)
  obtain ⟨c, hc, hmax⟩ := (isCompact_closedBall x (2 * r)).exists_isMaxOn
    (f := fun y => (2 * r - dist y x) * f y) ⟨x, hxmem⟩
    (((continuous_const.sub (continuous_id.dist continuous_const)).continuousOn).mul hf)
  have hmaxx : (2 * r - dist x x) * f x ≤ (2 * r - dist c x) * f c := hmax hxmem
  simp only [dist_self, sub_zero] at hmaxx
  have hweight : 0 ≤ 2 * r - dist c x := sub_nonneg.mpr hc
  have hfc : 0 < f c := by
    by_contra h
    have : (2 * r - dist c x) * f c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hweight (le_of_not_gt h)
    nlinarith
  have hweightpos : 0 < 2 * r - dist c x := by
    by_contra h
    have : 2 * r - dist c x = 0 := le_antisymm (le_of_not_gt h) hweight
    rw [this, zero_mul] at hmaxx
    nlinarith
  let δ := (2 * r - dist c x) / 2
  have hδ : 0 < δ := half_pos hweightpos
  have hδr : δ ≤ r := by dsimp [δ]; nlinarith [dist_nonneg (x := c) (y := x)]
  have hsub : closedBall c δ ⊆ closedBall x (2 * r) := by
    intro y hy
    have htri := dist_triangle y c x
    have hyc : dist y c ≤ δ := hy
    dsimp [δ] at hyc
    exact htri.trans (by linarith)
  refine ⟨c, hc, δ, hδ, hδr, ?_, hfc, hsub, ?_⟩
  · dsimp [δ]
    nlinarith
  · intro y hy
    by_cases hneg : f y < 0
    · linarith
    have hnonneg := le_of_not_gt hneg
    have hmaxy : (2 * r - dist y x) * f y ≤ (2 * r - dist c x) * f c :=
      hmax (hsub hy)
    have htri := dist_triangle y c x
    have hyc : dist y c ≤ δ := hy
    have hwy : δ ≤ 2 * r - dist y x := by dsimp [δ] at *; linarith
    have hmul := mul_le_mul_of_nonneg_right hwy hnonneg
    have hbound : δ * f y ≤ δ * (2 * f c) := by
      dsimp [δ] at *
      nlinarith
    exact (mul_le_mul_iff_right₀ hδ).1 hbound

end TauCeti
