/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Point picking in a metric space

A continuous function on a compact subset of a metric ball has a point at which its
distance-to-boundary weighted value is maximal. A ball of half the remaining radius around
that point lies inside the original ball, and the function is at most twice its value there.

## References

* O. Chodosh, *Introduction to Minimal Surfaces*, proof of Lemma 29.1.
-/

public noncomputable section

open Metric

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- The distance-to-boundary weighted value used in point picking. -/
@[expose]
def pointPickingWeight (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (R - dist x x₀) * f x

/-- A positive weighted value inside a closed ball has a positive distance from the
boundary and a positive function value. -/
theorem pointPickingWeight_pos_of_mem_closedBall {x₀ x : X} {R : ℝ} {f : X → ℝ}
    (hx : x ∈ closedBall x₀ R) (hpos : 0 < pointPickingWeight x₀ R f x) :
    0 < R - dist x x₀ ∧ 0 < f x := by
  have hnonneg : 0 ≤ R - dist x x₀ := sub_nonneg.mpr (mem_closedBall.mp hx)
  have hmul : 0 < (R - dist x x₀) * f x := hpos
  have hδ : 0 < R - dist x x₀ := by
    by_contra hh
    have heq : R - dist x x₀ = 0 := le_antisymm (le_of_not_gt hh) hnonneg
    simp [heq] at hmul
  have hfpos : 0 < f x := by
    by_contra hh
    have hmul_nonpos := mul_nonpos_of_nonneg_of_nonpos hδ.le (le_of_not_gt hh)
    exact (not_lt_of_ge hmul_nonpos) hmul
  exact ⟨hδ, hfpos⟩

/-- The compact metric-space point-picking lemma. The weight attains a positive maximum
at an interior point; on half its remaining radius the function is at most twice its
value at that point. -/
theorem exists_pointPicking {x₀ : X} {R : ℝ} {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hSball : S ⊆ closedBall x₀ R)
    (hf : ContinuousOn f S) {x : X} (hx : x ∈ S)
    (hM : 0 < pointPickingWeight x₀ R f x) :
    ∃ q ∈ S, q ∈ ball x₀ R ∧
      (∀ y ∈ S, pointPickingWeight x₀ R f y ≤
        pointPickingWeight x₀ R f q) ∧
      pointPickingWeight x₀ R f x ≤ pointPickingWeight x₀ R f q ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ = (R - dist q x₀) / 2 ∧
        ball q ρ ⊆ ball x₀ R ∧
        ρ * f q = pointPickingWeight x₀ R f q / 2 ∧
        pointPickingWeight x₀ R f x / 2 ≤ ρ * f q ∧
        ∀ y ∈ S, y ∈ ball q ρ → f y ≤ 2 * f q := by
  have hwcont : ContinuousOn (pointPickingWeight x₀ R f) S := by
    exact ((continuous_const.sub (continuous_id.dist continuous_const)).continuousOn).mul hf
  obtain ⟨q, hqS, hqmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ hwcont
  have hMle : pointPickingWeight x₀ R f x ≤ pointPickingWeight x₀ R f q := hqmax hx
  have hqpos : 0 < pointPickingWeight x₀ R f q := lt_of_lt_of_le hM hMle
  obtain ⟨hδ, hfq⟩ := pointPickingWeight_pos_of_mem_closedBall (hSball hqS) hqpos
  have hqball : q ∈ ball x₀ R := by
    rw [mem_ball]
    linarith [dist_comm x₀ q]
  let ρ : ℝ := (R - dist q x₀) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρf : ρ * f q = pointPickingWeight x₀ R f q / 2 := by
    dsimp [ρ, pointPickingWeight]
    ring
  have hMhalf : pointPickingWeight x₀ R f x / 2 ≤ ρ * f q := by
    rw [hρf]
    linarith
  refine ⟨q, hqS, hqball, (fun y hy ↦ hqmax hy), hMle, ρ, hρ, rfl, ?_,
    hρf, hMhalf, ?_⟩
  · intro y hy
    rw [mem_ball] at hy ⊢
    have htri := dist_triangle y q x₀
    dsimp [ρ] at hy
    linarith
  · intro y hyS hyball
    have hδy : ρ < R - dist y x₀ := by
      rw [mem_ball] at hyball
      have htri := dist_triangle y q x₀
      dsimp [ρ] at hyball ⊢
      linarith
    by_cases hyf : 0 ≤ f y
    · have hcompare : ρ * f y ≤ (R - dist y x₀) * f y :=
        mul_le_mul_of_nonneg_right hδy.le hyf
      have hweight := hqmax hyS
      dsimp [pointPickingWeight] at hweight
      have hhalf : ρ * f y ≤ ρ * (2 * f q) := by
        calc
          ρ * f y ≤ (R - dist y x₀) * f y := hcompare
          _ ≤ (R - dist q x₀) * f q := hweight
          _ = ρ * (2 * f q) := by dsimp [ρ]; ring
      exact le_of_mul_le_mul_left hhalf hρ
    · linarith

/-- At the point selected by point picking, rescaling distances by `f q` gives a ball
of radius at least half the initial weighted value, on which the normalized function
equals one at the centre and is at most two. -/
theorem exists_pointPicking_rescaled {x₀ : X} {R : ℝ} {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hSball : S ⊆ closedBall x₀ R)
    (hf : ContinuousOn f S) {x : X} (hx : x ∈ S)
    (hM : 0 < pointPickingWeight x₀ R f x) :
    ∃ q ∈ S, ∃ ρ : ℝ, 0 < f q ∧ 0 < ρ ∧
      ρ = (R - dist q x₀) / 2 ∧
      pointPickingWeight x₀ R f x / 2 ≤ f q * ρ ∧
      f q / f q = 1 ∧
      ∀ y ∈ S, f q * dist y q < f q * ρ → f y / f q ≤ 2 := by
  obtain ⟨q, hqS, _hqball, _hmax, hMle, ρ, hρ, hρeq, _hball, _hρf, hMhalf,
    hlocal⟩ :=
    exists_pointPicking hS hSball hf hx hM
  have hqpos : 0 < pointPickingWeight x₀ R f q := lt_of_lt_of_le hM hMle
  have hfq : 0 < f q :=
    (pointPickingWeight_pos_of_mem_closedBall (hSball hqS) hqpos).2
  refine ⟨q, hqS, ρ, hfq, hρ, hρeq, ?_, by field_simp, ?_⟩
  · rw [mul_comm]
    exact hMhalf
  · intro y hyS hyScaled
    have hyball : y ∈ ball q ρ := by
      rw [mem_ball]
      exact lt_of_mul_lt_mul_left hyScaled hfq.le
    exact (div_le_iff₀ hfq).mpr (hlocal y hyS hyball)

end TauCeti
