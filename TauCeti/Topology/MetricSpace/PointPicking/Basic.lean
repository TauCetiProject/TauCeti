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

Point picking selects a centre for blow-up rescaling. If a continuous function on a compact
subset `S` of a closed metric ball has positive distance-to-boundary weighted value at some
point of `S`, that weight attains a positive maximum at `q ∈ S ∩ ball x₀ R`. The ball of half
the remaining radius lies inside the original ball, and `f y ≤ 2 * f q` for
`y ∈ S ∩ ball q ρ`. Scaling distances by `f q` gives the normalized estimate in
`IsCompact.exists_pointPickingWeight_div_two_le_and_div_le_two`.

## References

* O. Chodosh, *Introduction to Minimal Surfaces*, proof of Lemma 29.1.
-/

public noncomputable section

open Metric

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- The distance-to-boundary weighted value used in point picking. -/
def pointPickingWeight (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (R - dist x x₀) * f x

/-- The formula for the point-picking weight. -/
theorem pointPickingWeight_apply (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) :
    pointPickingWeight x₀ R f x = (R - dist x x₀) * f x := (rfl)

/-- At the centre the point-picking weight is the radius times the function value. -/
@[simp]
theorem pointPickingWeight_self (x₀ : X) (R : ℝ) (f : X → ℝ) :
    pointPickingWeight x₀ R f x₀ = R * f x₀ := by
  simp [pointPickingWeight_apply]

/-- The zero function has zero point-picking weight. -/
@[simp]
theorem pointPickingWeight_zero (x₀ : X) (R : ℝ) (x : X) :
    pointPickingWeight x₀ R (fun _ ↦ 0) x = 0 := by
  simp [pointPickingWeight_apply]

/-- The point-picking weight vanishes on the boundary sphere. -/
@[simp]
theorem pointPickingWeight_eq_zero_of_mem_sphere {x₀ x : X} {R : ℝ} (f : X → ℝ)
    (hx : x ∈ sphere x₀ R) : pointPickingWeight x₀ R f x = 0 := by
  simp [pointPickingWeight_apply, mem_sphere.mp hx]

/-- Positive function values inside the open ball have positive point-picking weight. -/
theorem pointPickingWeight_pos {x₀ x : X} {R : ℝ} {f : X → ℝ}
    (hx : x ∈ ball x₀ R) (hf : 0 < f x) : 0 < pointPickingWeight x₀ R f x := by
  rw [pointPickingWeight_apply]
  exact mul_pos (sub_pos.mpr (mem_ball.mp hx)) hf

/-- On the closed ball, positive weight is equivalent to open-ball membership and a positive
function value. -/
@[simp]
theorem pointPickingWeight_pos_iff_of_mem_closedBall {x₀ x : X} {R : ℝ} {f : X → ℝ}
    (hx : x ∈ closedBall x₀ R) :
    0 < pointPickingWeight x₀ R f x ↔ x ∈ ball x₀ R ∧ 0 < f x := by
  constructor
  · intro hpos
    rw [pointPickingWeight_apply] at hpos
    have hfpos := pos_of_mul_pos_right hpos (sub_nonneg.mpr (mem_closedBall.mp hx))
    exact ⟨mem_ball.mpr (sub_pos.mp (pos_of_mul_pos_left hpos hfpos.le)), hfpos⟩
  · rintro ⟨hxball, hf⟩
    exact pointPickingWeight_pos hxball hf

/-- A function continuous on a set has continuous point-picking weight on that set. -/
theorem _root_.ContinuousOn.pointPickingWeight {f : X → ℝ} {S : Set X}
    (hf : ContinuousOn f S) (x₀ : X) (R : ℝ) :
    ContinuousOn (pointPickingWeight x₀ R f) S := by
  exact ((continuous_const.sub (continuous_id.dist continuous_const)).continuousOn).mul hf

/-- A continuous function has continuous point-picking weight. -/
theorem _root_.Continuous.pointPickingWeight {f : X → ℝ}
    (hf : Continuous f) (x₀ : X) (R : ℝ) : Continuous (pointPickingWeight x₀ R f) := by
  exact (continuous_const.sub (continuous_id.dist continuous_const)).mul hf

/-- If the weight is positive somewhere on the compact set `S`, it attains a positive maximum
at `q ∈ S ∩ ball x₀ R`, with `0 < f q`. For `ρ = (R - dist q x₀) / 2`, the ball `ball q ρ`
lies in `ball x₀ R`, its scaled radius is at least half the starting weight, and
`f y ≤ 2 * f q` for `y ∈ S ∩ ball q ρ`. -/
theorem _root_.IsCompact.exists_mem_ball_isMaxOn_pointPickingWeight
    {x₀ : X} {R : ℝ} {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hSball : S ⊆ closedBall x₀ R)
    (hf : ContinuousOn f S) {x : X} (hx : x ∈ S)
    (hM : 0 < pointPickingWeight x₀ R f x) :
    ∃ q ∈ S, q ∈ ball x₀ R ∧ 0 < f q ∧
      IsMaxOn (pointPickingWeight x₀ R f) S q ∧
      pointPickingWeight x₀ R f x ≤ pointPickingWeight x₀ R f q ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ = (R - dist q x₀) / 2 ∧
        ball q ρ ⊆ ball x₀ R ∧
        ρ * f q = pointPickingWeight x₀ R f q / 2 ∧
        pointPickingWeight x₀ R f x / 2 ≤ ρ * f q ∧
        ∀ y ∈ S, y ∈ ball q ρ → f y ≤ 2 * f q := by
  obtain ⟨q, hqS, hqmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ (hf.pointPickingWeight x₀ R)
  have hMle : pointPickingWeight x₀ R f x ≤ pointPickingWeight x₀ R f q := hqmax hx
  have hqpos : 0 < pointPickingWeight x₀ R f q := lt_of_lt_of_le hM hMle
  obtain ⟨hqball, hfq⟩ := (pointPickingWeight_pos_iff_of_mem_closedBall (hSball hqS)).mp hqpos
  have hδ : 0 < R - dist q x₀ := sub_pos.mpr (mem_ball.mp hqball)
  let ρ : ℝ := (R - dist q x₀) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρf : ρ * f q = pointPickingWeight x₀ R f q / 2 := by
    dsimp [ρ, pointPickingWeight]
    ring
  have hMhalf : pointPickingWeight x₀ R f x / 2 ≤ ρ * f q := by
    rw [hρf]
    linarith
  refine ⟨q, hqS, hqball, hfq, hqmax, hMle, ρ, hρ, rfl, ?_, hρf, hMhalf, ?_⟩
  · exact ball_subset_ball' (by dsimp [ρ]; linarith)
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

/-- There are `q ∈ S ∩ ball x₀ R` and `ρ = (R - dist q x₀) / 2 > 0` with `0 < f q`,
`ball q ρ ⊆ ball x₀ R`, and scaled radius `f q * ρ` at least half the starting weight.
The normalized value `f y / f q` is at most two for `y ∈ S` whose distance from `q`,
scaled by `f q`, is less than this scaled radius. -/
theorem _root_.IsCompact.exists_pointPickingWeight_div_two_le_and_div_le_two
    {x₀ : X} {R : ℝ} {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hSball : S ⊆ closedBall x₀ R)
    (hf : ContinuousOn f S) {x : X} (hx : x ∈ S)
    (hM : 0 < pointPickingWeight x₀ R f x) :
    ∃ q ∈ S, q ∈ ball x₀ R ∧ ∃ ρ : ℝ, 0 < f q ∧ 0 < ρ ∧
      ρ = (R - dist q x₀) / 2 ∧ ball q ρ ⊆ ball x₀ R ∧
      pointPickingWeight x₀ R f x / 2 ≤ f q * ρ ∧
      ∀ y ∈ S, f q * dist y q < f q * ρ → f y / f q ≤ 2 := by
  obtain ⟨q, hqS, hqball, hfq, _hmax, _hMle, ρ, hρ, hρeq, hball, _hρf, hMhalf,
    hlocal⟩ := hS.exists_mem_ball_isMaxOn_pointPickingWeight hSball hf hx hM
  refine ⟨q, hqS, hqball, ρ, hfq, hρ, hρeq, hball, ?_, ?_⟩
  · rw [mul_comm]
    exact hMhalf
  · intro y hyS hyScaled
    have hyball : y ∈ ball q ρ := by
      rw [mem_ball]
      exact lt_of_mul_lt_mul_left hyScaled hfq.le
    exact (div_le_iff₀ hfq).mpr (hlocal y hyS hyball)

end TauCeti
