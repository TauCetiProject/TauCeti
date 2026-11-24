/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
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

Point picking selects a centre for blow-up rescaling. Let `X` be a pseudometric space,
`x₀ : X` a centre, `R : ℝ` a radius, and `f : X → ℝ` continuous on a compact subset `S` of
`closedBall x₀ R`. The weight `TauCeti.pointPickingWeight x₀ R f x` is
`(R - dist x x₀) * f x`, the function value multiplied by the radial margin.
If this weight is positive at some point of `S`,
`IsCompact.exists_mem_ball_isMaxOn_pointPickingWeight` gives a positive maximum at
`q ∈ S ∩ ball x₀ R`. For `ρ = (R - dist q x₀) / 2`, the ball `ball q ρ` lies inside the
original ball, and `f y ≤ 2 * f q` for `y ∈ S ∩ ball q ρ`.
More generally, `IsCompact.exists_point_picking` works along a map `g : Y → X` on a compact
subset `S` of `g ⁻¹' closedBall x₀ R`, assuming continuity only of the weighted quantity.
The comparison point must belong to `S` and have strictly positive weight. Taking
`S = g ⁻¹' closedBall x₀ R` gives the compact-preimage version used for the smooth Allard
estimate, with the local bound on the whole preimage of the ball about `g q`.

Scaling distances by `f q` gives the normalized estimate in
`IsCompact.exists_pointPickingWeight_div_two_le_and_div_le_two`.

## References

* O. Chodosh, *Introduction to Minimal Surfaces*, proof of Lemma 29.1.
-/

public noncomputable section

open Metric

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- The point-picking weight `pointPickingWeight x₀ R f x = (R - dist x x₀) * f x`
multiplies `f x` by the radial margin to radius `R` around the centre `x₀`. -/
def pointPickingWeight (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (R - dist x x₀) * f x

/-- The point-picking weight as a function. -/
theorem pointPickingWeight_def (x₀ : X) (R : ℝ) (f : X → ℝ) :
    pointPickingWeight x₀ R f = fun x ↦ (R - dist x x₀) * f x := (rfl)

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
theorem pointPickingWeight_zero (x₀ : X) (R : ℝ) :
    pointPickingWeight x₀ R 0 = 0 := by
  ext x
  simp [pointPickingWeight_apply]

/-- The constantly zero function has zero point-picking weight. -/
@[simp]
theorem pointPickingWeight_fun_zero (x₀ : X) (R : ℝ) :
    pointPickingWeight x₀ R (fun _ ↦ 0) = 0 := by
  exact pointPickingWeight_zero x₀ R

/-- The point-picking weight vanishes exactly on the sphere or at a zero of the function. -/
@[simp]
theorem pointPickingWeight_eq_zero_iff (x₀ x : X) (R : ℝ) (f : X → ℝ) :
    pointPickingWeight x₀ R f x = 0 ↔ x ∈ sphere x₀ R ∨ f x = 0 := by
  rw [pointPickingWeight_apply, mul_eq_zero, sub_eq_zero, mem_sphere, eq_comm (a := R)]

/-- The point-picking weight vanishes on the boundary sphere. -/
@[simp]
theorem pointPickingWeight_eq_zero_of_mem_sphere {x₀ x : X} {R : ℝ} (f : X → ℝ)
    (hx : x ∈ sphere x₀ R) : pointPickingWeight x₀ R f x = 0 := by
  simp [pointPickingWeight_apply, mem_sphere.mp hx]

/-- Nonnegative function values in the closed ball have nonnegative point-picking weight. -/
theorem pointPickingWeight_nonneg {x₀ x : X} {R : ℝ} {f : X → ℝ}
    (hx : x ∈ closedBall x₀ R) (hf : 0 ≤ f x) : 0 ≤ pointPickingWeight x₀ R f x := by
  rw [pointPickingWeight_apply]
  exact mul_nonneg (sub_nonneg.mpr (mem_closedBall.mp hx)) hf

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

/-- Functions agreeing on a set have point-picking weights agreeing on that set. -/
theorem _root_.Set.EqOn.pointPickingWeight {f g : X → ℝ} {S : Set X}
    (h : Set.EqOn f g S) (x₀ : X) (R : ℝ) :
    Set.EqOn (pointPickingWeight x₀ R f) (pointPickingWeight x₀ R g) S := by
  intro x hx
  simp only [pointPickingWeight_apply, h hx]

/-- A function continuous on a set has continuous point-picking weight on that set. -/
theorem _root_.ContinuousOn.pointPickingWeight {f : X → ℝ} {S : Set X}
    (hf : ContinuousOn f S) (x₀ : X) (R : ℝ) :
    ContinuousOn (pointPickingWeight x₀ R f) S := by
  exact ((continuous_const.sub (continuous_id.dist continuous_const)).continuousOn).mul hf

/-- A continuous function has continuous point-picking weight. -/
theorem _root_.Continuous.pointPickingWeight {f : X → ℝ}
    (hf : Continuous f) (x₀ : X) (R : ℝ) : Continuous (pointPickingWeight x₀ R f) := by
  exact (continuous_const.sub (continuous_id.dist continuous_const)).mul hf

/-- **Point picking along a map.** On a compact subset `S` of the preimage of a closed ball,
assume the weighted quantity is continuous and strictly positive at `q ∈ S`. It attains a
positive maximum at `p ∈ S` over the open ball, with `A p > 0` and `A y ≤ 2 * A p` for
`y ∈ S` whose image lies within half the radial margin of `g p`.
In particular, taking `S` to be the whole closed-ball preimage bounds `A` on the whole preimage
of that smaller open ball. No sign assumption on `A` is needed. -/
theorem _root_.IsCompact.exists_point_picking
    {Y Z : Type*} [TopologicalSpace Y] [PseudoMetricSpace Z]
    {g : Y → Z} {A : Y → ℝ} {x : Z} {r₀ : ℝ} {S : Set Y}
    (hK : IsCompact S) (hS : S ⊆ g ⁻¹' closedBall x r₀)
    (hcont : ContinuousOn (fun y ↦ (r₀ - dist (g y) x) * A y) S)
    {q : Y} (hq : q ∈ S) (hpos : 0 < (r₀ - dist (g q) x) * A q) :
    ∃ p ∈ S, g p ∈ ball x r₀ ∧ 0 < A p ∧
      IsMaxOn (fun y ↦ (r₀ - dist (g y) x) * A y) S p ∧
      (r₀ - dist (g q) x) * A q ≤ (r₀ - dist (g p) x) * A p ∧
      ∀ y ∈ S, dist (g y) (g p) < (r₀ - dist (g p) x) / 2 → A y ≤ 2 * A p := by
  obtain ⟨p, hpS, hmax⟩ := hK.exists_isMaxOn ⟨q, hq⟩ hcont
  have hqp : (r₀ - dist (g q) x) * A q ≤ (r₀ - dist (g p) x) * A p := hmax hq
  have hFp : 0 < (r₀ - dist (g p) x) * A p := hpos.trans_le hqp
  have hAp : 0 < A p :=
    pos_of_mul_pos_right hFp (sub_nonneg.mpr (mem_closedBall.mp (hS hpS)))
  have hd : 0 < r₀ - dist (g p) x := pos_of_mul_pos_left hFp hAp.le
  refine ⟨p, hpS, mem_ball.2 (by linarith), hAp, hmax, hqp, fun y hyS hy ↦ ?_⟩
  by_cases hyA : 0 ≤ A y
  · have hd2 : (r₀ - dist (g p) x) / 2 ≤ r₀ - dist (g y) x := by
      have := dist_triangle (g y) (g p) x
      linarith
    have h1 := (mul_le_mul_of_nonneg_right hd2 hyA).trans (hmax hyS)
    nlinarith
  · linarith

/-- Let `S ⊆ closedBall x₀ R` be compact and `f` continuous on `S`. If `x ∈ S` satisfies
`0 < pointPickingWeight x₀ R f x`, the weight attains a positive maximum at
`q ∈ S ∩ ball x₀ R`, with `0 < f q`. For `ρ = (R - dist q x₀) / 2`, the ball `ball q ρ`
lies in `ball x₀ R`, its scaled radius is at least `pointPickingWeight x₀ R f x / 2`, and
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
  obtain ⟨q, hqS, hqball, hfq, hqmax, _hMle, hlocal⟩ :=
    hS.exists_point_picking (g := id) hSball (hf.pointPickingWeight x₀ R) hx hM
  have hMle : pointPickingWeight x₀ R f x ≤ pointPickingWeight x₀ R f q := hqmax hx
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
    exact hlocal y hyS (mem_ball.mp hyball)

/-- Let `S ⊆ closedBall x₀ R` be compact and `f` continuous on `S`. If `x ∈ S` satisfies
`0 < pointPickingWeight x₀ R f x`, there are `q ∈ S ∩ ball x₀ R` and
`ρ = (R - dist q x₀) / 2 > 0` with `0 < f q`, `ball q ρ ⊆ ball x₀ R`, and scaled radius
`f q * ρ` at least `pointPickingWeight x₀ R f x / 2`.
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
