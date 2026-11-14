/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.PointPicking.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Point picking on the real line

The constant function and the absolute value give explicit maxima for the weighted quantity
`(1 - dist q 0) * f q` on `[-1, 1]`. The absolute value example also shows that the local
factor two cannot in general be replaced by one.

## References

* O. Chodosh, *Introduction to Minimal Surfaces*, proof of Lemma 29.1.
-/

public noncomputable section

namespace TauCeti.PointPicking

/-- For the constant function, the weighted value on `[-1, 1]` is at most one. -/
theorem realLine_constant_weight_le (q : ℝ) :
    (1 - dist q 0) * (1 : ℝ) ≤ 1 := by
  simp only [Real.dist_eq, sub_zero, mul_one]
  linarith [abs_nonneg q]

/-- The constant example attains its maximum at the origin. -/
theorem realLine_constant_weight_eq :
    (1 - dist (0 : ℝ) 0) * (1 : ℝ) = 1 := by
  simp

/-- One is the attained maximum of the constant-function weighted values. -/
theorem realLine_constant_isGreatest :
    IsGreatest (((fun q : ℝ ↦ (1 - dist q 0) * (1 : ℝ)) ''
      Set.Icc (-1 : ℝ) 1)) 1 := by
  constructor
  · exact ⟨0, by norm_num, realLine_constant_weight_eq⟩
  · rintro b ⟨q, _hq, rfl⟩
    exact realLine_constant_weight_le q

/-- The explicit constant-function maximizer has the weighted-maximizer property used
by the general point-picking lemma. -/
theorem realLine_constant_isMaxOn :
    IsMaxOn (pointPickingWeight (0 : ℝ) 1 (fun _ : ℝ ↦ 1))
      (Set.Icc (-1 : ℝ) 1) 0 := by
  intro q _hq
  simpa only [Set.mem_ofPred_eq, pointPickingWeight, realLine_constant_weight_eq] using
    realLine_constant_weight_le q

/-- The origin is the unique maximizer for the constant-function example. -/
theorem realLine_constant_weight_eq_iff (q : ℝ) :
    (1 - dist q 0) * (1 : ℝ) = 1 ↔ q = 0 := by
  rw [Real.dist_eq, sub_zero, mul_one]
  constructor
  · intro h
    exact abs_eq_zero.mp (by linarith)
  · rintro rfl
    simp

/-- The corresponding point-picking radius is one half. -/
theorem realLine_constant_radius : (1 - dist (0 : ℝ) 0) / 2 = 1 / 2 := by
  simp

/-- The constant function satisfies the local factor-two bound on the selected ball. -/
theorem realLine_constant_local :
    (1 : ℝ) ≤ 2 * (1 : ℝ) := by
  norm_num

/-- The absolute-value example has weighted maximum at most one quarter. -/
theorem realLine_abs_weight_le (q : ℝ) :
    (1 - dist q 0) * |q| ≤ 1 / 4 := by
  rw [Real.dist_eq, sub_zero]
  nlinarith [sq_nonneg (|q| - 1 / 2)]

/-- Both points at distance one half from the origin attain the weighted maximum. -/
theorem realLine_abs_weight_eq_pos :
    (1 - dist (1 / 2 : ℝ) 0) * |(1 / 2 : ℝ)| = 1 / 4 := by
  norm_num [Real.dist_eq]

/-- One quarter is the attained maximum of the absolute-value weighted values. -/
theorem realLine_abs_isGreatest :
    IsGreatest (((fun q : ℝ ↦ (1 - dist q 0) * |q|) ''
      Set.Icc (-1 : ℝ) 1)) (1 / 4 : ℝ) := by
  constructor
  · exact ⟨1 / 2, by norm_num, realLine_abs_weight_eq_pos⟩
  · rintro b ⟨q, _hq, rfl⟩
    exact realLine_abs_weight_le q

/-- The positive absolute-value maximizer has the weighted-maximizer property used
by the general point-picking lemma. -/
theorem realLine_abs_isMaxOn :
    IsMaxOn (pointPickingWeight (0 : ℝ) 1 (fun q : ℝ ↦ |q|))
      (Set.Icc (-1 : ℝ) 1) (1 / 2) := by
  intro q _hq
  simpa only [Set.mem_ofPred_eq, pointPickingWeight, realLine_abs_weight_eq_pos] using
    realLine_abs_weight_le q

/-- The negative point at distance one half also attains the weighted maximum. -/
theorem realLine_abs_weight_eq_neg :
    (1 - dist (-1 / 2 : ℝ) 0) * |(-1 / 2 : ℝ)| = 1 / 4 := by
  norm_num [Real.dist_eq]

/-- These are the only maximizers of the absolute-value weighted quantity. -/
theorem realLine_abs_weight_eq_iff (q : ℝ) :
    (1 - dist q 0) * |q| = 1 / 4 ↔ q = 1 / 2 ∨ q = -1 / 2 := by
  constructor
  · intro h
    rw [Real.dist_eq, sub_zero] at h
    have hs : (|q| - 1 / 2) ^ 2 = 0 := by
      nlinarith
    have ha : |q| = 1 / 2 := by
      have hz := mul_self_eq_zero.mp (by simpa only [pow_two] using hs)
      linarith
    rcases le_total 0 q with hq | hq
    · left
      rwa [abs_of_nonneg hq] at ha
    · right
      rw [abs_of_nonpos hq] at ha
      linarith
  · rintro (rfl | rfl)
    · exact realLine_abs_weight_eq_pos
    · exact realLine_abs_weight_eq_neg

/-- At the positive maximizer, the point-picking radius is one quarter. -/
theorem realLine_abs_radius :
    (1 - dist (1 / 2 : ℝ) 0) / 2 = 1 / 4 := by
  norm_num [Real.dist_eq]

/-- The negative maximizer has the same point-picking radius. -/
theorem realLine_abs_radius_neg :
    (1 - dist (-1 / 2 : ℝ) 0) / 2 = 1 / 4 := by
  norm_num [Real.dist_eq]

/-- On the chosen ball, the absolute value is at most three quarters. -/
theorem realLine_abs_local_three_quarters (y : ℝ)
    (hy : y ∈ Metric.ball (1 / 2 : ℝ) (1 / 4)) : |y| ≤ 3 / 4 := by
  have hdist : |y - 1 / 2| < (1 / 4 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hy
  rcases abs_lt.mp hdist with ⟨hl, hu⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- The local factor-two estimate for the absolute-value example. -/
theorem realLine_abs_local (y : ℝ)
    (hy : y ∈ Metric.ball (1 / 2 : ℝ) (1 / 4)) :
    |y| ≤ 3 / 4 ∧ (3 / 4 : ℝ) ≤ 2 * |(1 / 2 : ℝ)| ∧
      |y| ≤ 2 * |(1 / 2 : ℝ)| := by
  have h := realLine_abs_local_three_quarters y hy
  exact ⟨h, by norm_num, le_trans h (by norm_num)⟩

/-- The same local estimate holds at the negative maximizer. -/
theorem realLine_abs_local_neg (y : ℝ)
    (hy : y ∈ Metric.ball (-1 / 2 : ℝ) (1 / 4)) :
    |y| ≤ 3 / 4 ∧ (3 / 4 : ℝ) ≤ 2 * |(-1 / 2 : ℝ)| ∧
      |y| ≤ 2 * |(-1 / 2 : ℝ)| := by
  have hdist : |y - -1 / 2| < (1 / 4 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hy
  rcases abs_lt.mp hdist with ⟨hl, hu⟩
  have h : |y| ≤ 3 / 4 := by
    apply abs_le.mpr
    constructor <;> linarith
  exact ⟨h, by norm_num, le_trans h (by norm_num)⟩

/-- A point in the chosen ball has larger absolute value than the maximizer. -/
theorem realLine_abs_factor_one_fails :
    (5 / 8 : ℝ) ∈ Metric.ball (1 / 2 : ℝ) (1 / 4) ∧
      ¬ |(5 / 8 : ℝ)| ≤ |(1 / 2 : ℝ)| := by
  constructor
  · rw [Metric.mem_ball, Real.dist_eq]
    norm_num
  · norm_num

/-- Starting at the boundary point `1` gives weighted value zero for any function. -/
theorem realLine_boundary_weight (f : ℝ → ℝ) :
    (1 - dist (1 : ℝ) 0) * f 1 = 0 := by
  norm_num [Real.dist_eq]

end TauCeti.PointPicking
