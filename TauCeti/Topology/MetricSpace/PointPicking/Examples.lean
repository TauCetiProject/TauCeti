/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.PointPicking.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Point picking on the real line

The constant function and the absolute value give explicit maxima for
`pointPickingWeight 0 1 f` on `[-1, 1]`. The absolute value example also shows that the local
factor two cannot in general be replaced by one. Unnamed examples check the values, level
sets, radii, local bounds, and the zero weight at the boundary.

## References

* O. Chodosh, *Introduction to Minimal Surfaces*, proof of Lemma 29.1.
-/

public noncomputable section

namespace TauCeti.PointPicking

/-- The constant-function weight on `[-1, 1]` is maximal at the origin. -/
theorem isMaxOn_pointPickingWeight_const_Icc :
    IsMaxOn (pointPickingWeight (0 : ℝ) 1 (fun _ : ℝ ↦ 1))
      (Set.Icc (-1 : ℝ) 1) 0 := by
  intro q _hq
  simp [pointPickingWeight_apply]

-- One is the attained maximum of the constant-function weighted values.
example :
    IsGreatest (pointPickingWeight (0 : ℝ) 1 (fun _ : ℝ ↦ 1) ''
      Set.Icc (-1 : ℝ) 1) 1 := by
  refine ⟨⟨0, by norm_num, by simp⟩, ?_⟩
  apply mem_upperBounds.mpr
  refine Set.forall_mem_image.mpr ?_
  intro q hq
  simpa using isMaxOn_pointPickingWeight_const_Icc hq

-- The constant-function weight equals one exactly at the origin.
example (q : ℝ) :
    pointPickingWeight (0 : ℝ) 1 (fun _ : ℝ ↦ 1) q = 1 ↔ q = 0 := by
  simp [pointPickingWeight_apply]

-- The constant example has radius and scaled radius one half.
example : (1 - dist (0 : ℝ) 0) / 2 = 1 / 2 := by simp

example : (1 / 2 : ℝ) * 1 = pointPickingWeight (0 : ℝ) 1 (fun _ ↦ 1) 0 / 2 := by
  norm_num

example : (1 : ℝ) ≤ 2 * 1 := by norm_num

private theorem pointPickingWeight_abs_le (q : ℝ) :
    pointPickingWeight (0 : ℝ) 1 (fun y ↦ |y|) q ≤ 1 / 4 := by
  rw [pointPickingWeight_apply, Real.dist_eq, sub_zero]
  nlinarith [sq_nonneg (|q| - 1 / 2)]

/-- The absolute-value weight on `[-1, 1]` is maximal at `1 / 2`. -/
theorem isMaxOn_pointPickingWeight_abs_Icc :
    IsMaxOn (pointPickingWeight (0 : ℝ) 1 (fun q : ℝ ↦ |q|))
      (Set.Icc (-1 : ℝ) 1) (1 / 2) := by
  intro q _hq
  have hq := pointPickingWeight_abs_le q
  norm_num [pointPickingWeight_apply, Real.dist_eq] at hq ⊢
  exact hq

/-- The absolute-value weight on `[-1, 1]` is also maximal at `-1 / 2`. -/
theorem isMaxOn_pointPickingWeight_abs_Icc_neg_one_div_two :
    IsMaxOn (pointPickingWeight (0 : ℝ) 1 (fun q : ℝ ↦ |q|))
      (Set.Icc (-1 : ℝ) 1) (-1 / 2) := by
  intro q _hq
  have hq := pointPickingWeight_abs_le q
  norm_num [pointPickingWeight_apply, Real.dist_eq] at hq ⊢
  exact hq

-- One quarter is the attained maximum of the absolute-value weighted values.
example :
    IsGreatest (pointPickingWeight (0 : ℝ) 1 (fun q : ℝ ↦ |q|) ''
      Set.Icc (-1 : ℝ) 1) (1 / 4 : ℝ) := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num [pointPickingWeight_apply, Real.dist_eq]⟩, ?_⟩
  apply mem_upperBounds.mpr
  refine Set.forall_mem_image.mpr ?_
  intro q hq
  have h := isMaxOn_pointPickingWeight_abs_Icc hq
  norm_num [pointPickingWeight_apply, Real.dist_eq] at h ⊢
  exact h

-- The absolute-value weight equals one quarter exactly at the two selected points.
example (q : ℝ) :
    pointPickingWeight (0 : ℝ) 1 (fun y ↦ |y|) q = 1 / 4 ↔
      q = 1 / 2 ∨ q = -1 / 2 := by
  constructor
  · intro h
    rw [pointPickingWeight_apply, Real.dist_eq, sub_zero] at h
    have hs : (|q| - 1 / 2) ^ 2 = 0 := by nlinarith
    have ha : |q| = 1 / 2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    simpa only [neg_div'] using (abs_eq (by positivity : (0 : ℝ) ≤ 1 / 2)).mp ha
  · rintro (rfl | rfl) <;> norm_num [pointPickingWeight_apply, Real.dist_eq]

-- Both absolute-value maximizers have radius one quarter and scaled radius one eighth.
example : (1 - dist (1 / 2 : ℝ) 0) / 2 = 1 / 4 := by norm_num [Real.dist_eq]

example : (1 - dist (-1 / 2 : ℝ) 0) / 2 = 1 / 4 := by norm_num [Real.dist_eq]

example : (1 / 4 : ℝ) * |(1 / 2 : ℝ)| =
    pointPickingWeight (0 : ℝ) 1 (fun y ↦ |y|) (1 / 2) / 2 := by
  norm_num [pointPickingWeight_apply, Real.dist_eq]

example : (1 / 4 : ℝ) * |(-1 / 2 : ℝ)| =
    pointPickingWeight (0 : ℝ) 1 (fun y ↦ |y|) (-1 / 2) / 2 := by
  norm_num [pointPickingWeight_apply, Real.dist_eq]

-- The ball-inclusion API gives the bound at either centre without a sign case split.
example (y : ℝ) (hy : y ∈ Metric.ball (1 / 2 : ℝ) (1 / 4)) : |y| ≤ 3 / 4 := by
  have h : y ∈ Metric.ball (0 : ℝ) (3 / 4) :=
    Metric.ball_subset_ball' (by norm_num [Real.dist_eq]) hy
  exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using h)

example (y : ℝ) (hy : y ∈ Metric.ball (-1 / 2 : ℝ) (1 / 4)) : |y| ≤ 3 / 4 := by
  have h : y ∈ Metric.ball (0 : ℝ) (3 / 4) :=
    Metric.ball_subset_ball' (by norm_num [Real.dist_eq]) hy
  exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using h)

example : (3 / 4 : ℝ) ≤ 2 * |(1 / 2 : ℝ)| := by norm_num

example : (3 / 4 : ℝ) ≤ 2 * |(-1 / 2 : ℝ)| := by norm_num

-- A point in the selected ball violates a proposed factor-one bound.
example : (5 / 8 : ℝ) ∈ Metric.ball (1 / 2 : ℝ) (1 / 4) := by
  norm_num [Metric.mem_ball, Real.dist_eq]

example : ¬ |(5 / 8 : ℝ)| ≤ |(1 / 2 : ℝ)| := by norm_num

-- Starting at the boundary point gives zero weight for any function.
example (f : ℝ → ℝ) : pointPickingWeight (0 : ℝ) 1 f 1 = 0 := by
  exact pointPickingWeight_eq_zero_of_mem_sphere f (by norm_num [Metric.mem_sphere, Real.dist_eq])

end TauCeti.PointPicking
