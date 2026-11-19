/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Lipschitz maps vanishing on a hyperplane

A Lipschitz map that vanishes on the affine hyperplane `{f = a}` of a real normed space is bounded
by a multiple of `|f x - a|`: moving from `x` along a vector `v` with `f v = 1` reaches the
hyperplane after a displacement of norm `|f x - a| ‖v‖`. The functional `f` only needs to be
linear, not continuous.

## Main results

* `LipschitzWith.norm_le_mul_abs_sub_of_eq_zero`: if `g` is `K`-Lipschitz, vanishes on
  `{f = a}`, and `f v = 1`, then `‖g x‖ ≤ K ‖v‖ |f x - a|`.
-/

public section

open scoped NNReal

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup F]

/-- **A Lipschitz map vanishing on a hyperplane is `O (|f x - a|)`.** If `g` is `K`-Lipschitz and
vanishes on the hyperplane `{f = a}` of a linear functional `f`, then `‖g x‖ ≤ K ‖v‖ |f x - a|`
for every `v` with `f v = 1`. -/
theorem LipschitzWith.norm_le_mul_abs_sub_of_eq_zero {K : ℝ≥0} {g : E → F}
    (hg : LipschitzWith K g) {f : E →ₗ[ℝ] ℝ} {v : E} (hv : f v = 1) {a : ℝ}
    (hg0 : ∀ x, f x = a → g x = 0) (x : E) : ‖g x‖ ≤ K * ‖v‖ * |f x - a| := by
  -- The point `x - (f x - a) • v` lies on the hyperplane, at distance `|f x - a| ‖v‖` from `x`.
  have hP : f (x - (f x - a) • v) = a := by simp [hv]
  have h := hg.dist_le_mul x (x - (f x - a) • v)
  simp only [hg0 _ hP, dist_eq_norm, sub_zero, sub_sub_cancel, norm_smul, Real.norm_eq_abs] at h
  linarith [mul_comm |f x - a| ‖v‖, mul_assoc (K : ℝ) ‖v‖ |f x - a|]
