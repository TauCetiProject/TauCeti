/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Closed convex hulls and convex sets containing a ball

Taking the closed convex hull of a set in a real seminormed space preserves both boundedness and
diameter. These are the closed-hull counterparts of `isBounded_convexHull` and `convexHull_diam`.

A convex set containing a ball `ball x r` and a point `y` contains the ball of radius `(1 - t) * r`
about `x + t • (y - x)` for every `0 ≤ t ≤ 1` (`Convex.ball_add_smul_sub_subset`).
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- A closed convex hull is bounded exactly when the original set is. -/
@[simp]
theorem isBounded_closedConvexHull : IsBounded (closedConvexHull ℝ K) ↔ IsBounded K := by
  rw [closedConvexHull_eq_closure_convexHull, isBounded_closure_iff, isBounded_convexHull]

/-- Taking the closed convex hull preserves the diameter. -/
@[simp]
theorem diam_closedConvexHull : diam (closedConvexHull ℝ K) = diam K := by
  rw [closedConvexHull_eq_closure_convexHull, diam_closure, convexHull_diam]

end TauCeti

/-- A convex set containing the ball `ball x r` and a point `y` contains the ball of radius
`(1 - t) * r` about `x + t • (y - x)` for every `0 ≤ t ≤ 1`. -/
theorem Convex.ball_add_smul_sub_subset {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) {x y : E} {r t : ℝ} (hball : Metric.ball x r ⊆ s) (hy : y ∈ s)
    (ht₀ : 0 ≤ t) (ht : t ≤ 1) : Metric.ball (x + t • (y - x)) ((1 - t) * r) ⊆ s := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  intro z hz
  -- `z = (1 - t) • b + t • y` with `b = x + (1 - t)⁻¹ • (z - (x + t • (y - x)))` in `ball x r`.
  have hb : x + (1 - t)⁻¹ • (z - (x + t • (y - x))) ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by linarith), ← dist_eq_norm, inv_mul_lt_iff₀ (by linarith)]
    rwa [Metric.mem_ball] at hz
  convert hs (hball hb) hy (by linarith : (0 : ℝ) ≤ 1 - t) ht₀ (by ring) using 1
  rw [smul_add, smul_smul, mul_inv_cancel₀ (by linarith : (1 - t) ≠ 0), one_smul]
  module
