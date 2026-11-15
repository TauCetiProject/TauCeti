/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Convex.Topology

/-!
# Closed convex hulls and convex sets containing a ball

Taking the closed convex hull of a set in a real seminormed space preserves both boundedness and
diameter. These are the closed-hull counterparts of `isBounded_convexHull` and `convexHull_diam`.

A convex set containing a ball `ball x r` and a point `y` contains the ball of radius `(1 - t) * r`
about `x + t • (y - x)` for every `0 ≤ t ≤ 1` (`Convex.ball_add_smul_sub_subset`).

If a set `Ω` is star-convex about every point of `Metric.ball x₀ ρ`, then for every strictly
smaller radius `r < ρ` and every `x ∈ Ω`, segments from `Metric.closedBall x₀ r` to `x` stay in `Ω`
(`TauCeti.add_smul_sub_mem_of_mem_closedBall_of_forall_starConvex`), and in a proper real normed
space the closed convex hulls `closure (convexHull ℝ (insert x (Metric.closedBall x₀ r)))` and
`closure (convexHull ℝ (insert x (Metric.ball x₀ r)))` are contained in `Ω`
(`TauCeti.closure_convexHull_insert_closedBall_subset_of_forall_starConvex`,
`TauCeti.closure_convexHull_insert_ball_subset_of_forall_starConvex`).
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

/-- If `Ω` is star-convex about every point of `Metric.ball x₀ ρ`, then for any `r < ρ`,
any `x ∈ Ω`, and any `y ∈ Metric.closedBall x₀ r`, the closed segment from `y` to `x` lies in
`Ω`. -/
theorem add_smul_sub_mem_of_mem_closedBall_of_forall_starConvex
    {Ω : Set E} {x y x₀ : E} {r ρ t : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hy : y ∈ closedBall x₀ r) (ht : t ∈ Icc (0 : ℝ) 1)
    (hstar : ∀ z ∈ ball x₀ ρ, StarConvex ℝ z Ω) :
    y + t • (x - y) ∈ Ω :=
  (hstar y (closedBall_subset_ball hr hy)).add_smul_sub_mem hx ht.1 ht.2

/-- In a proper real normed space, if `Ω` is star-convex about every point of `Metric.ball x₀ ρ`,
then for every `x ∈ Ω` and `r < ρ` the closed convex hull of
`insert x (Metric.closedBall x₀ r)` is contained in `Ω`. -/
theorem closure_convexHull_insert_closedBall_subset_of_forall_starConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Ω : Set E} {x x₀ : E} {r ρ : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω) :
    closure (convexHull ℝ (insert x (closedBall x₀ r))) ⊆ Ω :=
  (isCompact_closedBall x₀ r).closure_convexHull_insert_subset_of_forall_starConvex
    (convex_closedBall x₀ r) Subset.rfl hx fun y hy ↦ hstar y (closedBall_subset_ball hr hy)

/-- In a proper real normed space, if `Ω` is star-convex about every point of `Metric.ball x₀ ρ`,
then for every `x ∈ Ω` and `r < ρ` the closed convex hull of `insert x (Metric.ball x₀ r)` is
contained in `Ω`. -/
theorem closure_convexHull_insert_ball_subset_of_forall_starConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Ω : Set E} {x x₀ : E} {r ρ : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω) :
    closure (convexHull ℝ (insert x (ball x₀ r))) ⊆ Ω :=
  (isCompact_closedBall x₀ r).closure_convexHull_insert_subset_of_forall_starConvex
    (convex_closedBall x₀ r) ball_subset_closedBall hx
    fun y hy ↦ hstar y (closedBall_subset_ball hr hy)

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
