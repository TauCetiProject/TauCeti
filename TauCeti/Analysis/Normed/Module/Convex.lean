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

In a nontrivial real seminormed space a punctured ball `ball c r \ {c}`, `r > 0`, is not convex
(`TauCeti.not_convex_ball_sdiff_singleton`), so it is neither an open nor a closed ball
(`TauCeti.ball_sdiff_singleton_ne_ball`, `TauCeti.ball_sdiff_singleton_ne_closedBall`), although it
agrees with `ball c r` up to a null set for every measure without atoms.
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

namespace TauCeti

open Metric Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {r : ℝ}

/-- **A punctured ball is not convex.** In a nontrivial real seminormed space, a ball of positive
radius with its centre removed is not convex: the centre is the midpoint of two of its points. -/
theorem not_convex_ball_sdiff_singleton (c : E) (hr : 0 < r) : ¬Convex ℝ (ball c r \ {c}) := by
  -- For a small multiple `w ≠ 0` of a nonzero vector, the points `c ± w` lie in the punctured
  -- ball, and their midpoint `c` does not.
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set t := r / (2 * (‖v‖ + 1))
  have ht : 0 < t := by positivity
  have hw : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hw0 : t • v ≠ 0 := smul_ne_zero ht.ne' hv
  have hmem {w : E} (hw : ‖w‖ < r) (hw0 : w ≠ 0) : c + w ∈ ball c r \ {c} :=
    ⟨by rwa [mem_ball, dist_self_add_left], by simpa using hw0⟩
  intro hconv
  refine (hconv (hmem hw hw0) (hmem (by rwa [norm_neg]) (neg_ne_zero.2 hw0))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).2 ?_
  rw [mem_singleton_iff]
  module

/-- In a nontrivial real seminormed space, a punctured ball of positive radius is not a ball. -/
theorem ball_sdiff_singleton_ne_ball (c : E) (hr : 0 < r) (c' : E) (r' : ℝ) :
    ball c r \ {c} ≠ ball c' r' :=
  fun h => not_convex_ball_sdiff_singleton c hr (h ▸ convex_ball c' r')

/-- In a nontrivial real seminormed space, a punctured ball of positive radius is not a closed
ball. -/
theorem ball_sdiff_singleton_ne_closedBall (c : E) (hr : 0 < r) (c' : E) (r' : ℝ) :
    ball c r \ {c} ≠ closedBall c' r' :=
  fun h => not_convex_ball_sdiff_singleton c hr (h ▸ convex_closedBall c' r')

end TauCeti
