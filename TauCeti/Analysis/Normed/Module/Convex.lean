/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closed convex hulls and convex sets containing a ball

Taking the closed convex hull of a set in a real seminormed space preserves both boundedness and
diameter. These are the closed-hull counterparts of `isBounded_convexHull` and `convexHull_diam`.
A norm bound `‖T x‖ ≤ r` for a continuous linear map on a set extends to its closed real convex
hull (`ContinuousLinearMap.norm_le_of_mem_closure_convexHull`).

A set that is star-convex with respect to every point of `ball x r` sends every point `y` of its
closure into its interior along the segment toward `x`: the ball of radius `(1 - t) * r` about
`x + t • (y - x)` lies in `interior s` for every `0 ≤ t ≤ 1`
(`TauCeti.ball_add_smul_sub_subset_interior_of_forall_starConvex`), and for `z` within `r / 2` of
`y` the translated closed ball `closedBall (y + t • (x - z)) (t * (r / 2))` lies in `interior s`
for `0 < t ≤ 1` (`TauCeti.closedBall_add_smul_sub_subset_interior_of_forall_starConvex`); when a
set `K` has its closed `δ`-thickening inside `ball z (r / 2)` and `t * (dist x z + r / 2) ≤ δ`,
that translated closed ball either lies in `interior s` or is disjoint from `K`
(`TauCeti.closedBall_add_smul_sub_subset_interior_or_disjoint_of_forall_starConvex`). For a
convex set containing `ball x r`, this yields `Convex.ball_add_smul_sub_subset`.

Replacing every member of a filter by its real convex hull preserves limits of real-linear maps
into real seminormed spaces (`Filter.Tendsto.lift'_convexHull`).

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

/-- If `s` is star-convex with respect to every point of `ball x r`, then for every
`y ∈ closure s` and `0 ≤ t ≤ 1` the ball of radius `(1 - t) * r` about `x + t • (y - x)` lies in
`interior s`. -/
theorem ball_add_smul_sub_subset_interior_of_forall_starConvex {s : Set E} {x y : E} {r t : ℝ}
    (hs : ∀ w ∈ ball x r, StarConvex ℝ w s) (hy : y ∈ closure s) (ht₀ : 0 ≤ t) (ht : t ≤ 1) :
    ball (x + t • (y - x)) ((1 - t) * r) ⊆ interior s := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  intro p hp
  rw [mem_ball] at hp
  have h1t : 0 < 1 - t := sub_pos.2 ht
  set d := dist p (x + t • (y - x))
  set ε := ((1 - t) * r - d) / (2 * (1 + t))
  have hε : 0 < ε := div_pos (sub_pos.2 hp) (by linarith)
  obtain ⟨y', hy's, hyy'⟩ := Metric.mem_closure_iff.1 hy ε hε
  refine mem_interior.2 ⟨ball p ε, fun q hq => ?_, isOpen_ball, mem_ball_self hε⟩
  rw [mem_ball] at hq
  -- Express `q` as `(1 - t) • z + t • y'` with `z ∈ ball x r`.
  let z := x + (1 - t)⁻¹ • ((q - p) + (p - (x + t • (y - x))) + t • (y - y'))
  have hz : z ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv,
      Real.norm_of_nonneg h1t.le, inv_mul_lt_iff₀ h1t]
    have hle : ‖(q - p) + (p - (x + t • (y - x))) + t • (y - y')‖ ≤
        dist q p + d + t * dist y y' := by
      refine norm_add₃_le.trans (le_of_eq ?_)
      rw [← dist_eq_norm, ← dist_eq_norm, norm_smul, Real.norm_of_nonneg ht₀, ← dist_eq_norm]
    have hε_eq : (1 + t) * ε = ((1 - t) * r - d) / 2 := by
      simp only [ε]
      field_simp
    linarith [mul_le_mul_of_nonneg_left hyy'.le ht₀]
  convert hs z hz hy's h1t.le ht₀ (by ring) using 1
  rw [smul_add, smul_smul, mul_inv_cancel₀ h1t.ne', one_smul]
  module

/-- If `s` is star-convex with respect to every point of `ball x r`, then for every
`y ∈ closure s`, every `z` with `dist y z < r / 2`, and every `0 < t ≤ 1`, the translated closed
ball `closedBall (y + t • (x - z)) (t * (r / 2))` lies in `interior s`. -/
theorem closedBall_add_smul_sub_subset_interior_of_forall_starConvex {s : Set E} {x y z : E}
    {r t : ℝ} (hs : ∀ w ∈ ball x r, StarConvex ℝ w s) (hy : y ∈ closure s)
    (hz : dist y z < r / 2) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    closedBall (y + t • (x - z)) (t * (r / 2)) ⊆ interior s := by
  refine Subset.trans (fun q hq => ?_)
    (ball_add_smul_sub_subset_interior_of_forall_starConvex hs hy (sub_nonneg.2 ht₁) (by linarith))
  rw [mem_closedBall] at hq
  rw [mem_ball]
  have hcenter : dist (y + t • (x - z)) (x + (1 - t) • (y - x)) = t * dist y z := by
    have hsub : (y + t • (x - z)) - (x + (1 - t) • (y - x)) = t • (y - z) := by module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg ht₀.le, ← dist_eq_norm]
  calc dist q (x + (1 - t) • (y - x))
      ≤ dist q (y + t • (x - z)) + dist (y + t • (x - z)) (x + (1 - t) • (y - x)) :=
        dist_triangle _ _ _
    _ < t * (r / 2) + t * (r / 2) := by
        linarith [mul_lt_mul_of_pos_left hz ht₀]
    _ = (1 - (1 - t)) * r := by ring

/-- If `s` is star-convex with respect to every point of `ball x r` and `cthickening δ K` lies in
`ball z (r / 2)`, then for every `y ∈ closure s` and every `0 < t ≤ 1` with
`t * (dist x z + r / 2) ≤ δ`, the translated closed ball
`closedBall (y + t • (x - z)) (t * (r / 2))` either lies in `interior s` or is disjoint from `K`. -/
theorem closedBall_add_smul_sub_subset_interior_or_disjoint_of_forall_starConvex {s : Set E}
    {x y z : E} {r δ t : ℝ} (hs : ∀ w ∈ ball x r, StarConvex ℝ w s)
    (hKB : cthickening δ K ⊆ ball z (r / 2)) (ht₀ : 0 < t) (ht₁ : t ≤ 1)
    (htδ : t * (dist x z + r / 2) ≤ δ) (hy : y ∈ closure s) :
    closedBall (y + t • (x - z)) (t * (r / 2)) ⊆ interior s ∨
      Disjoint (closedBall (y + t • (x - z)) (t * (r / 2))) K := by
  by_cases hdis : Disjoint (closedBall (y + t • (x - z)) (t * (r / 2))) K
  · exact Or.inr hdis
  left
  obtain ⟨q, hqB, hqK⟩ := not_disjoint_iff.1 hdis
  rw [mem_closedBall] at hqB
  have hshift : dist y (y + t • (x - z)) = t * dist x z := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht₀.le,
      ← dist_eq_norm]
  have hyq : dist y q ≤ δ :=
    calc dist y q
        ≤ dist y (y + t • (x - z)) + dist (y + t • (x - z)) q := dist_triangle _ _ _
      _ ≤ t * dist x z + t * (r / 2) := by
          rw [dist_comm _ q]
          exact add_le_add hshift.le hqB
      _ = t * (dist x z + r / 2) := (mul_add _ _ _).symm
      _ ≤ δ := htδ
  have hyz : dist y z < r / 2 := mem_ball.1 (hKB (mem_cthickening_of_dist_le y q δ K hqK hyq))
  exact closedBall_add_smul_sub_subset_interior_of_forall_starConvex hs hy hyz ht₀ ht₁

end TauCeti

/-- A norm bound `‖T x‖ ≤ r` for a continuous linear map on a set `s` extends to the closed real
convex hull `closure (convexHull ℝ s)`. -/
theorem ContinuousLinearMap.norm_le_of_mem_closure_convexHull
    {𝕜 E F : Type*} [Semiring 𝕜] [SMul ℝ 𝕜]
    [AddCommMonoid E] [TopologicalSpace E] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    (T : E →L[𝕜] F) {s : Set E} {r : ℝ} (hs : ∀ x ∈ s, ‖T x‖ ≤ r)
    {x : E} (hx : x ∈ closure (convexHull ℝ s)) : ‖T x‖ ≤ r := by
  have hsub : closure (convexHull ℝ s) ⊆
      (T.toLinearMap.restrictScalars ℝ) ⁻¹' Metric.closedBall 0 r :=
    closure_minimal
      (convexHull_min (fun y hy ↦ by simpa using hs y hy)
        ((convex_closedBall (0 : F) r).linear_preimage _))
      (Metric.isClosed_closedBall.preimage T.continuous)
  simpa using hsub hx

/-- A convex set containing the ball `ball x r` and a point `y` contains the ball of radius
`(1 - t) * r` about `x + t • (y - x)` for every `0 ≤ t ≤ 1`. -/
theorem Convex.ball_add_smul_sub_subset {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) {x y : E} {r t : ℝ} (hball : Metric.ball x r ⊆ s) (hy : y ∈ s)
    (ht₀ : 0 ≤ t) (ht : t ≤ 1) : Metric.ball (x + t • (y - x)) ((1 - t) * r) ⊆ s :=
  (TauCeti.ball_add_smul_sub_subset_interior_of_forall_starConvex
    (fun _ hz => hs.starConvex (hball hz)) (subset_closure hy) ht₀ ht).trans interior_subset

/-- If an `ℝ`-linear map `f` into a real seminormed space tends to `y` along `l`, then it still
tends to `y` along the real convexification `l.lift' (convexHull ℝ)`. -/
theorem Filter.Tendsto.lift'_convexHull {B E : Type*} [AddCommMonoid B] [Module ℝ B]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter B} {f : B →ₗ[ℝ] E} {y : E}
    (h : Filter.Tendsto f l (nhds y)) :
    Filter.Tendsto f (l.lift' (convexHull ℝ)) (nhds y) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  exact Filter.eventually_of_mem (Filter.mem_lift' (h ε hε)) fun _ hx =>
    convexHull_min subset_rfl ((convex_ball y ε).linear_preimage f) hx

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
