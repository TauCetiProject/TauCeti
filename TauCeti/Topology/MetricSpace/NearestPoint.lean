/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Isolating a nearest point

A finite search in a closed ball gives an open ball about the same centre that contains the
nearest point but no competitors.
-/

public section

open Metric Set

/-- If `S` has finitely many points in `closedBall c R`, and `p ∈ S` lies strictly inside that
ball and strictly closer to `c` than every other such point, then some open ball `ball c r` with
`dist p c < r ≤ R` meets `S` only in `p`. -/
theorem Set.Finite.exists_inter_ball_eq_singleton_of_forall_dist_lt {X : Type*}
    [PseudoMetricSpace X] {S : Set X} {c p : X} {R : ℝ} (hS : (S ∩ closedBall c R).Finite)
    (hp : p ∈ S) (hd : dist p c < R)
    (hlt : ∀ q ∈ S ∩ closedBall c R, q ≠ p → dist p c < dist q c) :
    ∃ r, dist p c < r ∧ r ≤ R ∧ S ∩ ball c r = {p} := by
  let T := (S ∩ closedBall c R) \ {p}
  have hT : T.Finite := hS.sdiff
  have hgap : ∃ r, dist p c < r ∧ r ≤ R ∧ ∀ q ∈ T, r ≤ dist q c := by
    obtain h | h := T.eq_empty_or_nonempty
    · exact ⟨R, hd, le_rfl, by simp [h]⟩
    · obtain ⟨q, hq, hmin⟩ := T.exists_min_image (dist · c) hT h
      exact ⟨min R (dist q c), lt_min hd (hlt q hq.1 hq.2), min_le_left ..,
        fun w hw ↦ (min_le_right ..).trans (hmin w hw)⟩
  obtain ⟨r, hr, hrR, hav⟩ := hgap
  refine ⟨r, hr, hrR, eq_singleton_iff_unique_mem.mpr ⟨⟨hp, hr⟩, ?_⟩⟩
  intro q hq
  by_contra hne
  exact (not_lt_of_ge (hav q ⟨⟨hq.1, ball_subset_closedBall (ball_subset_ball hrR hq.2)⟩, hne⟩))
    (mem_ball.mp hq.2)
