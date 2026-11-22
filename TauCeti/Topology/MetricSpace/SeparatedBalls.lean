/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Small closed balls around finitely many points are separated

Around finitely many points of a metric space, closed balls of a small enough common radius lie in
prescribed neighbourhoods of their centres and are pairwise far apart: the radius is less than
half the distance between any two distinct centres, so the balls are disjoint and no point of one
ball lies on the boundary sphere of another. This is the geometric input for splitting a sum over
points near the centres as a sum over the balls, as in the contour-integral computation of sums
over the roots of a polynomial.

## Main declarations

* `TauCeti.eventually_closedBall_subset_and_lt_dist`: every small enough common radius works for
  every centre at once.
* `TauCeti.exists_pos_closedBall_subset_and_lt_dist`: a positive common radius that is small
  enough for every centre at once.
* `TauCeti.eq_of_dist_lt_of_dist_lt`: two such centres within the radius of a common point
  coincide.
* `TauCeti.mem_and_apply_eq_of_surjOn_of_dist_lt`: a map moving the points of a separated set
  by less than the radius and onto a target is determined by the points of the target near the
  source points.

For a family `θ : ι → Y` of points of a pseudometric space with `2 s ≤ dist (θ i) (θ j)` for
`i ≠ j`, the open balls of radius `s` around them are pairwise disjoint, so a point of `Y` has a
well-defined ball index: `TauCeti.ballIndex θ s i₀ y` is the index of the ball containing `y`, and
the default `i₀` when `y` lies in no ball.

* `TauCeti.ballIndex_eq_iff`: `ballIndex θ s i₀ y = i` exactly when `y` lies in the ball around
  `θ i`, or `i = i₀` and `y` lies in no ball.
* `TauCeti.le_dist_of_ballIndex_ne`: a point whose ball index is not `i` is at distance at least
  `s` from `θ i`.
* `TauCeti.ballIndex_preimage`: the preimage of a set of indices.
-/

public section

open Filter Metric Set Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- Around finitely many points, closed balls of every small enough common radius lie in
prescribed neighbourhoods of their centres and are pairwise far apart: twice the radius is less
than the distance between any two distinct centres. -/
theorem eventually_closedBall_subset_and_lt_dist {T : Set X} (hT : T.Finite) {U : X → Set X}
    (hU : ∀ w ∈ T, U w ∈ 𝓝 w) :
    ∀ᶠ r in 𝓝 (0 : ℝ), (∀ w ∈ T, closedBall w r ⊆ U w) ∧
      ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, closedBall w r ⊆ U w :=
    (eventually_all_finite hT).2 fun w hw => eventually_closedBall_subset (hU w hw)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' :=
    (eventually_all_finite hT).2 fun w _ => (eventually_all_finite hT).2 fun w' _ =>
      eventually_imp_distrib_left.2 fun hww =>
        (eventually_lt_nhds (half_pos (dist_pos.2 hww))).mono fun _ _ => by linarith
  exact h1.and h2

/-- Around finitely many points, closed balls of a small enough common radius lie in prescribed
neighbourhoods of their centres and are pairwise far apart: twice the radius is less than the
distance between any two distinct centres. -/
theorem exists_pos_closedBall_subset_and_lt_dist {T : Finset X} {U : X → Set X}
    (hU : ∀ w ∈ T, U w ∈ 𝓝 w) :
    ∃ r > 0, (∀ w ∈ T, closedBall w r ⊆ U w) ∧ ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' :=
  (eventually_mem_nhdsWithin.and
    (nhdsWithin_le_nhds (eventually_closedBall_subset_and_lt_dist T.finite_toSet hU))).exists
    (f := 𝓝[>] 0)

/-- Two points that are either equal or more than `2 * r` apart are equal if both lie within `r`
of a common point. -/
theorem eq_of_dist_lt_of_dist_lt {Y : Type*} [PseudoMetricSpace Y] {w w' y : Y} {r : ℝ}
    (hsep : w ≠ w' → 2 * r < dist w w') (h : dist y w < r) (h' : dist y w' < r) : w = w' := by
  by_contra hne
  linarith [hsep hne, dist_triangle_left w w' y]

omit [MetricSpace X] in
/-- A map `e` from `A` onto `B` that moves each point of `A` by less than `r`, with `A` inside
a set `T` whose distinct points are more than `2 * r` apart, matches a point `w` of `B` lying
within `r` of a point `z` of `T` with `z`: then `z ∈ A` and `e z = w`. -/
theorem mem_and_apply_eq_of_surjOn_of_dist_lt [PseudoMetricSpace X] {A B T : Set X} {e : X → X}
    {r : ℝ} (hA : A ⊆ T) (he : Set.SurjOn e A B) (hsep : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * r < dist z w)
    (hclose : ∀ z ∈ A, dist (e z) z < r) {z w : X} (hz : z ∈ T) (hw : w ∈ B) (hwz : dist w z < r) :
    z ∈ A ∧ e z = w := by
  obtain ⟨z', hz', rfl⟩ := he hw
  obtain rfl : z = z' :=
    eq_of_dist_lt_of_dist_lt (hsep z hz z' (hA hz')) hwz (hclose z' hz')
  exact ⟨hz', rfl⟩

section BallIndex

variable {ι Y : Type*} [PseudoMetricSpace Y]

open scoped Classical in
/-- The index of the open ball of radius `s` around a point `θ i` that contains `y`, and `i₀`
when `y` lies in no such ball. For `2 s`-separated points the balls are pairwise disjoint, so the
index is unique (`TauCeti.ballIndex_eq_of_mem_ball`). -/
noncomputable def ballIndex (θ : ι → Y) (s : ℝ) (i₀ : ι) (y : Y) : ι :=
  if h : ∃ i, y ∈ ball (θ i) s then h.choose else i₀

/-- For `2 s`-separated points, the open balls of radius `s` around them meet only when they are
equal. -/
private theorem eq_of_mem_ball_of_mem_ball {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) {y : Y} {i j : ι}
    (hi : y ∈ ball (θ i) s) (hj : y ∈ ball (θ j) s) : i = j := by
  by_contra hij
  exact (ball_disjoint_ball (by linarith [hθ i j hij])).ne_of_mem hi hj rfl

/-- A point in the ball around `θ i` has index `i`. -/
theorem ballIndex_eq_of_mem_ball {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) {y : Y} {i : ι}
    (hy : y ∈ ball (θ i) s) : ballIndex θ s i₀ y = i := by
  have h : ∃ j, y ∈ ball (θ j) s := ⟨i, hy⟩
  rw [ballIndex, dite_eq_left h]
  exact eq_of_mem_ball_of_mem_ball hθ h.choose_spec hy

/-- A point in no ball has the default index. -/
@[simp]
theorem ballIndex_eq_of_forall_notMem {θ : ι → Y} {s : ℝ} (i₀ : ι) {y : Y}
    (hy : ∀ i, y ∉ ball (θ i) s) : ballIndex θ s i₀ y = i₀ := by
  rw [ballIndex, dite_eq_right (by simpa using hy)]

/-- For `2 s`-separated points, `ballIndex θ s i₀ y = i` exactly when `y` lies in the ball of
radius `s` around `θ i`, or `i` is the default index `i₀` and `y` lies in no ball. -/
@[simp]
theorem ballIndex_eq_iff {θ : ι → Y} {s : ℝ} (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    {i₀ : ι} {y : Y} {i : ι} :
    ballIndex θ s i₀ y = i ↔ y ∈ ball (θ i) s ∨ i = i₀ ∧ ∀ j, y ∉ ball (θ j) s := by
  by_cases hy : ∃ j, y ∈ ball (θ j) s
  · obtain ⟨j, hj⟩ := hy
    rw [ballIndex_eq_of_mem_ball hθ i₀ hj]
    refine ⟨fun h ↦ .inl (h ▸ hj), ?_⟩
    rintro (hi | ⟨-, hno⟩)
    · exact eq_of_mem_ball_of_mem_ball hθ hj hi
    · exact (hno j hj).elim
  · push Not at hy
    simp [hy, eq_comm]

/-- For `2 s`-separated points, a point whose index is not `i` is at distance at least `s`
from `θ i`. -/
theorem le_dist_of_ballIndex_ne {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) {i₀ : ι} {y : Y} {i : ι}
    (h : ballIndex θ s i₀ y ≠ i) : s ≤ dist y (θ i) :=
  not_lt.1 fun hy ↦ h (ballIndex_eq_of_mem_ball hθ i₀ (mem_ball.2 hy))

/-- For `2 s`-separated points, the preimage of a set `A` of indices under `ballIndex` is the
union of the balls with index in `A`, together with the complement of all balls when `i₀ ∈ A`. -/
theorem ballIndex_preimage {θ : ι → Y} {s : ℝ} (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    (i₀ : ι) (A : Set ι) :
    ballIndex θ s i₀ ⁻¹' A =
      (⋃ i ∈ A, ball (θ i) s) ∪ ({_y | i₀ ∈ A} ∩ ⋂ i, (ball (θ i) s)ᶜ) := by
  ext y
  by_cases hy : ∃ i, y ∈ ball (θ i) s
  · obtain ⟨i, hi⟩ := hy
    simp only [mem_preimage, ballIndex_eq_of_mem_ball hθ i₀ hi, mem_union, mem_iUnion₂,
      mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    refine ⟨fun hA ↦ .inl ⟨i, hA, hi⟩, ?_⟩
    rintro (⟨j, hj, hyj⟩ | ⟨-, hy⟩)
    · rwa [eq_of_mem_ball_of_mem_ball hθ hi hyj]
    · exact (hy i hi).elim
  · push Not at hy
    simp [hy]

end BallIndex

end TauCeti

end
