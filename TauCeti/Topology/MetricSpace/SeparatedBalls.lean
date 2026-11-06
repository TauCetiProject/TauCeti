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

* `TauCeti.exists_pos_closedBall_subset_and_lt_dist`: a common radius that is small enough for
  every centre at once.
* `TauCeti.eq_of_dist_lt_of_dist_lt`: two such centres within the radius of a common point
  coincide.
* `TauCeti.mem_and_apply_eq_of_bijOn_of_dist_lt`: a bijection moving the points of a separated set
  by less than the radius is determined by the points of the target near the source points.
-/

public section

open Filter Metric Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- Around finitely many points, closed balls of a small enough common radius lie in prescribed
neighbourhoods of their centres and are pairwise far apart: twice the radius is less than the
distance between any two distinct centres. -/
theorem exists_pos_closedBall_subset_and_lt_dist {T : Finset X} {U : X → Set X}
    (hU : ∀ w ∈ T, U w ∈ 𝓝 w) :
    ∃ r > 0, (∀ w ∈ T, closedBall w r ⊆ U w) ∧ ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, closedBall w r ⊆ U w :=
    (eventually_all_finset T).2 fun w hw => eventually_closedBall_subset (hU w hw)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
    refine (eventually_all_finset T).2 fun w _ => (eventually_all_finset T).2 fun w' _ => ?_
    by_cases hww : w = w'
    · exact Eventually.of_forall fun _ h => absurd hww h
    · exact (eventually_lt_nhds (half_pos (dist_pos.2 hww))).mono fun r hr _ => by linarith
  obtain ⟨r, ⟨h1r, h2r⟩, hr⟩ :=
    (((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
      (f := 𝓝[>] (0 : ℝ))
  exact ⟨r, hr, h1r, h2r⟩

/-- Two points that are either equal or more than `2 * r` apart are equal if both lie within `r`
of a common point. -/
theorem eq_of_dist_lt_of_dist_lt {Y : Type*} [PseudoMetricSpace Y] {w w' y : Y} {r : ℝ}
    (hsep : w ≠ w' → 2 * r < dist w w') (h : dist y w < r) (h' : dist y w' < r) : w = w' := by
  by_contra hne
  linarith [hsep hne, dist_triangle_left w w' y]

/-- A bijection `e` from `A` onto `B` that moves each point of `A` by less than `r`, with `A` inside
a set `T` whose distinct points are more than `2 * r` apart, matches a point `w` of `B` lying
within `r` of a point `z` of `T` with `z`: then `z ∈ A` and `e z = w`. -/
theorem mem_and_apply_eq_of_bijOn_of_dist_lt {A B T : Set X} {e : X → X} {r : ℝ} (hA : A ⊆ T)
    (he : Set.BijOn e A B) (hsep : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * r < dist z w)
    (hclose : ∀ z ∈ A, dist (e z) z < r) {z w : X} (hz : z ∈ T) (hw : w ∈ B) (hwz : dist w z < r) :
    z ∈ A ∧ e z = w := by
  obtain ⟨z', hz', rfl⟩ := he.surjOn hw
  obtain rfl : z = z' :=
    eq_of_dist_lt_of_dist_lt (hsep z hz z' (hA hz')) hwz (hclose z' hz')
  exact ⟨hz', rfl⟩

end TauCeti

end
