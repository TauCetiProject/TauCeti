/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
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

For a separable subset of a pseudometric space, any family mapping a set into it with pairwise
distances bounded below by a positive constant is countable
(`TopologicalSpace.IsSeparable.countable_of_mapsTo_of_le_dist`).

## Main declarations

* `TauCeti.exists_pos_closedBall_subset_and_lt_dist`: a common radius that is small enough for
  every centre at once.
* `TauCeti.eq_of_dist_lt_of_dist_lt`: two such centres within the radius of a common point
  coincide.
* `TauCeti.mem_and_apply_eq_of_surjOn_of_dist_lt`: a map moving the points of a separated set
  by less than the radius and onto a target is determined by the points of the target near the
  source points.
* `TopologicalSpace.IsSeparable.countable_of_mapsTo_of_le_dist`: a family mapping into a
  separable set with positive uniform separation is countable.
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
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' :=
    (eventually_all_finset T).2 fun w _ => (eventually_all_finset T).2 fun w' _ =>
      eventually_imp_distrib_left.2 fun hww =>
        (eventually_lt_nhds (half_pos (dist_pos.2 hww))).mono fun _ _ => by linarith
  exact (eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (h1.and h2))).exists (f := 𝓝[>] 0)

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

/-- Any family of points mapping into a separable subset of a pseudometric space whose distinct
images are separated by at least `r > 0` has a countable domain. -/
theorem _root_.TopologicalSpace.IsSeparable.countable_of_mapsTo_of_le_dist
    {ι Y : Type*} [PseudoMetricSpace Y] {t : Set Y} (ht : TopologicalSpace.IsSeparable t)
    {s : Set ι} {u : ι → Y} (hmaps : Set.MapsTo u s t) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r ≤ dist (u i) (u j)) :
    s.Countable := by
  obtain ⟨D, hD_count, hDt⟩ := ht
  have hex : ∀ i : s, ∃ d : D, dist (u i.val) d.val < r / 2 := fun i => by
    obtain ⟨d, hdD, hdist'⟩ :=
      Metric.mem_closure_iff.1 (hDt (hmaps i.property)) (r / 2) (half_pos hr)
    exact ⟨⟨d, hdD⟩, hdist'⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := fun i j hij => by
    by_contra hne
    have h1 := hdist i.val i.property j.val j.property (Subtype.coe_ne_coe.2 hne)
    have h2 : dist (u i.val) (u j.val) < r := by
      calc dist (u i.val) (u j.val)
          ≤ dist (u i.val) (φ i).val + dist (φ i).val (u j.val) := dist_triangle _ _ _
        _ = dist (u i.val) (φ i).val + dist (u j.val) (φ j).val := by
            rw [hij, dist_comm (φ j).val]
        _ < r / 2 + r / 2 := add_lt_add (hφ i) (hφ j)
        _ = r := add_halves r
    exact h2.not_ge h1
  have : Countable D := hD_count.to_subtype
  exact hinj.countable.to_set

end TauCeti

end
