/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Order.Compact

/-!
# Small closed balls around finitely many points are separated

Around finitely many points of a metric space, closed balls of a small enough common radius lie in
prescribed neighbourhoods of their centres and are pairwise far apart: the radius is less than
half the distance between any two distinct centres, so the balls are disjoint and no point of one
ball lies on the boundary sphere of another. This is the geometric input for splitting a sum over
points near the centres as a sum over the balls, as in the contour-integral computation of sums
over the roots of a polynomial.

In a proper pseudometric space, a finite family of pairwise disjoint closed balls of radius `r`
lying in prescribed open sets can likewise be enlarged to a strictly larger common radius `r' > r`
preserving both containment and pairwise disjointness.

## Main declarations

* `TauCeti.exists_pos_closedBall_subset_and_lt_dist`: a common radius that is small enough for
  every centre at once.
* `TauCeti.eq_of_dist_lt_of_dist_lt`: two such centres within the radius of a common point
  coincide.
* `TauCeti.mem_and_apply_eq_of_surjOn_of_dist_lt`: a map moving the points of a separated set
  by less than the radius and onto a target is determined by the points of the target near the
  source points.
* `IsOpen.exists_gt_closedBall_subset`: in a proper pseudometric space, a closed ball contained in
  an open set remains inside it for a strictly larger radius.
* `Disjoint.exists_gt_closedBall`: in a proper pseudometric space, two disjoint closed balls of
  equal radius remain disjoint for a strictly larger radius.
* `TauCeti.exists_gt_closedBall_subset_and_pairwiseDisjoint`: in a proper pseudometric space, a
  finite pairwise-disjoint family of closed balls of common radius inside open sets admits a
  strictly larger common radius with the same properties.
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

section ProperSpace

variable {Y : Type*} [PseudoMetricSpace Y] [ProperSpace Y]

/-- In a proper pseudometric space, if a closed ball `closedBall x r` is contained in an open set
`U`, then `closedBall x r' ⊆ U` for some strictly larger radius `r' > r`. -/
theorem _root_.IsOpen.exists_gt_closedBall_subset {x : Y} {r : ℝ} {U : Set Y} (hU : IsOpen U)
    (hsub : closedBall x r ⊆ U) : ∃ r' > r, closedBall x r' ⊆ U := by
  let K : Set Y := closedBall x (r + 1) \ U
  rcases K.eq_empty_or_nonempty with hK | hK
  · exact ⟨r + 1, by linarith, Set.sdiff_eq_empty.1 hK⟩
  have hcomp : IsCompact K := (isCompact_closedBall x (r + 1)).diff hU
  obtain ⟨y, hyK, hymin⟩ :=
    hcomp.exists_isMinOn hK (continuous_id.dist continuous_const).continuousOn
  have hlt : r < dist y x := not_le.1 fun hle ↦ hyK.2 (hsub hle)
  refine ⟨min (r + 1) ((r + dist y x) / 2), lt_min (by linarith) (by linarith), fun z hz ↦ ?_⟩
  by_contra hzU
  have hzK : z ∈ K := ⟨closedBall_subset_closedBall (min_le_left _ _) hz, hzU⟩
  have hle : dist y x ≤ dist z x := hymin hzK
  have hzr : dist z x ≤ (r + dist y x) / 2 := (mem_closedBall.1 hz).trans (min_le_right _ _)
  linarith

/-- In a proper pseudometric space, two disjoint closed balls of the same radius `r` remain
disjoint for some strictly larger radius `r' > r`. -/
theorem _root_.Disjoint.exists_gt_closedBall {x y : Y} {r : ℝ}
    (hdisj : Disjoint (closedBall x r) (closedBall y r)) :
    ∃ r' > r, Disjoint (closedBall x r') (closedBall y r') := by
  let K : Set Y := closedBall x (r + 1) ∩ closedBall y (r + 1)
  rcases K.eq_empty_or_nonempty with hK | hK
  · exact ⟨r + 1, by linarith, Set.disjoint_iff_inter_eq_empty.2 hK⟩
  have hcomp : IsCompact K := (isCompact_closedBall x (r + 1)).inter_right isClosed_closedBall
  have hcont : Continuous fun z : Y ↦ max (dist z x) (dist z y) :=
    (continuous_id.dist continuous_const).max (continuous_id.dist continuous_const)
  obtain ⟨z₀, _, hz₀min⟩ := hcomp.exists_isMinOn hK hcont.continuousOn
  have hlt : r < max (dist z₀ x) (dist z₀ y) := not_le.1 fun hle ↦
    Set.disjoint_left.1 hdisj ((le_max_left _ _).trans hle) ((le_max_right _ _).trans hle)
  refine ⟨min (r + 1) ((r + max (dist z₀ x) (dist z₀ y)) / 2), lt_min (by linarith) (by linarith),
    Set.disjoint_left.2 fun z hzx hzy ↦ ?_⟩
  have hzK : z ∈ K :=
    ⟨closedBall_subset_closedBall (min_le_left _ _) hzx,
      closedBall_subset_closedBall (min_le_left _ _) hzy⟩
  have hle : max (dist z₀ x) (dist z₀ y) ≤ max (dist z x) (dist z y) := hz₀min hzK
  have hzr : max (dist z x) (dist z y) ≤ (r + max (dist z₀ x) (dist z₀ y)) / 2 :=
    max_le ((mem_closedBall.1 hzx).trans (min_le_right _ _))
      ((mem_closedBall.1 hzy).trans (min_le_right _ _))
  linarith

/-- In a proper pseudometric space, a finite pairwise-disjoint family of closed balls of common
radius `r` lying in prescribed open sets can be enlarged to a strictly larger common radius
`r' > r` preserving both containment and pairwise disjointness. -/
theorem exists_gt_closedBall_subset_and_pairwiseDisjoint {T : Finset Y} {U : Y → Set Y} {r : ℝ}
    (hU : ∀ w ∈ T, IsOpen (U w)) (hsub : ∀ w ∈ T, closedBall w r ⊆ U w)
    (hdisj : (T : Set Y).Pairwise fun w w' ↦ Disjoint (closedBall w r) (closedBall w' r)) :
    ∃ r' > r, (∀ w ∈ T, closedBall w r' ⊆ U w) ∧
      (T : Set Y).Pairwise fun w w' ↦ Disjoint (closedBall w r') (closedBall w' r') := by
  have h1 : ∀ᶠ r' in 𝓝[>] r, ∀ w ∈ T, closedBall w r' ⊆ U w := by
    rw [eventually_all_finset]
    intro w hw
    obtain ⟨r₁, hr₁, hsub₁⟩ := (hU w hw).exists_gt_closedBall_subset (hsub w hw)
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hr₁)] with r' hr'
    exact (closedBall_subset_closedBall hr'.le).trans hsub₁
  have h2 : ∀ᶠ r' in 𝓝[>] r,
      (T : Set Y).Pairwise fun w w' ↦ Disjoint (closedBall w r') (closedBall w' r') := by
    simp only [Set.Pairwise, Finset.mem_coe, eventually_all_finset]
    intro w hw w' hw'
    rw [eventually_imp_distrib_left]
    intro hne
    obtain ⟨r₁, hr₁, hdisj₁⟩ := (hdisj hw hw' hne).exists_gt_closedBall
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hr₁)] with r' hr'
    exact hdisj₁.mono (closedBall_subset_closedBall hr'.le) (closedBall_subset_closedBall hr'.le)
  exact (eventually_mem_nhdsWithin.and (h1.and h2)).exists

end ProperSpace

end TauCeti

end
