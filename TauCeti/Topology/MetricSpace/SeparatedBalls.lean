/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Basic

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
* `TauCeti.eq_of_mem_closedBall_of_lt_dist`: a centre within the radius of another coincides
  with it.
* `TauCeti.exists_pos_ball_subset_and_ball_sdiff_singleton_subset_sdiff`: small punctured balls
  about a point of an open set lie in it and avoid a given finite set.
* `TauCeti.mem_and_apply_eq_of_surjOn_of_dist_lt`: a map moving the points of a separated set
  by less than the radius and onto a target is determined by the points of the target near the
  source points.

For a family `θ : ι → Y` of points of a pseudometric space with `2 s ≤ dist (θ i) (θ j)` for
`i ≠ j`, the open balls of radius `s` around them are pairwise disjoint, so a point of `Y` has a
well-defined ball index: `TauCeti.ballIndex θ s i₀ y` is the index of the ball containing `y`, and
the default `i₀` when `y` lies in no ball.

* `TauCeti.pairwise_disjoint_ball_of_two_mul_le_dist`: the balls are pairwise disjoint.
* `TauCeti.mem_ball_ballIndex`: with no separation hypothesis, a point lying in some ball lies in
  the ball of its index.
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

/-- A point within `r` of `z` is `z` itself if it is either equal to `z` or more than `2 * r` away
from it. -/
theorem eq_of_mem_closedBall_of_lt_dist {Y : Type*} [PseudoMetricSpace Y] {w z : Y} {r : ℝ}
    (hsep : w ≠ z → 2 * r < dist w z) (h : w ∈ closedBall z r) : w = z := by
  by_contra hne
  linarith [hsep hne, mem_closedBall.1 h, dist_nonneg (x := w) (y := z)]

/-- About a point `z` of an open set `Ω`, small balls lie in `Ω` and, punctured at `z`, avoid a
finite set `Z`. -/
theorem exists_pos_ball_subset_and_ball_sdiff_singleton_subset_sdiff {Ω Z : Set X} {z : X}
    (hΩ : IsOpen Ω) (hZ : Z.Finite) (hz : z ∈ Ω) :
    ∃ r > 0, ball z r ⊆ Ω ∧ ball z r \ {z} ⊆ Ω \ Z := by
  obtain ⟨r, hr, hrsub⟩ := isOpen_iff.1
    (hΩ.inter (hZ.sdiff (t := {z})).isClosed.isOpen_compl) z ⟨hz, fun h ↦ h.2 rfl⟩
  exact ⟨r, hr, fun y hy ↦ (hrsub hy).1,
    fun y hy ↦ ⟨(hrsub hy.1).1, fun hyZ ↦ (hrsub hy.1).2 ⟨hyZ, hy.2⟩⟩⟩

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

open Function in
/-- For `2 s`-separated points `θ i`, the open balls of radius `s` around them are pairwise
disjoint. -/
theorem pairwise_disjoint_ball_of_two_mul_le_dist {ι Y : Type*} [PseudoMetricSpace Y]
    {θ : ι → Y} {s : ℝ} (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) :
    Pairwise (Disjoint on fun i ↦ ball (θ i) s) :=
  fun i j hij ↦ ball_disjoint_ball (by linarith [hθ i j hij])

section BallIndex

variable {ι Y : Type*} [PseudoMetricSpace Y]

/-- The index of the open ball of radius `s` around a point `θ i` that contains `y`, and `i₀`
when `y` lies in no such ball: the extension (`Function.extend`) of the index projection
`Σ i, ball (θ i) s → ι` along the point projection `Σ i, ball (θ i) s → Y`, with the constant
default `i₀`. For `2 s`-separated points the balls are pairwise disjoint, so the index is unique
(`TauCeti.ballIndex_eq_of_mem_ball`); in general it is the index of some ball containing `y`
(`TauCeti.mem_ball_ballIndex`). -/
noncomputable def ballIndex (θ : ι → Y) (s : ℝ) (i₀ : ι) (y : Y) : ι :=
  Function.extend (fun p : Σ i, ball (θ i) s ↦ (p.2 : Y)) Sigma.fst (fun _ ↦ i₀) y

/-- A point lying in some ball lies in the ball of its index, with no separation hypothesis. -/
theorem mem_ball_ballIndex {θ : ι → Y} {s : ℝ} (i₀ : ι) {y : Y} (h : ∃ i, y ∈ ball (θ i) s) :
    y ∈ ball (θ (ballIndex θ s i₀ y)) s := by
  classical
  obtain ⟨i, hi⟩ := h
  have h' : ∃ p : Σ i, ball (θ i) s, (p.2 : Y) = y := ⟨⟨i, y, hi⟩, rfl⟩
  rw [ballIndex, Function.extend_def, dite_eq_left h']
  have := (Classical.choose h').2.property
  rwa [Classical.choose_spec h'] at this

/-- A point in the ball around `θ i` has index `i`. -/
theorem ballIndex_eq_of_mem_ball {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) {y : Y} {i : ι}
    (hy : y ∈ ball (θ i) s) : ballIndex θ s i₀ y = i :=
  (Subtype.val_injective.comp (Set.sigmaToiUnion_injective _
    (pairwise_disjoint_ball_of_two_mul_le_dist hθ))).extend_apply _ _ ⟨i, y, hy⟩

/-- A point in no ball has the default index. -/
@[simp]
theorem ballIndex_eq_of_forall_notMem {θ : ι → Y} {s : ℝ} (i₀ : ι) {y : Y}
    (hy : ∀ i, y ∉ ball (θ i) s) : ballIndex θ s i₀ y = i₀ :=
  Function.extend_apply' _ _ _ fun ⟨⟨i, _, hi⟩, h⟩ ↦ hy i (h ▸ hi)

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
    · exact (ballIndex_eq_of_mem_ball hθ i₀ hj).symm.trans (ballIndex_eq_of_mem_ball hθ i₀ hi)
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
  rw [← biUnion_preimage_singleton]
  ext y
  simp only [mem_iUnion₂, mem_preimage, mem_singleton_iff, ballIndex_eq_iff hθ, exists_prop,
    and_or_left, exists_or, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff]
  exact or_congr Iff.rfl ⟨fun ⟨_, hA, rfl, h⟩ ↦ ⟨hA, h⟩, fun ⟨hA, h⟩ ↦ ⟨_, hA, rfl, h⟩⟩

end BallIndex

end TauCeti

end
