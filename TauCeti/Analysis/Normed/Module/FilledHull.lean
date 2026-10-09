/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Convex
public import TauCeti.Topology.FilledHull
public import TauCeti.Analysis.Normed.Module.Ball.Exterior
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Boundedness and diameter of filled hulls

The filled hull `TauCeti.filledHull K` is `K` together with the bounded connected components of
its complement. Its topological API is in `TauCeti/Topology/FilledHull.lean`. In a real seminormed
space, filling preserves boundedness and diameter: for nonempty `K`, the filled hull lies in
`closedConvexHull ℝ K`, which has the same diameter as `K`.

The containment uses the geometric Hahn–Banach separation theorem
(`geometric_hahn_banach_point_closed`). A point outside the closed convex hull lies in an open
half-space disjoint from `K`. This half-space is preconnected and unbounded, so the point's
component in `Kᶜ` is unbounded. In a seminormed space, the continuous separating functional sends
bounded sets to bounded sets, while its image of this half-space contains every real number below
the separating level.

Nonemptiness is essential for the convex-hull containment: with the zero seminorm, the filled
hull of `∅` is the whole space, whereas its convex hull is empty. The diameter results need no
nonemptiness assumption because the empty hull lies in a radius-zero ball. As usual for
`Metric.diam`, an unbounded set has diameter `0`.

These bounds apply to sets enclosed by a boundary: `IsPreconnected.subset_filledHull` places a
preconnected set disjoint from `K` inside the filled hull as soon as it meets it. Thus a
preconnected set cut off from infinity by a bounded `K` has diameter at most `diam K`, without
regularity assumptions on `K`. The related frontier bound in
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean` requires the whole frontier to lie in `K`;
`TauCeti.subset_filledHull_of_frontier_subset` connects the two forms of enclosure.

## Main results

* `TauCeti.filledHull_sphere` — filling a sphere gives the closed ball.
* `TauCeti.filledHull_subset_closedConvexHull` — the filled hull of a nonempty set lies in its
  closed convex hull.
* `TauCeti.isBounded_filledHull` and `TauCeti.diam_filledHull` — filling preserves boundedness
  and diameter.
* `TauCeti.diam_le_diam_of_subset_filledHull` and
  `IsPreconnected.diam_le_diam_of_disjoint` — sets enclosed by a bounded `K` are no wider than `K`.
* `TauCeti.filledHull_empty` — the empty hull is empty in a nontrivial real normed space.
* `TauCeti.connectedComponentIn_compl_eq_of_unbounded_component` — the unbounded complementary
  component of a bounded set is unique in dimension at least two.
* `TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn` — of two points in
  different complementary components, at least one lies in the filled hull, in dimension at
  least two.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {K S : Set E}

/-- The filled hull of a sphere of nonnegative radius is the closed ball. No nontriviality or
separation assumption is needed: when the seminorm vanishes identically, both sides are the whole
space. -/
@[simp]
theorem filledHull_sphere (x : E) {r : ℝ} (hr : 0 ≤ r) :
    filledHull (sphere x r) = closedBall x r := by
  refine Subset.antisymm (fun y hy => ?_) fun y hy => ?_
  · by_contra hyr
    rw [mem_closedBall, not_le] at hyr
    have hyx : 0 < ‖y - x‖ := by rw [← dist_eq_norm]; linarith
    have hdist : ∀ t : ℝ, dist (x + t • (y - x)) x = |t| * ‖y - x‖ := fun t => by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    let ray := (fun t : ℝ => x + t • (y - x)) '' Ici 1
    have hcont : Continuous fun t : ℝ => x + t • (y - x) := by fun_prop
    have hconn : IsPreconnected ray := isPreconnected_Ici.image _ hcont.continuousOn
    have hsub : ray ⊆ (sphere x r)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_compl_iff, mem_sphere, hdist, abs_of_pos (by linarith [mem_Ici.mp ht])]
      have : ‖y - x‖ ≤ t * ‖y - x‖ := le_mul_of_one_le_left hyx.le (mem_Ici.mp ht)
      rw [dist_eq_norm] at hyr
      linarith
    have hyray : y ∈ ray := ⟨1, self_mem_Ici, by simp⟩
    obtain ⟨C, hC⟩ := ((mem_filledHull_iff.mp hy).subset
      (hconn.subset_connectedComponentIn hyray hsub)).subset_closedBall x
    set t := (|C| + 1) / ‖y - x‖ + 1
    have ht : 1 ≤ t := le_add_of_nonneg_left (by positivity)
    have hmem := mem_closedBall.mp (hC ⟨t, ht, rfl⟩)
    rw [hdist, abs_of_pos (by linarith), add_mul, div_mul_cancel₀ _ hyx.ne'] at hmem
    linarith [le_abs_self C]
  · rcases (mem_closedBall.mp hy).eq_or_lt with h | h
    · exact subset_filledHull (mem_sphere.mpr h)
    · exact subset_filledHull_of_frontier_subset isBounded_ball frontier_ball_subset_sphere
        (mem_ball.mpr h)

/-- The filled hull of a nonempty set lies in its closed convex hull. Nonemptiness is essential:
with the zero seminorm, `filledHull ∅ = univ`, while `closedConvexHull ℝ ∅ = ∅`. -/
theorem filledHull_subset_closedConvexHull (hK : K.Nonempty) :
    filledHull K ⊆ closedConvexHull ℝ K := by
  intro x hx
  rw [mem_filledHull_iff] at hx
  by_contra hxC
  obtain ⟨φ, u, hφx, hφC⟩ := geometric_hahn_banach_point_closed convex_closedConvexHull
    isClosed_closedConvexHull hxC
  -- The open half-space cut off by `φ` is a preconnected subset of `Kᶜ` containing `x`.
  have hHK : {y | φ y < u} ⊆ Kᶜ :=
    fun y hy hyK => absurd (hφC y (subset_closedConvexHull hyK)) (not_lt.mpr hy.le)
  have hsub : {y | φ y < u} ⊆ connectedComponentIn Kᶜ x :=
    (convex_halfSpace_lt φ.toLinearMap.isLinear u).isPreconnected.subset_connectedComponentIn
      hφx hHK
  -- It is unbounded, because a nonempty `K` forces `φ` to be nonzero.
  obtain ⟨b, hb⟩ := hK
  have hφne : (φ : E →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    have hzero : ∀ y : E, φ y = 0 := fun y =>
      (LinearMap.congr_fun h y).trans (LinearMap.zero_apply y)
    have hb' := hφC b (subset_closedConvexHull hb)
    rw [hzero] at hφx hb'
    linarith
  obtain ⟨R, hR⟩ := (φ.lipschitzWith.isBounded_image (hx.subset hsub)).bddBelow
  have hφsurj : Function.Surjective φ := LinearMap.surjective_iff_ne_zero.mpr hφne
  obtain ⟨y, hy⟩ := hφsurj (min u R - 1)
  have hyu : φ y < u := by rw [hy]; linarith [min_le_left u R]
  have hRy := hR ⟨y, hyu, rfl⟩
  rw [hy] at hRy
  linarith [min_le_right u R]

/-- The empty hull lies in a radius-zero ball, even when zero norm does not imply equality. -/
private theorem filledHull_empty_subset_closedBall :
    filledHull (∅ : Set E) ⊆ closedBall (0 : E) 0 := by
  rw [← filledHull_sphere (0 : E) le_rfl]
  exact filledHull_mono (empty_subset _)

/-- A filled hull is bounded exactly when the set filled is. -/
@[simp]
theorem isBounded_filledHull : IsBounded (filledHull K) ↔ IsBounded K := by
  refine ⟨fun h => h.subset subset_filledHull, fun hKb => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact isBounded_closedBall.subset filledHull_empty_subset_closedBall
  · exact (isBounded_closedConvexHull.mpr hKb).subset (filledHull_subset_closedConvexHull hK)

/-- Filling preserves the diameter, including for empty and unbounded sets. -/
@[simp]
theorem diam_filledHull : diam (filledHull K) = diam K := by
  by_cases hKb : IsBounded K
  · rcases K.eq_empty_or_nonempty with rfl | hK
    · rw [diam_empty]
      exact le_antisymm (by simpa using
        diam_le_of_subset_closedBall le_rfl filledHull_empty_subset_closedBall) diam_nonneg
    refine le_antisymm ?_ (diam_mono subset_filledHull (isBounded_filledHull.mpr hKb))
    calc diam (filledHull K) ≤ diam (closedConvexHull ℝ K) :=
          diam_mono (filledHull_subset_closedConvexHull hK) (isBounded_closedConvexHull.mpr hKb)
      _ = diam K := diam_closedConvexHull
  · rw [diam_eq_zero_of_unbounded (mt isBounded_filledHull.mp hKb), diam_eq_zero_of_unbounded hKb]

/-- A set inside the filled hull of a bounded `K` has diameter at most `diam K`. -/
theorem diam_le_diam_of_subset_filledHull (hK : IsBounded K) (h : S ⊆ filledHull K) :
    diam S ≤ diam K :=
  (diam_mono h (isBounded_filledHull.mpr hK)).trans_eq diam_filledHull

/-- A preconnected set disjoint from a bounded `K` that meets its filled hull has diameter at most
`diam K`. No regularity is required of `K`. -/
theorem _root_.IsPreconnected.diam_le_diam_of_disjoint (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) (hK : IsBounded K) : diam S ≤ diam K :=
  diam_le_diam_of_subset_filledHull hK (hS.subset_filledHull hSK hne)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- The filled hull of the empty set is empty in a nontrivial real normed space. This does not
extend to seminormed spaces with identically zero seminorm. -/
@[simp]
theorem filledHull_empty [Nontrivial E] : filledHull (∅ : Set E) = ∅ := by
  apply filledHull_eq_self
  · rw [compl_empty]
    exact isPreconnected_univ
  · rw [compl_empty]
    exact NormedSpace.unbounded_univ ℝ E

variable {x y : E}

/-- **The unbounded component of the complement of a bounded set is unique** in a real normed space
of dimension at least two. -/
theorem connectedComponentIn_compl_eq_of_unbounded_component (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hx : ¬ IsBounded (connectedComponentIn Kᶜ x))
    (hy : ¬ IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : E)
  have hext : (closedBall (0 : E) R)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hR
  have hesc : ∀ z : E, ¬ IsBounded (connectedComponentIn Kᶜ z) →
      ∃ z' ∈ connectedComponentIn Kᶜ z, z' ∈ (closedBall (0 : E) R)ᶜ :=
    fun z hz => not_subset.mp fun hs => hz (isBounded_closedBall.subset hs)
  obtain ⟨x', hx'c, hx'R⟩ := hesc x hx
  obtain ⟨y', hy'c, hy'R⟩ := hesc y hy
  have h1 : y' ∈ connectedComponentIn Kᶜ x' :=
    (isPreconnected_compl_closedBall h 0 R).subset_connectedComponentIn hx'R hext hy'R
  rw [connectedComponentIn_eq hx'c, connectedComponentIn_eq h1, ← connectedComponentIn_eq hy'c]

/-- **Two points in different components of the complement of a bounded set cannot both lie outside
the filled hull** in a real normed space of dimension at least two. -/
theorem mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hxy : y ∉ connectedComponentIn Kᶜ x) :
    x ∈ filledHull K ∨ y ∈ filledHull K := by
  by_cases hy : y ∈ K
  · exact Or.inr (subset_filledHull hy)
  · by_contra hcon
    push Not at hcon
    simp only [mem_filledHull_iff] at hcon
    exact hxy ((connectedComponentIn_compl_eq_of_unbounded_component h hK hcon.1 hcon.2).symm ▸
      mem_connectedComponentIn (mem_compl hy))

end TauCeti
