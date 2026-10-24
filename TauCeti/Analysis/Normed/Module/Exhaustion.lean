/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.FilledIn
-- Provides `NormedSpace.toLocallyConvexSpace`, hence `LocallyConnectedSpace E`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Filled compact exhaustions of open sets

The main theorem `IsOpen.exists_isFilledIn_compact_exhaustion` says that every open subset `Ω` of
a proper real normed space has an exhaustion by compact sets `K n ⊆ interior (K (n + 1))`, each of
which is filled in `Ω` in the sense of `TauCeti.IsFilledIn`: no connected component of `Ω \ K n`
is relatively compact in `Ω`. Such an exhaustion is the device which turns Runge approximation on
compact sets into the solution of an equation on all of `Ω`: successive local solutions are
corrected by global approximants with summable errors on the `K n`. The sets are
`K n = closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`, and
`IsOpen.isFilledIn_closedBall_sdiff_thickening` shows that each such set is filled in `Ω`: a point
outside it either lies outside the ball, hence outside the filled hull of the ball, or is joined to
a point of `Ωᶜ` by a short segment avoiding it.

## Main declarations

* `IsOpen.isFilledIn_closedBall_sdiff_thickening`: a closed ball with a thickening of `Ωᶜ`
  removed is filled in `Ω`.
* `IsOpen.exists_isFilledIn_compact_exhaustion`: an open set in a proper real normed space has a
  compact exhaustion by sets filled in it.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Metric Set

section Exhaustion

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **A closed ball minus a thickening of `Ωᶜ` is filled in `Ω`.** A point outside
`K = closedBall a r \ thickening δ Ωᶜ` either lies outside the ball, hence outside the filled hull
of the ball and so of `K`, or lies within `δ` of a point `y ∉ Ω`, to which the segment from it
leads without meeting `K`. -/
theorem IsOpen.isFilledIn_closedBall_sdiff_thickening {Ω : Set E} (hΩ : IsOpen Ω) (a : E)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IsFilledIn (closedBall a r \ thickening δ Ωᶜ) Ω := by
  have hKΩ : closedBall a r \ thickening δ Ωᶜ ⊆ Ω := fun x hx => by
    by_contra hxΩ
    exact hx.2 (self_subset_thickening hδ _ hxΩ)
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (isClosed_closedBall.sdiff isOpen_thickening) hΩ hKΩ]
  rintro x ⟨hxH, hxK⟩ hDΩ
  by_cases hx : x ∈ closedBall a r
  · -- `x` is within `δ` of a point `y ∉ Ω`; the segment `[x, y]` stays that close to `y`, so it
    -- avoids `K` and carries `y` into the component of `x` in `Kᶜ`.
    have hxt : x ∈ thickening δ Ωᶜ := by
      by_contra hxt
      exact hxK ⟨hx, hxt⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxt
    have hseg : segment ℝ x y ⊆ connectedComponentIn (closedBall a r \ thickening δ Ωᶜ)ᶜ x :=
      (convex_segment x y).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x y)
        fun z hz hzK => hzK.2 <| mem_thickening_iff.mpr
          ⟨y, hy, (mem_closedBall.mp (segment_subset_closedBall_right x y hz)).trans_lt hxy⟩
    exact hy (hDΩ (hseg (right_mem_segment ℝ x y)))
  · -- The filled hull of `K` lies in that of the ball, hence in its closed convex hull: the ball.
    exact hx (closedConvexHull_min subset_rfl (convex_closedBall _ _) isClosed_closedBall
      (filledHull_subset_closedConvexHull (nonempty_closedBall.mpr hr)
        (filledHull_mono sdiff_subset hxH)))

/-- **Filled compact exhaustion.** Every open set `Ω` of a proper real normed space is the union of
compact sets `K n` with `K n ⊆ interior (K (n + 1))`, each of which is filled in `Ω`: no connected
component of `Ω \ K n` is relatively compact in `Ω`. -/
theorem IsOpen.exists_isFilledIn_compact_exhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n + 1))) ∧
      ⋃ n, K n = Ω ∧ ∀ n, IsFilledIn (K n) Ω := by
  set K : ℕ → Set E := fun n => closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ
  have hKcpt : ∀ n, IsCompact (K n) := fun n => (isCompact_closedBall _ _).diff isOpen_thickening
  have hKΩ : ∀ n, K n ⊆ Ω := fun n x hx => by
    by_contra hxΩ
    exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)
  refine ⟨K, hKcpt, fun n => ?_, ?_, fun n => ?_⟩
  · -- `K n` lies in the open set `ball 0 (n + 2) \ cthickening (n + 2)⁻¹ Ωᶜ ⊆ K (n + 1)`.
    have hopen : IsOpen (ball (0 : E) (n + 1 + 1) \ cthickening (n + 1 + 1 : ℝ)⁻¹ Ωᶜ) :=
      isOpen_ball.sdiff isClosed_cthickening
    refine Subset.trans ?_ (hopen.subset_interior_iff.mpr ?_)
    · rintro x ⟨hx₁, hx₂⟩
      refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx₁).trans_lt (by linarith)),
        fun h => hx₂ (cthickening_subset_thickening' (by positivity) ?_ _ h)⟩
      gcongr
      linarith
    · simp only [K, Nat.cast_add, Nat.cast_one]
      exact sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)
  · refine Subset.antisymm (iUnion_subset hKΩ) fun x hx => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ε⁻¹)
    have hn₁ : ‖x‖ ≤ n := (le_max_left _ _).trans hn
    have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
    refine mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr (by linarith), fun h => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
    refine hy (hball ?_)
    rw [mem_ball, dist_comm]
    exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)
  · exact hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) (by positivity)

end Exhaustion
