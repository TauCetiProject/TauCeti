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

* `IsOpen.isFilledIn_empty`: the empty set is filled in every open set of a nontrivial proper real
  normed space.
* `IsOpen.isFilledIn_closedBall_sdiff_thickening`: a closed ball with a thickening of `Ωᶜ`
  removed is filled in `Ω`.
* `IsOpen.exists_isFilledIn_compact_exhaustion`: an open set in a proper real normed space has a
  compact exhaustion by sets filled in it.
* `TauCeti.not_isFilledIn_closedBall_sdiff_ball_ball` and
  `TauCeti.isFilledIn_closedBall_sdiff_ball_sdiff_closedBall`: a closed annulus is not filled in a
  larger open ball, because its inner hole is trapped inside the ball, whereas puncturing the ball
  by a smaller concentric closed ball makes the annulus filled in the punctured ball.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Metric Set

section Exhaustion

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- The empty set is filled in every open subset of a nontrivial proper real normed space. -/
theorem IsOpen.isFilledIn_empty [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω) :
    IsFilledIn ∅ Ω := by
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω), filledHull_empty]
  simp

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

namespace TauCeti

/-- A closed annulus `closedBall c R \ ball c r` (`0 < r ≤ R`) is **not** filled in any larger
concentric open ball `ball c R'` (`R < R'`). -/
theorem not_isFilledIn_closedBall_sdiff_ball_ball {c : E} {r R R' : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hRR' : R < R') :
    ¬ IsFilledIn (closedBall c R \ ball c r) (ball c R') := by
  set K := closedBall c R \ ball c r
  have hKΩ : K ⊆ ball c R' := sdiff_subset.trans (closedBall_subset_ball hRR')
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (isClosed_closedBall.sdiff isOpen_ball) isOpen_ball hKΩ]
  intro h
  have hsph : sphere c r ⊆ K := fun y hy =>
    ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hy),
      fun hyb => (mem_ball.mp hyb).ne (mem_sphere.mp hy)⟩
  have hcH : c ∈ filledHull K \ K :=
    ⟨filledHull_mono hsph (by rw [filledHull_sphere c hr.le]; exact mem_closedBall_self hr.le),
      fun hcK => hcK.2 (mem_ball_self hr)⟩
  refine h c hcH fun y hy => ball_subset_ball (hrR.trans hRR'.le) ?_
  by_contra hyr
  have hconn : IsPreconnected ((fun z => dist z c) '' connectedComponentIn Kᶜ c) :=
    isPreconnected_connectedComponentIn.image _ (continuous_id.dist continuous_const).continuousOn
  have h0 : (0 : ℝ) ∈ (fun z => dist z c) '' connectedComponentIn Kᶜ c :=
    ⟨c, mem_connectedComponentIn hcH.2, dist_self c⟩
  obtain ⟨z, hzC, hzr⟩ := hconn.Icc_subset h0 ⟨y, hy, rfl⟩ ⟨hr.le, not_lt.mp hyr⟩
  exact connectedComponentIn_subset Kᶜ c hzC (hsph (mem_sphere.mpr hzr))

/-- Puncturing the outer open ball by a concentric closed ball inside the inner hole makes the
closed annulus `closedBall c R \ ball c r` filled in `ball c R' \ closedBall c r₀`
(`0 ≤ r₀ < r ≤ R < R'`). -/
theorem isFilledIn_closedBall_sdiff_ball_sdiff_closedBall {c : E} {r₀ r R R' : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₀r : r₀ < r) (hrR : r ≤ R) (hRR' : R < R') :
    IsFilledIn (closedBall c R \ ball c r) (ball c R' \ closedBall c r₀) := by
  set K := closedBall c R \ ball c r
  set Ω := ball c R' \ closedBall c r₀
  have hKΩ : K ⊆ Ω := fun z hz =>
    ⟨closedBall_subset_ball hRR' hz.1,
      fun hzr₀ => hz.2 (closedBall_subset_ball hr₀r hzr₀)⟩
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (isClosed_closedBall.sdiff isOpen_ball) (isOpen_ball.sdiff isClosed_closedBall) hKΩ]
  rintro x ⟨hxH, hxK⟩ hDΩ
  have hr : 0 < r := hr₀.trans_lt hr₀r
  have hxR : x ∈ closedBall c R :=
    closedConvexHull_min subset_rfl (convex_closedBall c R) isClosed_closedBall
      (filledHull_subset_closedConvexHull (nonempty_closedBall.mpr (hr.le.trans hrR))
        (filledHull_mono sdiff_subset hxH))
  have hxr : x ∈ ball c r := by
    by_contra hxr
    exact hxK ⟨hxR, hxr⟩
  have hseg : segment ℝ x c ⊆ connectedComponentIn Kᶜ x :=
    (convex_segment x c).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x c)
      fun z hz hzK => hzK.2 ((convex_ball c r).segment_subset hxr (mem_ball_self hr) hz)
  exact (hDΩ (hseg (right_mem_segment ℝ x c))).2 (mem_closedBall_self hr₀)

end TauCeti

end Exhaustion
