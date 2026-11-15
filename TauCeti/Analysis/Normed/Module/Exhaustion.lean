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

* `TauCeti.closedBall_sdiff_thickening_subset_interior`: decreasing the thickening radius and
  increasing the ball radius places one stage inside the interior of the next.
* `IsOpen.iUnion_closedBall_sdiff_thickening` and
  `IsOpen.exists_subset_interior_closedBall_sdiff_thickening`: the explicit stages exhaust `Ω` and
  their interiors cover every compact subset of `Ω`.
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

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- **Strict nesting of ball-minus-thickening stages.** Increasing the ball radius from `r` to `R`
and shrinking the thickening radius from `δ₁` to `δ₂ > 0` places `closedBall a r \ thickening δ₁ s`
inside the interior of `closedBall a R \ thickening δ₂ s`. -/
theorem TauCeti.closedBall_sdiff_thickening_subset_interior (a : X) {r R δ₁ δ₂ : ℝ} (hrR : r < R)
    (hδ₂ : 0 < δ₂) (hδ : δ₂ < δ₁) (s : Set X) :
    closedBall a r \ thickening δ₁ s ⊆ interior (closedBall a R \ thickening δ₂ s) := by
  have hopen : IsOpen (ball a R \ cthickening δ₂ s) := isOpen_ball.sdiff isClosed_cthickening
  refine Subset.trans ?_ (hopen.subset_interior_iff.mpr
    (sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening δ₂ s)))
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨mem_ball.mpr ((mem_closedBall.mp hx₁).trans_lt hrR),
    fun h => hx₂ (cthickening_subset_thickening' (hδ₂.trans hδ) hδ s h)⟩

/-- **Exhaustion of an open set by explicit ball-minus-thickening stages.** Every open set `Ω` in a
pseudometric space is the union of `closedBall a (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ` over `n : ℕ`. -/
theorem IsOpen.iUnion_closedBall_sdiff_thickening {Ω : Set X} (hΩ : IsOpen Ω) (a : X) :
    (⋃ n : ℕ, closedBall a (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ) = Ω := by
  refine Subset.antisymm (iUnion_subset fun n x hx => ?_) fun x hx => ?_
  · by_contra hxΩ
    exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    obtain ⟨n, hn⟩ := exists_nat_ge (max (dist x a) ε⁻¹)
    have hn₁ : dist x a ≤ n := (le_max_left _ _).trans hn
    have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
    refine mem_iUnion.mpr ⟨n, mem_closedBall.mpr (by linarith), fun h => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
    refine hy (hball ?_)
    rw [mem_ball, dist_comm]
    exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)

/-- **Compact cofinality of the explicit exhaustion stages.** Every compact subset `K` of an open
set `Ω` lies in the interior of `closedBall a (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ` for some `n`. -/
theorem IsOpen.exists_subset_interior_closedBall_sdiff_thickening {Ω K : Set X} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (a : X) :
    ∃ n : ℕ, K ⊆ interior (closedBall a (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ) := by
  let U : ℕ → Set X := fun n => interior (closedBall a (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ)
  have hmono : Monotone U := monotone_nat_of_le_succ fun n => interior_mono <|
    sdiff_subset_sdiff (closedBall_subset_closedBall (by push_cast; linarith))
      (thickening_mono (inv_anti₀ (by positivity) (by push_cast; linarith)) Ωᶜ)
  have hcover : K ⊆ ⋃ n, U n := by
    refine hKΩ.trans ?_
    rw [← hΩ.iUnion_closedBall_sdiff_thickening a]
    refine iUnion_subset fun n => Subset.trans ?_ (subset_iUnion U (n + 1))
    simpa only [U, Nat.cast_add, Nat.cast_one] using
      TauCeti.closedBall_sdiff_thickening_subset_interior a (by linarith) (by positivity)
        (inv_strictAnti₀ (by positivity) (by linarith)) Ωᶜ
  exact hK.elim_directed_cover U (fun _ => isOpen_interior) hcover hmono.directed_le

end PseudoMetricSpace

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
  refine ⟨fun n => closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ,
    fun n => (isCompact_closedBall _ _).diff isOpen_thickening, fun n => ?_,
    hΩ.iUnion_closedBall_sdiff_thickening 0,
    fun n => hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) (by positivity)⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    closedBall_sdiff_thickening_subset_interior 0 (by linarith) (by positivity)
      (inv_strictAnti₀ (by positivity) (by linarith)) Ωᶜ

end Exhaustion
