/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A unique nearest point is isolated by a ball

Let `Z` be a subset of a pseudometric space meeting a closed ball `closedBall z R` in finitely many
points, and let `ρ ∈ Z` be the unique point of `Z` nearest to `z`, with `dist z ρ < R`. Then some
ball about `z` of radius `r`, with `dist z ρ < r ≤ R`, meets `Z` in `ρ` alone
(`TauCeti.exists_ball_inter_eq_singleton_of_finite`): the finitely many other points of `Z` in
the closed ball are all strictly farther from `z` than `ρ`.

## Main results

* `TauCeti.exists_ball_inter_eq_singleton_of_finite`: the ball about `z` isolating a unique nearest
  point.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- If `Z` meets `closedBall z R` in finitely many points and `ρ ∈ Z`, with `dist z ρ < R`, is the
only point of `Z` at distance at most `dist z ρ` from `z`, then a ball about `z` of radius `r`,
with `dist z ρ < r ≤ R`, meets `Z` in `ρ` alone. -/
theorem exists_ball_inter_eq_singleton_of_finite {Z : Set X} {z ρ : X} {R : ℝ}
    (hZ : (closedBall z R ∩ Z).Finite) (hρ : ρ ∈ Z) (hR : dist z ρ < R)
    (huniq : ∀ w ∈ Z, dist z w ≤ dist z ρ → w = ρ) :
    ∃ r, dist z ρ < r ∧ r ≤ R ∧ ball z r ∩ Z = {ρ} := by
  -- every other point of `Z` in the closed ball is strictly farther than `ρ`
  have hgap : ∀ w ∈ (closedBall z R ∩ Z) \ {ρ}, ∀ᶠ r in 𝓝[>] dist z ρ, r ≤ dist z w := by
    rintro w ⟨⟨-, hwZ⟩, hwρ⟩
    exact (eventually_le_nhds <| lt_of_not_ge fun h ↦
      hwρ (mem_singleton_iff.2 (huniq w hwZ h))).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hr, hrR, hrw⟩ := (eventually_mem_nhdsWithin.and <|
    ((eventually_le_nhds hR).filter_mono nhdsWithin_le_nhds).and
      ((eventually_all_finite (hZ.sdiff (t := {ρ}))).2 hgap)).exists
  -- `r ∈ Ioi (dist z ρ)` is the radius inequality `dist z ρ < r`
  replace hr : dist z ρ < r := mem_Ioi.1 hr
  refine ⟨r, hr, hrR, Subset.antisymm ?_ (singleton_subset_iff.2 ⟨mem_ball'.2 hr, hρ⟩)⟩
  rintro w ⟨hw, hwZ⟩
  refine mem_singleton_iff.2 (by_contra fun hwρ ↦ ?_)
  have hwR : w ∈ closedBall z R := ball_subset_closedBall (ball_subset_ball hrR hw)
  exact (hrw w ⟨⟨hwR, hwZ⟩, mem_singleton_iff.not.2 hwρ⟩).not_gt (mem_ball'.1 hw)

end TauCeti
