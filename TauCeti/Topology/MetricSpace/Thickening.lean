/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Data.Fintype.Lattice

/-!
# Pairwise disjoint thickenings

Compact pairwise disjoint sets in a finite family admit pairwise disjoint thickenings of one
common positive radius. This supplies uniformly separated neighborhoods, for example the
component neighborhoods used to construct disjoint solid-torus neighborhoods of a link.
-/

public section

open Set Metric Function

namespace TauCeti

/-- A finite family of pairwise disjoint compact sets admits pairwise disjoint thickenings of one
common positive radius. This extends Mathlib's two-set result `Disjoint.exists_thickenings`. -/
theorem exists_thickenings_pairwiseDisjoint
    {X ι : Type*} [MetricSpace X] [Finite ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (Disjoint on K)) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (Disjoint on fun i => thickening δ (K i)) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      exact ⟨1, zero_lt_one, fun i j hij => False.elim (hι.false i)⟩
  | inr hι =>
      let : Nonempty ι := hι
      have hex : ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
          Disjoint (thickening δ (K i)) (thickening δ (K j)) := by
        intro i j hij
        exact (hdisj hij).exists_thickenings (hK i) (hK j).isClosed
      let r : ι → ι → ℝ := fun i j =>
        if h : i = j then 1 else Classical.choose (hex i j h)
      have hr_pos : ∀ i j, 0 < r i j := by
        intro i j
        by_cases hij : i = j
        · simp [r, hij]
        · simpa [r, hij] using (Classical.choose_spec (hex i j hij)).1
      have hr_disj : ∀ i j, i ≠ j →
          Disjoint (thickening (r i j) (K i)) (thickening (r i j) (K j)) := by
        intro i j hij
        simpa [r, hij] using (Classical.choose_spec (hex i j hij)).2
      obtain ⟨ij, hij⟩ := Finite.exists_min (fun p : ι × ι => r p.1 p.2)
      refine ⟨r ij.1 ij.2, hr_pos ij.1 ij.2, ?_⟩
      intro i j hne
      exact (hr_disj i j hne).mono
        (thickening_mono (hij (i, j)) _) (thickening_mono (hij (i, j)) _)

end TauCeti
