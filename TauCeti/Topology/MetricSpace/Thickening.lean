/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Pairwise disjoint thickenings

Compact pairwise disjoint sets in a finite family admit pairwise disjoint thickenings of one
common positive radius.
-/

public section

open Set Metric Function

namespace TauCeti

/-- A finite family of pairwise disjoint compact sets admits pairwise disjoint thickenings of one
common positive radius. -/
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
      let _ := Fintype.ofFinite ι
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
      let P : Finset (ι × ι) := Finset.univ.product Finset.univ
      have hP : P.Nonempty := by
        rcases hι with ⟨i⟩
        exact ⟨(i, i), by simp [P]⟩
      let Q : Finset ℝ := P.image (fun p => r p.1 p.2)
      have hQ : Q.Nonempty := hP.image _
      let δ : ℝ := Q.min' hQ
      have hδ_pos : 0 < δ := by
        have hqpos : ∀ q ∈ Q, 0 < q := by
          intro q hq
          rcases Finset.mem_image.1 hq with ⟨p, hp, rfl⟩
          exact hr_pos p.1 p.2
        exact hqpos _ (Finset.min'_mem Q hQ)
      have hδ_le (i j : ι) : δ ≤ r i j := by
        apply Finset.min'_le Q (r i j)
        exact Finset.mem_image.2 ⟨(i, j), by simp [P], rfl⟩
      have hV_disj : ∀ i j, i ≠ j →
          Disjoint (thickening δ (K i)) (thickening δ (K j)) := by
        intro i j hij
        apply (hr_disj i j hij).mono
        · exact thickening_mono (hδ_le i j) _
        · exact thickening_mono (hδ_le i j) _
      exact ⟨δ, hδ_pos, hV_disj⟩

end TauCeti
