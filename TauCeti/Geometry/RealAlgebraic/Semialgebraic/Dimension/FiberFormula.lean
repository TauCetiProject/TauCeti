/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Projection
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Stack

/-!
# The dimension formula for a one-coordinate projection

For a semialgebraic subset `s` of `ℝ ^ (n + 1)`, let `B` be the set of base points where the
fiber of `Fin.tail` is infinite. Then
`dim s = max (dim (Fin.tail '' s)) (dim B + 1)`.
A fiber of a semialgebraic subset of the real line is either finite or contains an interval,
so this separates the contributions of zero-dimensional and one-dimensional fibers. Empty
sets and empty fibers are included using the bottom value of dimension.

The formula is the one-coordinate induction step in dimension calculations for projections.
It follows from the actual section and sector cells of an adapted cylindrical algebraic
decomposition, without assuming continuity of a map or constant dimension of its fibers.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Section 2.8.
-/

public section

open Set Topology

namespace TauCeti

variable {n : ℕ} {s : Set (Fin (n + 1) → ℝ)}

/-- In an adapted CAD, the infinite-fiber locus is the union of the projections of the cells
contained in the set that have an infinite fiber. -/
theorem IsCAD.setOf_infinite_setOf_cons_mem_eq_biUnion_image_tail
    {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞)
    (hadapt : ∀ E ∈ 𝒞, E ⊆ s ∨ Disjoint E s) :
    {x : Fin n → ℝ | {t : ℝ | Fin.cons t x ∈ s}.Infinite} =
      ⋃ E ∈ {E ∈ {E ∈ 𝒞 | E ⊆ s} | ∃ x, {t : ℝ | Fin.cons t x ∈ E}.Infinite},
        Fin.tail '' E := by
  classical
  let A := {E ∈ 𝒞 | E ⊆ s}
  have hA : A.Finite := h.finite.subset (sep_subset _ _)
  have hcover : ⋃₀ A = s := h.sUnion_sep_subset hadapt
  have hsector {E} (hE : E ∈ 𝒞) (hinf : ∃ x, {t : ℝ | Fin.cons t x ∈ E}.Infinite) :
      ∀ x, {t : ℝ | Fin.cons t x ∈ E}.Infinite ↔ x ∈ Fin.tail '' E := by
    rcases h.semialgebraicDim_setOf_cons_mem_cases hE with hfinite | hinfinite
    · obtain ⟨x, hx⟩ := hinf
      exact (hx (hfinite.2 x)).elim
    · exact hinfinite.2
  ext x
  constructor
  · intro hx
    have hex : ∃ E ∈ A, {t : ℝ | Fin.cons t x ∈ E}.Infinite := by
      by_contra! hfin
      have hf : (⋃ E ∈ A, {t : ℝ | Fin.cons t x ∈ E}).Finite :=
        hA.biUnion fun E hE ↦ hfin E hE
      apply hx
      refine hf.subset fun t ht ↦ ?_
      obtain ⟨E, hE, ht⟩ := mem_sUnion.mp (hcover.symm ▸ ht)
      exact mem_iUnion₂.mpr ⟨E, hE, ht⟩
    obtain ⟨E, hE, hxE⟩ := hex
    exact mem_iUnion₂.mpr ⟨E, ⟨hE, x, hxE⟩, (hsector hE.1 ⟨x, hxE⟩ x).mp hxE⟩
  · intro hx
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hx
    exact ((hsector hE.1.1 hE.2 x).mpr hxE).mono fun _ ht ↦ hE.1.2 ht

/-- **The fiber-dimension formula for forgetting one coordinate.** The total dimension is the
larger of the image dimension and one plus the dimension of the locus of infinite fibers.
Both sides are `⊥` for the empty set. -/
theorem IsSemialgebraic.semialgebraicDim_eq_max_image_tail_infinite_setOf_cons_mem
    (hs : IsSemialgebraic s) :
    semialgebraicDim s = max (semialgebraicDim (Fin.tail '' s))
      (semialgebraicDim {x : Fin n → ℝ | {t : ℝ | Fin.cons t x ∈ s}.Infinite} + 1) := by
  classical
  obtain ⟨𝒞, h𝒞, hadapt⟩ := hs.exists_isCAD_subset_or_disjoint
  let A := {E ∈ 𝒞 | E ⊆ s}
  let B := {x : Fin n → ℝ | {t : ℝ | Fin.cons t x ∈ s}.Infinite}
  let S := {E ∈ A | ∃ x, {t : ℝ | Fin.cons t x ∈ E}.Infinite}
  have hA : A.Finite := h𝒞.finite.subset (sep_subset _ _)
  have hS : S.Finite := hA.subset (sep_subset _ _)
  -- The infinite-fiber locus is a finite union of projected sector cells.
  have hB : B = ⋃ E ∈ S, Fin.tail '' E :=
    h𝒞.setOf_infinite_setOf_cons_mem_eq_biUnion_image_tail hadapt
  have hBdim : semialgebraicDim B = ⨆ E ∈ S, semialgebraicDim (Fin.tail '' E) := by
    rw [hB, ← sUnion_image]
    rw [semialgebraicDim_sUnion_of_isLocallyClosed (hS.image _)]
    · simp only [iSup_image]
    · rintro _ ⟨E, hE, rfl⟩
      exact h𝒞.image_tail.isLocallyClosed (mem_image_of_mem _ hE.1.1)
  -- A projected sector of maximal dimension attains the fiber contribution.
  have hBle : semialgebraicDim B + 1 ≤ semialgebraicDim s := by
    rcases S.eq_empty_or_nonempty with hempty | hne
    · simp [hBdim, hempty]
    · obtain ⟨E, hE, hmax⟩ := exists_max_image S (fun E ↦ semialgebraicDim (Fin.tail '' E)) hS hne
      have heq : semialgebraicDim B = semialgebraicDim (Fin.tail '' E) := by
        rw [hBdim]
        exact le_antisymm (iSup₂_le hmax) (le_iSup₂_of_le E hE le_rfl)
      rcases h𝒞.semialgebraicDim_setOf_cons_mem_cases hE.1.1 with hfinite | hinfinite
      · obtain ⟨x, hx⟩ := hE.2
        exact (hx (hfinite.2 x)).elim
      · rw [heq, ← hinfinite.1]
        exact semialgebraicDim_mono hE.1.2
  -- Every cell contributes either its base dimension or one additional dimension.
  refine le_antisymm ?_ (max_le hs.semialgebraicDim_image_tail_le hBle)
  rw [h𝒞.semialgebraicDim_eq_iSup hadapt]
  refine iSup₂_le fun E hE ↦ ?_
  rcases h𝒞.semialgebraicDim_setOf_cons_mem_cases hE.1 with hfinite | hinfinite
  · rw [hfinite.1]
    exact (semialgebraicDim_mono (image_mono hE.2)).trans (le_max_left _ _)
  · rw [hinfinite.1]
    refine (add_le_add (semialgebraicDim_mono ?_) le_rfl).trans (le_max_right _ _)
    intro x hx
    exact ((hinfinite.2 x).mpr hx).mono fun _ ht ↦ hE.2 ht

end TauCeti
