/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Initial.Mixed
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Cross.Partners
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.PentagonTerminal.Mixed
public import TauCeti.KnotTheory.Grid.Commutation.TurnCut

/-!
# The residual mixed pentagon--rectangle terms of grid commutation

A terminal-side commutation pentagon followed by a rectangle has two mixed orientations of
its unique common side column. If the rectangle starts where the pentagon ends, the domain is
either a common-initial-side recut partner or a turn cut. If the rectangle ends where the
pentagon starts, its row order and the position of the turn row identify it as a
common-initial-side recut partner, a terminal-cross recut partner, or the mixed member of a
terminal self-pair.

This file partitions the off-diagonal mixed-side terms into these four disjoint families.
After removing the two recut partner families, only the turn cuts and mixed terminal self-pairs
remain. The resulting sum formula supplies the terminal-pentagon mixed-side contribution in
`GridDiagram.commutationMap_comp_unblockedDifferential_eq_iff_oriented_overlap`.
The mixed members of the terminal self-pairs are retained: their cancelling partners have
same-side overlap, so their mixed-side sum alone need not vanish.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The individual side characterizations are formalized in
`Overlap.Initial.Mixed`, `Overlap.Terminal.Cross.Partners`, and
`Overlap.PentagonTerminal.Mixed`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

private theorem terminalMixed_side_facts
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) (hzx : z ≠ x) :
    (E.toRectangleDecomposition.HasMixedSideOverlap ↔
        E.rectangle.left = E.pentagon.right ∨ E.rectangle.right = E.pentagon.left) ∧
      ¬(E.rectangle.left = E.pentagon.right ∧ E.rectangle.right = E.pentagon.left) := by
  have hone (h : E.rectangle.left = E.pentagon.right ∨
      E.rectangle.right = E.pentagon.left) : E.toRectangleDecomposition.HasOneCommonSide := by
    obtain ⟨c, hc⟩ : ∃ c, c ∈ E.toRectangleDecomposition.commonSideColumns := by
      rcases h with h | h
      · exact ⟨E.pentagon.right, by simp [GridRectangleBetween.mem_sideColumns, ← h]⟩
      · exact ⟨E.pentagon.left, by simp [GridRectangleBetween.mem_sideColumns, ← h]⟩
    exact E.toRectangleDecomposition.hasOneCommonSide_of_mem_commonSideColumns hc hzx
  refine ⟨?_, fun ⟨hl, hr⟩ => ?_⟩
  · rw [GridRectangleDecomposition.hasMixedSideOverlap_iff]
    simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · intro h
      refine ⟨hone h, ?_⟩
      rcases h with h | h
      · exact Or.inr h.symm
      · exact Or.inl h.symm
  · exact E.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide (hone (Or.inl hl))
      (by simp [GridRectangleBetween.sideColumns, hl, hr, Finset.pair_comm])

private theorem terminalMixed_row_order
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hother : E.rectangle.left ≠ E.pentagon.right) :
    E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top ∨
      E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  have h := (E.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_right
    (by simpa using hcommon.symm) (by simpa using hother.symm)
    (E.underlying_first_isEmpty ((G.mem_pentagons _).1 hP).1)
    (E.underlying_second_isEmpty
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1)).2
  simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_middle] using h

private theorem terminalMixed_row_facts
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    (E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top →
        C.turnRow ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) ∧
      ¬(E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top ∧
        E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top) := by
  refine ⟨fun hrow => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo E.pentagon.turn_mem_cIco_bottom_top
      (Grid.mem_cIoo_cyclic_left hrow)
  · exact Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap E.pentagon.bottom E.pentagon.top) h₂
      (Grid.mem_cIoo_cyclic_right h₁)

open scoped Classical in
/-- Off the diagonal, the mixed-side pentagon--rectangle terms are the disjoint union of the
common-initial-side partners, terminal-cross partners, turn cuts, and mixed terminal self-pairs. -/
theorem filter_hasMixedSideOverlap_pentagonRectangleDecompositions_eq_union (hzx : z ≠ x) :
    (G.pentagonRectangleDecompositions C x z).filter
        (fun E => E.toRectangleDecomposition.HasMixedSideOverlap) =
      G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z ∪
        G.pentagonRectangleTurnCuts C x z ∪
          (G.pentagonTerminalSelfPairs C x z).filter
            (fun E => E.toRectangleDecomposition.HasMixedSideOverlap) := by
  ext E
  obtain ⟨hmixed, hother⟩ := G.terminalMixed_side_facts C E hzx
  obtain ⟨hturn, hexclusive⟩ := G.terminalMixed_row_facts C E
  have horder := G.terminalMixed_row_order C E
  have hb := E.pentagon.right_eq
  have hp := E.pentagon.left_ne_right
  have hr := E.rectangle.left_ne_right
  simp only [Finset.mem_filter, Finset.mem_union, mem_initialOverlapPartners_iff_sides,
    mem_terminalCrossOverlapPartners_iff_sides, mem_pentagonRectangleTurnCuts,
    mem_pentagonTerminalSelfPairs_iff_sides, hmixed]
  -- Column orientation fixes the branch; row order and the turn row distinguish its families.
  grind

open scoped Classical in
private theorem disjoint_terminalMixed_families (hzx : z ≠ x) :
    Disjoint (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z ∪
        G.pentagonRectangleTurnCuts C x z)
      ((G.pentagonTerminalSelfPairs C x z).filter
        (fun E => E.toRectangleDecomposition.HasMixedSideOverlap)) ∧
      Disjoint (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z)
        (G.pentagonRectangleTurnCuts C x z) ∧
      Disjoint (G.initialOverlapPartners C x z) (G.terminalCrossOverlapPartners C x z) := by
  refine ⟨?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.2 fun E h₁ h₂ => ?_ <;>
  · obtain ⟨hmixed, hother⟩ := G.terminalMixed_side_facts C E hzx
    obtain ⟨hturn, hexclusive⟩ := G.terminalMixed_row_facts C E
    have hb := E.pentagon.right_eq
    have hp := E.pentagon.left_ne_right
    have hr := E.rectangle.left_ne_right
    simp only [Finset.mem_filter, Finset.mem_union, mem_initialOverlapPartners_iff_sides,
      mem_terminalCrossOverlapPartners_iff_sides, mem_pentagonRectangleTurnCuts,
      mem_pentagonTerminalSelfPairs_iff_sides, hmixed] at h₁ h₂
    grind

open scoped Classical in
/-- The terminal-pentagon mixed-side contribution is the sum of its two recut partner families,
turn cuts, and mixed terminal self-pairs. This identity holds for any additive weights. -/
theorem sum_pentagonRectangle_mixedSide_eq_sum_partners_add_turnCuts_add_selfPairs
    {M : Type*} [AddCommMonoid M]
    (w : GridPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ E ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun E => E.toRectangleDecomposition.HasMixedSideOverlap), w E =
      (∑ E ∈ G.initialOverlapPartners C x z, w E) +
        (∑ E ∈ G.terminalCrossOverlapPartners C x z, w E) +
          (∑ E ∈ G.pentagonRectangleTurnCuts C x z, w E) +
            ∑ E ∈ (G.pentagonTerminalSelfPairs C x z).filter
              (fun E => E.toRectangleDecomposition.HasMixedSideOverlap), w E := by
  obtain ⟨h₁, h₂, h₃⟩ := G.disjoint_terminalMixed_families C hzx
  rw [G.filter_hasMixedSideOverlap_pentagonRectangleDecompositions_eq_union C hzx,
    Finset.sum_union h₁, Finset.sum_union h₂, Finset.sum_union h₃]

open scoped Classical in
/-- Removing the two recut partner families from the mixed-side pentagon--rectangle terms leaves
exactly the turn cuts and mixed terminal self-pairs. -/
theorem filter_hasMixedSideOverlap_pentagonRectangleDecompositions_sdiff_partners_eq_union
    (hzx : z ≠ x) :
    (G.pentagonRectangleDecompositions C x z).filter
        (fun E => E.toRectangleDecomposition.HasMixedSideOverlap) \
      (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z) =
        G.pentagonRectangleTurnCuts C x z ∪
          (G.pentagonTerminalSelfPairs C x z).filter
            (fun E => E.toRectangleDecomposition.HasMixedSideOverlap) := by
  obtain ⟨h₁, h₂, -⟩ := G.disjoint_terminalMixed_families C hzx
  have hdisjoint : Disjoint (G.initialOverlapPartners C x z ∪
      G.terminalCrossOverlapPartners C x z)
      (G.pentagonRectangleTurnCuts C x z ∪
        (G.pentagonTerminalSelfPairs C x z).filter
          (fun E => E.toRectangleDecomposition.HasMixedSideOverlap)) :=
    Finset.disjoint_union_right.2 ⟨h₂, (Finset.disjoint_union_left.1 h₁).1⟩
  rw [G.filter_hasMixedSideOverlap_pentagonRectangleDecompositions_eq_union C hzx,
    Finset.union_assoc, Finset.union_sdiff_cancel_left hdisjoint]

open scoped Classical in
/-- The residual mixed-side pentagon--rectangle sum retains the turn-cut weights and the mixed
terminal self-pair weights after both recut partner families have been removed. -/
theorem sum_pentagonRectangle_mixedSide_sdiff_partners_eq_sum_turnCuts_add_selfPairs
    {M : Type*} [AddCommMonoid M]
    (w : GridPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ E ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun E => E.toRectangleDecomposition.HasMixedSideOverlap) \
        (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z), w E =
      (∑ E ∈ G.pentagonRectangleTurnCuts C x z, w E) +
        ∑ E ∈ (G.pentagonTerminalSelfPairs C x z).filter
          (fun E => E.toRectangleDecomposition.HasMixedSideOverlap), w E := by
  obtain ⟨h, -, -⟩ := G.disjoint_terminalMixed_families C hzx
  rw [G.filter_hasMixedSideOverlap_pentagonRectangleDecompositions_sdiff_partners_eq_union C hzx,
    Finset.sum_union (Finset.disjoint_union_left.1 h).2]

end TauCeti.GridDiagram
