/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Initial.Partners
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.PentagonInitial.Mixed
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Terminal.Partners
public import TauCeti.KnotTheory.Grid.Commutation.TurnCut

/-!
# The residual mixed initial-side pentagon--rectangle terms of grid commutation

An initial-side commutation pentagon followed by a rectangle has two mixed orientations of its
unique common side column. If the rectangle ends on the replaced line, where the pentagon
starts, the two pieces share their top row, and the position of the turn row relative to the
rectangle's bottom row identifies the domain as a terminal-overlap recut partner or a turn cut.
If the rectangle starts where the pentagon ends, the two pieces share their bottom row; the
order of their top rows and the position of the turn row identify the domain as a
terminal-overlap recut partner, a common-initial-side cross partner, or the mixed member of an
initial-side self-pair.

This file partitions the off-diagonal mixed-side terms into these four disjoint families.
After removing the two recut partner families, only the turn cuts and the mixed initial-side
self-pairs remain. The resulting sum formula supplies the initial-side-pentagon mixed-side
contribution in `GridDiagram.commutationMap_comp_unblockedDifferential_eq_iff_oriented_overlap`.
The mixed members of the self-pairs are retained: their cancelling partners have same-side
overlap, so their mixed-side sum alone need not vanish.

## Main results

* `GridDiagram.filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_eq_union`:
  the off-diagonal mixed-side terms are the disjoint union of the four families.
* `GridDiagram.sum_initialPentagonRectangle_mixedSide_eq_sum_partners_add_turnCuts_add_selfPairs`:
  the corresponding splitting of any additive weight.
* `GridDiagram.sum_initialPentagonRectangle_mixedSide_sdiff_partners_eq_sum_turnCuts_add_selfPairs`:
  the residual sum after removing the two recut partner families.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The terminal-side analogue is
`TauCeti.KnotTheory.Grid.Commutation.Overlap.Residual.TerminalMixed`, whose structure this file
follows.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

private theorem initialMixed_side_facts
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) (hzx : z ≠ x) :
    (E.toGridRectangleDecomposition.HasMixedSideOverlap ↔
        E.first.left = E.second.right ∨ E.first.right = E.second.left) ∧
      ((E.first.left = E.second.right ∨ E.first.right = E.second.left) →
        E.toGridRectangleDecomposition.HasOneCommonSide) ∧
      ¬(E.first.left = E.second.right ∧ E.first.right = E.second.left) := by
  have hone (h : E.first.left = E.second.right ∨ E.first.right = E.second.left) :
      E.toGridRectangleDecomposition.HasOneCommonSide := by
    obtain ⟨c, hc⟩ : ∃ c, c ∈ E.toGridRectangleDecomposition.commonSideColumns := by
      rcases h with h | h
      · exact ⟨E.first.left, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
      · exact ⟨E.first.right, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
    exact E.toGridRectangleDecomposition.hasOneCommonSide_of_mem_commonSideColumns hc hzx
  rw [GridRectangleDecomposition.hasMixedSideOverlap_iff]
  refine ⟨⟨fun h => h.2, fun h => ⟨hone h, h⟩⟩, hone, fun ⟨hl, hr⟩ => ?_⟩
  exact E.toGridRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide (hone (Or.inl hl))
    (by simp [GridRectangleBetween.sideColumns, hl, hr, Finset.pair_comm])

/-- When the rectangle ends where the pentagon starts, the turn row lies in the rectangle's rows
exactly when it is not cut off below the rectangle's bottom row inside the pentagon's rows. -/
private theorem initialMixed_left_eq_right_rows
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.left = E.second.right) (hother : E.first.right ≠ E.second.left) :
    C.turnRow ∈ Grid.cIco E.second.bottom E.second.top ↔
      ¬(E.second.bottom ∈ Grid.cIoo E.first.bottom E.first.top ∧
        C.turnRow ∈ Grid.cIco E.first.bottom E.second.bottom) := by
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  have htop : E.second.top = E.first.top := by
    rw [GridRectangleBetween.top_def, ← hcommon, E.first.map_left, GridRectangleBetween.top_def]
  have hturn := E.first_turn_mem
  rw [htop]
  rcases (E.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_right hcommon hother
    hfirst hsecond).2 with hrow | hrow
  · -- The pentagon's rows lie inside the rectangle's rows, which contain the turn row.
    refine iff_of_true (Grid.cIco_subset_of_mem_cIoo hrow hturn) fun h => ?_
    exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.bottom E.first.top) h.1
      (Grid.mem_cIoo_cyclic_right hrow)
  · -- The rectangle's bottom row cuts the pentagon's rows into two disjoint arcs.
    have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow
    have hdisjoint := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
    rw [← hunion, Finset.mem_union] at hturn
    constructor
    · exact fun h h' => Finset.disjoint_left.mp hdisjoint h'.2 h
    · exact fun h => hturn.resolve_left fun h' => h ⟨hrow, h'⟩

/-- When the rectangle starts where the pentagon ends, the two top rows occur in exactly one
cyclic order, and if the pentagon's top comes first the turn row lies in the arc from the
rectangle's top to the pentagon's top. -/
private theorem initialMixed_right_eq_left_rows
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.right = E.second.left) (hother : E.first.left ≠ E.second.right) :
    (E.first.top ∈ Grid.cIoo E.first.bottom E.second.top ∨
        E.second.top ∈ Grid.cIoo E.first.bottom E.first.top) ∧
      ¬(E.first.top ∈ Grid.cIoo E.first.bottom E.second.top ∧
        E.second.top ∈ Grid.cIoo E.first.bottom E.first.top) ∧
      (E.first.top ∈ Grid.cIoo E.first.bottom E.second.top →
        C.turnRow ∈ Grid.cIco E.second.top E.first.top) := by
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  refine ⟨(E.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_left hcommon hother
    hfirst hsecond).2, fun ⟨h₁, h₂⟩ => ?_, fun h => ?_⟩
  · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.bottom E.first.top) h₂
      (Grid.mem_cIoo_cyclic_left h₁)
  · exact Grid.cIco_subset_of_mem_cIoo (Grid.mem_cIoo_cyclic_right h) E.first_turn_mem

open scoped Classical in
/-- Off the diagonal, the mixed-side initial-side pentagon--rectangle terms are the disjoint
union of the common-initial-side cross partners, terminal-overlap partners, turn cuts, and mixed
initial-side self-pairs. -/
theorem filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_eq_union
    (hzx : z ≠ x) :
    (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap) =
      G.initialPentagonInitialCrossOverlapPartners C x z ∪
          G.initialPentagonTerminalOverlapPartners C x z ∪
        G.initialPentagonRectangleTurnCuts C x z ∪
          (G.initialPentagonRectangleInitialSelfPairs C x z).filter
            (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap) := by
  ext E
  obtain ⟨hmixed, hone, hother⟩ := G.initialMixed_side_facts C E hzx
  have hleft := G.initialMixed_left_eq_right_rows C E
  have hright := G.initialMixed_right_eq_left_rows C E
  have hb := E.first_left_eq
  have hp := E.first.left_ne_right
  have hr := E.second.left_ne_right
  simp only [Finset.mem_filter, Finset.mem_union,
    mem_initialPentagonInitialCrossOverlapPartners_iff_sides,
    mem_initialPentagonTerminalOverlapPartners_iff_sides, mem_initialPentagonRectangleTurnCuts,
    mem_initialPentagonRectangleInitialSelfPairs_iff_sides, hmixed]
  -- Column orientation fixes the branch; row order and the turn row distinguish its families.
  grind

open scoped Classical in
private theorem disjoint_initialMixed_families (hzx : z ≠ x) :
    Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z ∪
        G.initialPentagonTerminalOverlapPartners C x z ∪ G.initialPentagonRectangleTurnCuts C x z)
      ((G.initialPentagonRectangleInitialSelfPairs C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap)) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z ∪
          G.initialPentagonTerminalOverlapPartners C x z)
        (G.initialPentagonRectangleTurnCuts C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z)
        (G.initialPentagonTerminalOverlapPartners C x z) := by
  refine ⟨?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.2 fun E h₁ h₂ => ?_ <;>
  · obtain ⟨hmixed, hone, hother⟩ := G.initialMixed_side_facts C E hzx
    have hleft := G.initialMixed_left_eq_right_rows C E
    have hright := G.initialMixed_right_eq_left_rows C E
    have hb := E.first_left_eq
    have hp := E.first.left_ne_right
    have hr := E.second.left_ne_right
    simp only [Finset.mem_filter, Finset.mem_union,
      mem_initialPentagonInitialCrossOverlapPartners_iff_sides,
      mem_initialPentagonTerminalOverlapPartners_iff_sides, mem_initialPentagonRectangleTurnCuts,
      mem_initialPentagonRectangleInitialSelfPairs_iff_sides, hmixed] at h₁ h₂
    grind

open scoped Classical in
/-- The initial-side-pentagon mixed-side contribution is the sum of its two recut partner
families, turn cuts, and mixed initial-side self-pairs. This identity holds for any additive
weights. -/
theorem sum_initialPentagonRectangle_mixedSide_eq_sum_partners_add_turnCuts_add_selfPairs
    {M : Type*} [AddCommMonoid M]
    (w : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ E ∈ (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap), w E =
      (∑ E ∈ G.initialPentagonInitialCrossOverlapPartners C x z, w E) +
        (∑ E ∈ G.initialPentagonTerminalOverlapPartners C x z, w E) +
          (∑ E ∈ G.initialPentagonRectangleTurnCuts C x z, w E) +
            ∑ E ∈ (G.initialPentagonRectangleInitialSelfPairs C x z).filter
              (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap), w E := by
  obtain ⟨h₁, h₂, h₃⟩ := G.disjoint_initialMixed_families C hzx
  rw [G.filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_eq_union C hzx,
    Finset.sum_union h₁, Finset.sum_union h₂, Finset.sum_union h₃]

open scoped Classical in
/-- Removing the two recut partner families from the mixed-side initial-side
pentagon--rectangle terms leaves exactly the turn cuts and mixed initial-side self-pairs. -/
theorem filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_sdiff_partners_eq_union
    (hzx : z ≠ x) :
    (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap) \
      (G.initialPentagonInitialCrossOverlapPartners C x z ∪
        G.initialPentagonTerminalOverlapPartners C x z) =
        G.initialPentagonRectangleTurnCuts C x z ∪
          (G.initialPentagonRectangleInitialSelfPairs C x z).filter
            (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap) := by
  obtain ⟨h₁, h₂, -⟩ := G.disjoint_initialMixed_families C hzx
  have hdisjoint : Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z ∪
      G.initialPentagonTerminalOverlapPartners C x z)
      (G.initialPentagonRectangleTurnCuts C x z ∪
        (G.initialPentagonRectangleInitialSelfPairs C x z).filter
          (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap)) :=
    Finset.disjoint_union_right.2 ⟨h₂, (Finset.disjoint_union_left.1 h₁).1⟩
  rw [G.filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_eq_union C hzx,
    Finset.union_assoc, Finset.union_sdiff_cancel_left hdisjoint]

open scoped Classical in
/-- The residual mixed-side initial-side pentagon--rectangle sum retains the turn-cut weights and
the mixed initial-side self-pair weights after both recut partner families have been removed. -/
theorem sum_initialPentagonRectangle_mixedSide_sdiff_partners_eq_sum_turnCuts_add_selfPairs
    {M : Type*} [AddCommMonoid M]
    (w : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ E ∈ (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap) \
        (G.initialPentagonInitialCrossOverlapPartners C x z ∪
          G.initialPentagonTerminalOverlapPartners C x z), w E =
      (∑ E ∈ G.initialPentagonRectangleTurnCuts C x z, w E) +
        ∑ E ∈ (G.initialPentagonRectangleInitialSelfPairs C x z).filter
          (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap), w E := by
  obtain ⟨h, -, -⟩ := G.disjoint_initialMixed_families C hzx
  rw [G.filter_hasMixedSideOverlap_initialPentagonRectangleDecompositions_sdiff_partners_eq_union
      C hzx,
    Finset.sum_union (Finset.disjoint_union_left.1 h).2]

end TauCeti.GridDiagram
