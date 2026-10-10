/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Basic
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Initial.Sum
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.LeftRight
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Cross.Sum
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Mixed
public import TauCeti.KnotTheory.Grid.Commutation.TurnCut
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The rectangle--pentagon overlap terms of the commutation chain-map equation

Let `C` be a validated column commutation of a grid diagram `G`, replacing the grid line
`b = finRotate n a`. In the chain-map equation of the commutation map, the coefficient of the
commutation map after the original differential counts, among others, the rectangle--pentagon
domains: a rectangle of `G` followed by a pentagon turning on its terminal side `b`. Off the
diagonal, those whose two pieces have a common side column share exactly one, and the common
column occupies one of four positions. Six families, each matched by a recut or by reading the
turn point the other way, cover these positions:

* the common initial side: `GridDiagram.initialOverlapSources`, recut into pentagon--rectangle
  domains;
* the common terminal side, the pentagon starting inside the rectangle's column interval:
  `GridDiagram.terminalCrossOverlapSources`, recut into pentagon--rectangle domains;
* the rectangle starting on `b`, where the pentagon ends, and avoiding the turn row:
  `GridDiagram.leftRightOverlapSources`, recut into pentagon--rectangle domains;
* the rectangle ending where the pentagon starts, the turn row lying in the rows from the
  rectangle's top to the pentagon's top: `GridDiagram.rightLeftOverlapSources`, recut into
  pentagon--rectangle domains;
* the rectangle starting on `b` and spanning the turn row: `GridDiagram.rectanglePentagonTurnCuts`,
  read at the turn point as initial-side-pentagon--rectangle domains;
* the common terminal side, the rectangle starting inside the pentagon's column interval, and the
  remaining domains in which the rectangle ends where the pentagon starts: the two halves of
  `GridDiagram.terminalSelfPairs` (`GridDiagram.mem_terminalSelfPairs_iff_sides`), which recut
  into each other and cancel in characteristic two.

This file shows that these six families partition the off-diagonal overlap terms, so that over a
coefficient ring of characteristic two the total weight of these terms is that of their partners
on the other side of the chain-map equation.

## Main results

* `TauCeti.GridDiagram.filter_not_hasDisjointSides_rectanglePentagonDecompositions_eq_union`:
  off the diagonal, the counted rectangle--pentagon domains with a common side column are the
  union of the six families.
* `TauCeti.GridDiagram.sum_rectanglePentagonWeight_overlap_eq_sum_partners`: off the diagonal and
  in characteristic two, the overlap terms of the rectangle--pentagon sum have the total weight of
  the partners of the five cross families, four in the pentagon--rectangle sum and one in the
  initial-side-pentagon--rectangle sum.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- Off the diagonal, a rectangle and a pentagon share a side column exactly when they share exactly
one, and never both pairs of sides. -/
private theorem overlap_side_facts
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) (hzx : z ≠ x) :
    (¬D.HasDisjointSides ↔ D.rectangle.left = D.pentagon.left ∨
        D.rectangle.left = D.pentagon.right ∨ D.rectangle.right = D.pentagon.left ∨
          D.rectangle.right = D.pentagon.right) ∧
      (D.toRectangleDecomposition.HasOneCommonSide ↔ D.rectangle.left = D.pentagon.left ∨
        D.rectangle.left = D.pentagon.right ∨ D.rectangle.right = D.pentagon.left ∨
          D.rectangle.right = D.pentagon.right) ∧
      ¬(D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right) ∧
      ¬(D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left) := by
  have hone : D.toRectangleDecomposition.HasOneCommonSide ↔ D.rectangle.left = D.pentagon.left ∨
      D.rectangle.left = D.pentagon.right ∨ D.rectangle.right = D.pentagon.left ∨
        D.rectangle.right = D.pentagon.right := by
    constructor
    · intro hone
      rcases D.toRectangleDecomposition.side_eq_cases_of_hasOneCommonSide hone with
        ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right] at h <;>
        simp only [h, true_or, or_true]
    · intro h
      obtain ⟨c, hc⟩ : ∃ c, c ∈ D.toRectangleDecomposition.commonSideColumns := by
        rcases h with h | h | h | h
        · exact ⟨D.rectangle.left, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.rectangle.left, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.rectangle.right, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.rectangle.right, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
      exact D.toRectangleDecomposition.hasOneCommonSide_of_mem_commonSideColumns hc hzx
  have hdisjoint : ¬D.HasDisjointSides ↔ D.toRectangleDecomposition.HasOneCommonSide := by
    rw [D.hasDisjointSides_def]
    exact ⟨(D.toRectangleDecomposition.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left,
      D.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide⟩
  refine ⟨hdisjoint.trans hone, hone, fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · exact D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide (hone.2 (Or.inl h₁))
      (by simp [GridRectangleBetween.sideColumns, h₁, h₂])
  · exact D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide
      (hone.2 (Or.inr (Or.inl h₁))) (by simp [GridRectangleBetween.sideColumns, h₁, h₂,
        Finset.pair_comm])

/-- The column order of the three side columns of a rectangle--pentagon domain whose two pieces
have different initial sides, the rectangle not starting on the pentagon's terminal side: exactly
one of the two initial sides lies strictly between the other and the pentagon's terminal side. -/
private theorem overlap_column_order
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    (D.rectangle.left ≠ D.pentagon.left → D.rectangle.left ≠ D.pentagon.right →
        D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right ∨
          D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right) ∧
      ¬(D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right ∧
          D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right) := by
  refine ⟨fun hleft hright => ?_, fun ⟨hP, hr⟩ => ?_⟩
  · rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff hright).2 ⟨hleft.symm, D.pentagon.left_ne_right⟩
      with h | h
    · exact Or.inl h
    · exact Or.inr (Grid.mem_cIoo_cyclic_left h)
  · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hr (Grid.mem_cIoo_cyclic_right hP)

open scoped Classical in
/-- Off the diagonal, the counted rectangle--pentagon domains whose two pieces have a common side
column are the union of the six overlap families. -/
theorem filter_not_hasDisjointSides_rectanglePentagonDecompositions_eq_union (hzx : z ≠ x) :
    (G.rectanglePentagonDecompositions C x z).filter (fun D => ¬D.HasDisjointSides) =
      G.initialOverlapSources C x z ∪ G.terminalCrossOverlapSources C x z ∪
        G.leftRightOverlapSources C x z ∪ G.rightLeftOverlapSources C x z ∪
          G.rectanglePentagonTurnCuts C x z ∪ G.terminalSelfPairs C x z := by
  ext D
  obtain ⟨hdisjoint, hone, hsame, _⟩ := G.overlap_side_facts C D hzx
  obtain ⟨horder, hexclusive⟩ := G.overlap_column_order C D
  have hb := D.pentagon.right_eq
  have hr := D.rectangle.left_ne_right
  have hP := D.pentagon.left_ne_right
  have hPl : D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right →
      D.pentagon.left ≠ D.rectangle.left := Grid.ne_left_of_mem_cIoo
  simp only [Finset.mem_filter, Finset.mem_union, mem_initialOverlapSources,
    mem_terminalCrossOverlapSources, mem_terminalSelfPairs_iff_sides, mem_rightLeftOverlapSources,
    mem_leftRightOverlapSources, mem_rectanglePentagonTurnCuts, hdisjoint, hone]
  -- The position of the common column, the column order of the two initial sides, and the
  -- position of the turn row sort each domain into one of the families.
  grind

open scoped Classical in
/-- Off the diagonal, the six overlap families of rectangle--pentagon domains are pairwise
disjoint: each is disjoint from the union of those listed before it in
`filter_not_hasDisjointSides_rectanglePentagonDecompositions_eq_union`. -/
private theorem disjoint_overlap_families (hzx : z ≠ x) :
    Disjoint (G.initialOverlapSources C x z ∪ G.terminalCrossOverlapSources C x z ∪
        G.leftRightOverlapSources C x z ∪ G.rightLeftOverlapSources C x z ∪
          G.rectanglePentagonTurnCuts C x z) (G.terminalSelfPairs C x z) ∧
      Disjoint (G.initialOverlapSources C x z ∪ G.terminalCrossOverlapSources C x z ∪
        G.leftRightOverlapSources C x z ∪ G.rightLeftOverlapSources C x z)
          (G.rectanglePentagonTurnCuts C x z) ∧
      Disjoint (G.initialOverlapSources C x z ∪ G.terminalCrossOverlapSources C x z ∪
        G.leftRightOverlapSources C x z) (G.rightLeftOverlapSources C x z) ∧
      Disjoint (G.initialOverlapSources C x z ∪ G.terminalCrossOverlapSources C x z)
        (G.leftRightOverlapSources C x z) ∧
      Disjoint (G.initialOverlapSources C x z) (G.terminalCrossOverlapSources C x z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.2 fun D h₁ h₂ => ?_ <;>
  · obtain ⟨-, hone, hsame, hmixed⟩ := G.overlap_side_facts C D hzx
    obtain ⟨-, hexclusive⟩ := G.overlap_column_order C D
    have hb := D.pentagon.right_eq
    have hr := D.rectangle.left_ne_right
    have hP := D.pentagon.left_ne_right
    have hPl : D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right →
        D.pentagon.left ≠ D.rectangle.left := Grid.ne_left_of_mem_cIoo
    simp only [Finset.mem_union, mem_initialOverlapSources, mem_terminalCrossOverlapSources,
      mem_terminalSelfPairs_iff_sides, mem_rightLeftOverlapSources, mem_leftRightOverlapSources,
      mem_rectanglePentagonTurnCuts, hone] at h₁ h₂
    -- Two families never prescribe the same position of the common column, column order, and
    -- position of the turn row.
    grind

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- Off the diagonal and over a coefficient ring of characteristic two, the counted
rectangle--pentagon domains whose two pieces have a common side column have the total weight of
the partners of the overlap families: the pentagon--rectangle recuts of the common-initial-side,
terminal cross, and mixed sources, and the initial-side-pentagon--rectangle readings of the
domains cut at the turn point. The terminal self-pairs cancel among themselves. -/
theorem sum_rectanglePentagonWeight_overlap_eq_sum_partners (hzx : z ≠ x) :
    ∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter (fun D => ¬D.HasDisjointSides),
        G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R E +
        ∑ E ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R E +
        ∑ E ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R E +
        ∑ E ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R E +
        ∑ E ∈ G.initialPentagonRectangleTurnCuts C x z,
          G.initialPentagonRectangleWeight C R E := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := G.disjoint_overlap_families C hzx
  rw [G.filter_not_hasDisjointSides_rectanglePentagonDecompositions_eq_union C hzx,
    Finset.sum_union h₁, Finset.sum_union h₂, Finset.sum_union h₃, Finset.sum_union h₄,
    Finset.sum_union h₅, G.sum_rectanglePentagonWeight_terminalSelfPairs_eq_zero C R x z, add_zero,
    G.sum_rectanglePentagonWeight_initialOverlapSources_eq_sum_pentagonRectangleWeight_partners
      C R x z,
    G.sum_rectanglePentagonWeight_terminalCrossOverlapSources_eq_sum_partners C R x z,
    G.sum_rectanglePentagonWeight_leftRightOverlapSources_eq_sum_partners C x z R,
    G.sum_rectanglePentagonWeight_rightLeftOverlapSources_eq_sum_partners C x z R,
    G.sum_rectanglePentagonWeight_turnCuts_eq_sum_initialPentagonRectangleWeight C x z R]

end TauCeti.GridDiagram
