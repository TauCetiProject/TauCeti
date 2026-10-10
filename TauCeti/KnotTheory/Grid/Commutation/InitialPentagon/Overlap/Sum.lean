/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Initial
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.RightLeft
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.SameSum
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Terminal
public import TauCeti.KnotTheory.Grid.Commutation.TurnCut
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The rectangle--initial-pentagon overlap terms of the commutation chain-map equation

Let `C` be a validated column commutation of a grid diagram `G`, replacing the grid line
`b = finRotate n a`. In the chain-map equation of the commutation map, the coefficient of the
commutation map after the original differential counts, among others, the
rectangle--initial-side-pentagon domains: a rectangle of `G` followed by a pentagon turning on its
initial side `b`. Off the diagonal, those whose two pieces have a common side column share exactly
one, and the common column occupies one of four positions. Six families, each matched by a recut
or by reading the turn point the other way, cover these positions:

* the common initial side `b`, the pentagon ending inside the rectangle's column interval:
  `GridDiagram.initialPentagonInitialCrossOverlapSources`, recut into initial-side
  pentagon--rectangle domains;
* the common terminal side: `GridDiagram.initialPentagonTerminalOverlapSources`, recut into
  initial-side pentagon--rectangle domains;
* the rectangle starting where the pentagon ends, its recut having the turn row in its first
  rectangle: `GridDiagram.initialPentagonLeftRightOverlapSources`, recut into initial-side
  pentagon--rectangle domains;
* the rectangle ending on `b`, where the pentagon starts, and avoiding the turn row:
  `GridDiagram.initialPentagonRightLeftOverlapSources`, recut into initial-side
  pentagon--rectangle domains;
* the rectangle ending on `b` and spanning the turn row:
  `GridDiagram.rectangleInitialPentagonTurnCuts`, read at the turn point as pentagon--rectangle
  domains;
* the common initial side `b`, the rectangle ending inside the pentagon's column interval, and the
  remaining domains in which the rectangle starts where the pentagon ends: the two halves of
  `GridDiagram.initialPentagonInitialSelfPairs`
  (`GridDiagram.mem_initialPentagonInitialSelfPairs_iff_sides`), which recut into each other and
  cancel in characteristic two.

This file shows that these six families partition the off-diagonal overlap terms, so that over a
coefficient ring of characteristic two the total weight of these terms is that of their partners
on the other side of the chain-map equation.

## Main results

* `TauCeti.GridDiagram.
  filter_not_hasDisjointSides_rectangleInitialPentagonDecompositions_eq_union`: off the diagonal,
  the counted rectangle--initial-side-pentagon domains with a common side column are the union of
  the six families.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_overlap_eq_sum_partners`: off the
  diagonal and in characteristic two, the overlap terms of the rectangle--initial-side-pentagon
  sum have the total weight of the partners of the five cross families, four in the initial-side
  pentagon--rectangle sum and one in the pentagon--rectangle sum.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- Off the diagonal, a rectangle and an initial-side pentagon share a side column exactly when they
share exactly one, and never both pairs of sides. -/
private theorem initialPentagon_overlap_side_facts
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) (hzx : z ≠ x) :
    (¬D.HasDisjointSides ↔ D.first.left = D.second.left ∨ D.first.left = D.second.right ∨
        D.first.right = D.second.left ∨ D.first.right = D.second.right) ∧
      (D.HasOneCommonSide ↔ D.first.left = D.second.left ∨ D.first.left = D.second.right ∨
        D.first.right = D.second.left ∨ D.first.right = D.second.right) ∧
      ¬(D.first.left = D.second.left ∧ D.first.right = D.second.right) ∧
      ¬(D.first.left = D.second.right ∧ D.first.right = D.second.left) := by
  have hone : D.HasOneCommonSide ↔ D.first.left = D.second.left ∨
      D.first.left = D.second.right ∨ D.first.right = D.second.left ∨
        D.first.right = D.second.right := by
    constructor
    · intro hone
      rcases D.side_eq_cases_of_hasOneCommonSide hone with
        ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp only [h, true_or, or_true]
    · intro h
      obtain ⟨c, hc⟩ : ∃ c, c ∈ D.commonSideColumns := by
        rcases h with h | h | h | h
        · exact ⟨D.first.left, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.first.left, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.first.right, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
        · exact ⟨D.first.right, by simp [GridRectangleBetween.mem_sideColumns, h]⟩
      exact D.hasOneCommonSide_of_mem_commonSideColumns hc hzx
  have hdisjoint : ¬D.HasDisjointSides ↔ D.HasOneCommonSide :=
    ⟨(D.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left,
      D.not_hasDisjointSides_of_hasOneCommonSide⟩
  refine ⟨hdisjoint.trans hone, hone, fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · exact D.sideColumns_ne_of_hasOneCommonSide (hone.2 (Or.inl h₁))
      (by simp [GridRectangleBetween.sideColumns, h₁, h₂])
  · exact D.sideColumns_ne_of_hasOneCommonSide (hone.2 (Or.inr (Or.inl h₁)))
      (by simp [GridRectangleBetween.sideColumns, h₁, h₂, Finset.pair_comm])

/-- The column order of the three side columns of a rectangle--initial-side-pentagon domain whose
two pieces have different terminal sides, the rectangle not ending where the pentagon starts:
exactly one of the two terminal sides lies strictly between the pentagon's initial side and the
other. -/
private theorem initialPentagon_overlap_column_order
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    (D.first.right ≠ D.second.right → D.first.right ≠ D.second.left →
        D.second.right ∈ Grid.cIoo D.second.left D.first.right ∨
          D.first.right ∈ Grid.cIoo D.second.left D.second.right) ∧
      ¬(D.second.right ∈ Grid.cIoo D.second.left D.first.right ∧
          D.first.right ∈ Grid.cIoo D.second.left D.second.right) := by
  refine ⟨fun hright hleft => ?_, fun ⟨hP, hr⟩ => ?_⟩
  · rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff D.second.left_ne_right).2 ⟨hleft, hright⟩
      with h | h
    · exact Or.inr h
    · exact Or.inl (Grid.mem_cIoo_cyclic_right h)
  · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hr (Grid.mem_cIoo_cyclic_left hP)

open scoped Classical in
/-- Off the diagonal, the counted rectangle--initial-side-pentagon domains whose two pieces have a
common side column are the union of the six overlap families. -/
theorem filter_not_hasDisjointSides_rectangleInitialPentagonDecompositions_eq_union
    (hzx : z ≠ x) :
    (G.rectangleInitialPentagonDecompositions C x z).filter (fun D => ¬D.HasDisjointSides) =
      G.initialPentagonInitialCrossOverlapSources C x z ∪
        G.initialPentagonTerminalOverlapSources C x z ∪
          G.initialPentagonLeftRightOverlapSources C x z ∪
            G.initialPentagonRightLeftOverlapSources C x z ∪
              G.rectangleInitialPentagonTurnCuts C x z ∪
                G.initialPentagonInitialSelfPairs C x z := by
  ext D
  obtain ⟨hdisjoint, hone, hsame, hmixed⟩ := G.initialPentagon_overlap_side_facts C D hzx
  obtain ⟨horder, hexclusive⟩ := G.initialPentagon_overlap_column_order C D
  have hb := D.second_left_eq
  have hr := D.first.left_ne_right
  have hP := D.second.left_ne_right
  simp only [Finset.mem_filter, Finset.mem_union, mem_initialPentagonInitialCrossOverlapSources,
    mem_initialPentagonTerminalOverlapSources, mem_initialPentagonLeftRightOverlapSources,
    mem_initialPentagonRightLeftOverlapSources, mem_rectangleInitialPentagonTurnCuts,
    mem_initialPentagonInitialSelfPairs_iff_sides, hdisjoint, hone]
  -- The position of the common column, the column order of the two terminal sides, and the
  -- position of the turn row sort each domain into one of the families.
  grind

open scoped Classical in
/-- Off the diagonal, the six overlap families of rectangle--initial-side-pentagon domains are
pairwise disjoint: each is disjoint from the union of those listed before it in
`filter_not_hasDisjointSides_rectangleInitialPentagonDecompositions_eq_union`. -/
theorem disjoint_initialPentagon_overlap_families (hzx : z ≠ x) :
    Disjoint (G.initialPentagonInitialCrossOverlapSources C x z ∪
        G.initialPentagonTerminalOverlapSources C x z ∪
          G.initialPentagonLeftRightOverlapSources C x z ∪
            G.initialPentagonRightLeftOverlapSources C x z ∪
              G.rectangleInitialPentagonTurnCuts C x z)
        (G.initialPentagonInitialSelfPairs C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapSources C x z ∪
        G.initialPentagonTerminalOverlapSources C x z ∪
          G.initialPentagonLeftRightOverlapSources C x z ∪
            G.initialPentagonRightLeftOverlapSources C x z)
        (G.rectangleInitialPentagonTurnCuts C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapSources C x z ∪
        G.initialPentagonTerminalOverlapSources C x z ∪
          G.initialPentagonLeftRightOverlapSources C x z)
        (G.initialPentagonRightLeftOverlapSources C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapSources C x z ∪
        G.initialPentagonTerminalOverlapSources C x z)
        (G.initialPentagonLeftRightOverlapSources C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapSources C x z)
        (G.initialPentagonTerminalOverlapSources C x z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.2 fun D h₁ h₂ => ?_ <;>
  · obtain ⟨-, hone, hsame, hmixed⟩ := G.initialPentagon_overlap_side_facts C D hzx
    obtain ⟨-, hexclusive⟩ := G.initialPentagon_overlap_column_order C D
    have hb := D.second_left_eq
    have hr := D.first.left_ne_right
    have hP := D.second.left_ne_right
    simp only [Finset.mem_union, mem_initialPentagonInitialCrossOverlapSources,
      mem_initialPentagonTerminalOverlapSources, mem_initialPentagonLeftRightOverlapSources,
      mem_initialPentagonRightLeftOverlapSources, mem_rectangleInitialPentagonTurnCuts,
      mem_initialPentagonInitialSelfPairs_iff_sides, hone] at h₁ h₂
    -- Two families never prescribe the same position of the common column, column order, and
    -- position of the turn row.
    grind

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- Off the diagonal and over a coefficient ring of characteristic two, the counted
rectangle--initial-side-pentagon domains whose two pieces have a common side column have the total
weight of the partners of the overlap families: the initial-side-pentagon--rectangle recuts of the
common-initial-side cross, common-terminal-side, and mixed sources, and the pentagon--rectangle
readings of the domains cut at the turn point. The same-sum pairs cancel among themselves. -/
theorem sum_rectangleInitialPentagonWeight_overlap_eq_sum_partners (hzx : z ≠ x) :
    ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
        (fun D => ¬D.HasDisjointSides), G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.initialPentagonInitialCrossOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E +
        ∑ E ∈ G.initialPentagonTerminalOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E +
        ∑ E ∈ G.initialPentagonLeftRightOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E +
        ∑ E ∈ G.initialPentagonRightLeftOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E +
        ∑ E ∈ G.pentagonRectangleTurnCuts C x z, G.pentagonRectangleWeight C R E := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := G.disjoint_initialPentagon_overlap_families C hzx
  rw [G.filter_not_hasDisjointSides_rectangleInitialPentagonDecompositions_eq_union C hzx,
    Finset.sum_union h₁, Finset.sum_union h₂, Finset.sum_union h₃, Finset.sum_union h₄,
    Finset.sum_union h₅, G.sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero C R x z,
    add_zero,
    G.sum_rectangleInitialPentagonWeight_initialCrossOverlapSources_eq_sum_partners C x z R,
    G.sum_rectangleInitialPentagonWeight_terminalOverlapSources_eq_sum_partners C x z R,
    G.sum_rectangleInitialPentagonWeight_leftRightOverlapSources_eq_sum_partners C x z R,
    G.sum_rectangleInitialPentagonWeight_rightLeftOverlapSources_eq_sum_partners C x z R,
    G.sum_rectangleInitialPentagonWeight_turnCuts_eq_sum_pentagonRectangleWeight C x z R]

end TauCeti.GridDiagram
