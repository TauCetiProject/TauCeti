/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# Unknotting numbers of torus link grids

This file bounds the unknotting number (`GridLink.unknottingNumber`) of the grid links presented
by the standard grids of small torus links. The Hopf link has unknotting number `⊤`, since it has
two components. The trefoil, presented by the standard `5 × 5` grid of the `(2, 3)` torus knot, is
unknotted by a single crossing change, and the `(3, 4)` torus knot, presented by its standard
`7 × 7` grid, by three. These are the upper bounds `u(T_{p,q}) ≤ (p - 1) (q - 1) / 2` of the
Milnor conjecture for these two torus knots, obtained from explicit sequences of
cross-commutations and commutations.

## Main results

* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_one`: the Hopf link has unknotting
  number `⊤`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_le_one`: the trefoil has
  unknotting number at most one.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`: the `(3, 4)` torus
  knot has unknotting number at most three.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes as cross-commutations and the unknotting
  number.
-/

public section

namespace TauCeti

namespace GridLink

/-- The Hopf link, presented by the standard `4 × 4` grid of the `(2, 2)` torus link, has
unknotting number `⊤`: it has two components, so no sequence of crossing changes reaches the
unknot. -/
theorem unknottingNumber_toGridLink_torusLink_one_one :
    (GridDiagram.torusLink 1 1).toGridLink.unknottingNumber = ⊤ := by
  by_contra h
  have := isKnot_of_unknottingNumber_ne_top h
  rw [isKnot_toGridLink] at this
  exact GridDiagram.not_isKnot_torusLink_one_one this

/-- The standard `5 × 5` grid of the `(2, 3)` torus knot with its markings made explicit. -/
private def trefoilGrid : GridDiagram 5 where
  O := ⟨1⟩
  X := ⟨finRotate 5 ^ 3⟩
  disjoint := by decide

private theorem torusLink_one_two_eq_trefoilGrid : GridDiagram.torusLink 1 2 = trefoilGrid := by
  ext c <;> simp [trefoilGrid]

/-- The standard `5 × 5` unknot grid with its markings made explicit. -/
private def unknotGrid : GridDiagram 5 where
  O := ⟨1⟩
  X := ⟨finRotate 5⟩
  disjoint := by decide

private theorem unknot_three_eq_unknotGrid : GridDiagram.unknot 3 = unknotGrid := by
  ext c <;> simp [unknotGrid]

/-- The trefoil, presented by the standard `5 × 5` grid of the `(2, 3)` torus knot, has unknotting
number at most one. Exchanging its first two columns is a cross-commutation, and five
commutations turn the result into the standard `5 × 5` unknot grid. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_le_one :
    (GridDiagram.torusLink 1 2).toGridLink.unknottingNumber ≤ 1 := by
  rw [torusLink_one_two_eq_trefoilGrid]
  set G₀ := trefoilGrid.swapColumns 0 (finRotate 5 0)
  set G₁ := G₀.swapRows 0 (finRotate 5 0)
  set G₂ := G₁.swapRows 1 (finRotate 5 1)
  set G₃ := G₂.swapColumns 1 (finRotate 5 1)
  set G₄ := G₃.swapRows 4 (finRotate 5 4)
  have hcross : trefoilGrid.toGridLink.unknottingNumber ≤ G₀.toGridLink.unknottingNumber + 1 :=
    trefoilGrid.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 0) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have hmoves : G₀.MovesTo (GridDiagram.unknot 3) := by
    have h₅ : G₄.swapColumns 4 (finRotate 5 4) = GridDiagram.unknot 3 := by
      rw [unknot_three_eq_unknotGrid]
      ext c
      all_goals revert c; decide
    rw [← h₅]
    -- Each step exchanges an adjacent non-interleaving pair of rows or columns.
    refine (G₀.movesTo_swapRows 0 ?_).trans <|
      (G₁.movesTo_swapRows 1 ?_).trans <|
      (G₂.movesTo_swapColumns 1 ?_).trans <|
      (G₃.movesTo_swapRows 4 ?_).trans <| G₄.movesTo_swapColumns 4 ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  calc trefoilGrid.toGridLink.unknottingNumber ≤ G₀.toGridLink.unknottingNumber + 1 := hcross
    _ = 1 := by
      rw [(G₀.toGridLink_eq_iff_movesTo).mpr hmoves, GridDiagram.toGridLink_unknot,
        unknottingNumber_unknot, zero_add]

/-- The standard `7 × 7` grid of the `(3, 4)` torus knot with its markings made explicit. -/
private def torusTwoThreeGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7 ^ 4⟩
  disjoint := by decide

private theorem torusLink_two_three_eq_torusTwoThreeGrid :
    GridDiagram.torusLink 2 3 = torusTwoThreeGrid := by
  ext c <;> simp [torusTwoThreeGrid]

/-- The standard `7 × 7` unknot grid with its markings made explicit. -/
private def unknotSevenGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7⟩
  disjoint := by decide

private theorem unknot_five_eq_unknotSevenGrid : GridDiagram.unknot 5 = unknotSevenGrid := by
  ext c <;> simp [unknotSevenGrid]

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number at most
three. Three cross-commutations of adjacent columns, interspersed with nine commutations, turn
it into the standard `7 × 7` unknot grid.

This is the upper bound `u(T_{3,4}) ≤ (3 - 1) (4 - 1) / 2` of the Milnor conjecture for this torus
knot. -/
theorem unknottingNumber_toGridLink_torusLink_two_three_le_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber ≤ 3 := by
  rw [torusLink_two_three_eq_torusTwoThreeGrid]
  -- The diagrams `G₁`, `G₃` and `G₇` are reached by a cross-commutation (`h₁`, `h₃`, `h₇`), each
  -- of the others by a commutation; the commutations are grouped into the move sequences `h₂`,
  -- `h₆` and `h₁₂`, the last of which ends at the standard unknot grid.
  set G₁ := torusTwoThreeGrid.swapColumns 0 (finRotate 7 0)
  set G₂ := G₁.swapRows 0 (finRotate 7 0)
  set G₃ := G₂.swapColumns 1 (finRotate 7 1)
  set G₄ := G₃.swapRows 1 (finRotate 7 1)
  set G₅ := G₄.swapRows 2 (finRotate 7 2)
  set G₆ := G₅.swapColumns 2 (finRotate 7 2)
  set G₇ := G₆.swapColumns 6 (finRotate 7 6)
  set G₈ := G₇.swapRows 6 (finRotate 7 6)
  set G₉ := G₈.swapRows 0 (finRotate 7 0)
  set G₁₀ := G₉.swapColumns 0 (finRotate 7 0)
  set G₁₁ := G₁₀.swapRows 5 (finRotate 7 5)
  have h₁ : torusTwoThreeGrid.toGridLink.unknottingNumber ≤ G₁.toGridLink.unknottingNumber + 1 :=
    torusTwoThreeGrid.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 0) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₃ : G₂.toGridLink.unknottingNumber ≤ G₃.toGridLink.unknottingNumber + 1 :=
    G₂.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 1) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₇ : G₆.toGridLink.unknottingNumber ≤ G₇.toGridLink.unknottingNumber + 1 :=
    G₆.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 6) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₂ : G₁.MovesTo G₂ := G₁.movesTo_swapRows 0 (by
    simp only [GridDiagram.RowsNoninterleaving, Grid.Noninterleaving, Grid.mem_cIoo]
    decide)
  have h₆ : G₃.MovesTo G₆ := by
    refine (G₃.movesTo_swapRows 1 ?_).trans <|
      (G₄.movesTo_swapRows 2 ?_).trans <| G₅.movesTo_swapColumns 2 ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  have h₁₂ : G₇.MovesTo (GridDiagram.unknot 5) := by
    have h : G₁₁.swapColumns 5 (finRotate 7 5) = GridDiagram.unknot 5 := by
      rw [unknot_five_eq_unknotSevenGrid]
      ext c
      all_goals revert c; decide
    rw [← h]
    refine (G₇.movesTo_swapRows 6 ?_).trans <|
      (G₈.movesTo_swapRows 0 ?_).trans <|
      (G₉.movesTo_swapColumns 0 ?_).trans <|
      (G₁₀.movesTo_swapRows 5 ?_).trans <| G₁₁.movesTo_swapColumns 5 ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  calc torusTwoThreeGrid.toGridLink.unknottingNumber
      ≤ G₁.toGridLink.unknottingNumber + 1 := h₁
    _ = G₂.toGridLink.unknottingNumber + 1 := by rw [(G₁.toGridLink_eq_iff_movesTo).mpr h₂]
    _ ≤ G₃.toGridLink.unknottingNumber + 1 + 1 := by gcongr
    _ = G₆.toGridLink.unknottingNumber + 1 + 1 := by rw [(G₃.toGridLink_eq_iff_movesTo).mpr h₆]
    _ ≤ G₇.toGridLink.unknottingNumber + 1 + 1 + 1 := by gcongr
    _ = 3 := by
      rw [(G₇.toGridLink_eq_iff_movesTo).mpr h₁₂, GridDiagram.toGridLink_unknot,
        unknottingNumber_unknot]
      norm_num

end GridLink

end TauCeti
