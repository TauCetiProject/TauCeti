/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Horizontal
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Vertical

/-!
# Monomial weights of initial-side commutation annuli

The diagonal terms involving initial-side pentagons are thin vertical or horizontal annuli.
Their constituent domains cover disjoint squares, so their composite monomial counts each
covered `O`-marking once. This file gives the resulting formulas in both composition orders.

Vertical weights are products of at most one variable from each commuted column. Horizontal
weights are the variable of the unique `O`-marking in the turn row. These formulas are in the
variables of the commuted diagram and are ready to compare with the terminal-side annular terms
in the commutation chain-map equation.

## References

Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.

This file adapts the terminal-side formalization in
`TauCeti.KnotTheory.Grid.Commutation.Annulus.Weight`.
-/

public section

namespace TauCeti
namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
variable (R : Type*) [CommSemiring R] {x : GridState n}

/-- A vertical rectangle--initial-side pentagon annulus has one factor for each covered
`O`-marking in the commuted columns. -/
theorem rectangleInitialPentagonWeight_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    G.rectangleInitialPentagonWeight C R D =
      (if G.O C.column ∈ Grid.cIoo C.turnRow D.pentagon.top
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.top C.turnRow
        then MvPolynomial.X C.column else 1) := by
  rw [G.rectangleInitialPentagonWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_of_same_side_order hleft hthin),
    D.coveredSquares_union_of_same_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_union_singleton_product _ _ _ _ _ C.column_ne_next]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- A vertical initial-side pentagon--rectangle annulus has one factor for each covered
`O`-marking in the commuted columns. -/
theorem initialPentagonRectangleWeight_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hleft : D.second.left = D.first.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    G.initialPentagonRectangleWeight C R D =
      (if G.O C.column ∉ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow)
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.bottom C.turnRow
        then MvPolynomial.X C.column else 1) := by
  rw [G.initialPentagonRectangleWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_map_of_same_side_order hleft hthin),
    D.coveredSquares_union_map_of_same_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_union_singleton_product _ _ _ _ _ C.column_ne_next]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- A horizontal rectangle--initial-side pentagon annulus contributes the turn row's variable
unless the `O`-marking is in the omitted second commuted column. -/
theorem rectangleInitialPentagonWeight_of_opposite_side_order
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hleft : D.first.left = D.pentagon.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    G.rectangleInitialPentagonWeight C R D =
      if G.O (finRotate n C.column) = C.turnRow then 1 else
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column)
          (G.O.transpose C.turnRow)) := by
  rw [G.rectangleInitialPentagonWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_of_opposite_side_order hleft hthin),
    D.coveredSquares_union_of_opposite_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_univ_erase_product_singleton]

/-- A horizontal initial-side pentagon--rectangle annulus contributes the turn row's variable
unless the `O`-marking is in the omitted first commuted column. -/
theorem initialPentagonRectangleWeight_of_opposite_side_order
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hleft : D.second.left = D.pentagon.right)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    G.initialPentagonRectangleWeight C R D =
      if G.O C.column = C.turnRow then 1 else
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column)
          (G.O.transpose C.turnRow)) := by
  rw [G.initialPentagonRectangleWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_map_of_opposite_side_order hleft hthin),
    D.coveredSquares_union_map_of_opposite_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_univ_erase_product_singleton]

/-- The weight formula for every counted vertical rectangle--initial-side pentagon term. -/
@[simp]
theorem rectangleInitialPentagonWeight_of_mem_rectangleInitialPentagonSameSideOrder
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectangleInitialPentagonSameSideOrder C x) :
    G.rectangleInitialPentagonWeight C R D =
      (if G.O C.column ∈ Grid.cIoo C.turnRow D.pentagon.top
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.top C.turnRow
        then MvPolynomial.X C.column else 1) := by
  exact G.rectangleInitialPentagonWeight_of_same_side_order C R D
    ((G.mem_rectangleInitialPentagonSameSideOrder C x D).1 hD).2.1
    (G.rectangle_right_eq_finRotate_left_of_mem_rectangleInitialPentagonSameSideOrder C x D hD)

/-- The weight formula for every counted vertical initial-side pentagon--rectangle term. -/
@[simp]
theorem initialPentagonRectangleWeight_of_mem_initialPentagonRectangleSameSideOrder
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.initialPentagonRectangleSameSideOrder C x) :
    G.initialPentagonRectangleWeight C R D =
      (if G.O C.column ∉ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow)
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.bottom C.turnRow
        then MvPolynomial.X C.column else 1) := by
  exact G.initialPentagonRectangleWeight_of_same_side_order C R D
    ((G.mem_initialPentagonRectangleSameSideOrder C x D).1 hD).2.1
    (G.pentagon_right_eq_finRotate_left_of_mem_initialPentagonRectangleSameSideOrder C x D hD)

/-- Every counted horizontal rectangle--initial-side pentagon term contributes the variable of
the unique `O`-marking in the turn row. -/
@[simp]
theorem rectangleInitialPentagonWeight_of_mem_rectangleInitialPentagonOppositeSideOrder
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectangleInitialPentagonOppositeSideOrder C x) :
    G.rectangleInitialPentagonWeight C R D =
      MvPolynomial.X (Equiv.swap C.column (finRotate n C.column)
        (G.O.transpose C.turnRow)) := by
  have hleft : D.first.left = D.pentagon.right := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact ((G.mem_rectangleInitialPentagonOppositeSideOrder C x D).1 hD).2.1
  rw [G.rectangleInitialPentagonWeight_of_opposite_side_order C R D hleft
    (G.rectangle_top_eq_finRotate_bottom_of_mem_rectangleInitialPentagonOppositeSideOrder
      C x D hD)]
  have hX := G.X_next_eq_turnRow_of_mem_rectangleInitialPentagonOppositeSideOrder C x D hD
  exact ite_eq_right (fun hO => G.disjoint (finRotate n C.column) (hO.trans hX.symm))

/-- Every counted horizontal initial-side pentagon--rectangle term contributes the variable of
the unique `O`-marking in the turn row. -/
@[simp]
theorem initialPentagonRectangleWeight_of_mem_initialPentagonRectangleOppositeSideOrder
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.initialPentagonRectangleOppositeSideOrder C x) :
    G.initialPentagonRectangleWeight C R D =
      MvPolynomial.X (Equiv.swap C.column (finRotate n C.column)
        (G.O.transpose C.turnRow)) := by
  have hleft : D.second.left = D.pentagon.right := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
    exact ((G.mem_initialPentagonRectangleOppositeSideOrder C x D).1 hD).2.1
  have hthin : D.pentagon.top = finRotate n D.pentagon.bottom := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
    exact G.pentagon_top_eq_finRotate_bottom_of_mem_initialPentagonRectangleOppositeSideOrder
      C x D hD
  rw [G.initialPentagonRectangleWeight_of_opposite_side_order C R D hleft hthin]
  have hX := G.X_column_eq_turnRow_of_mem_initialPentagonRectangleOppositeSideOrder C x D hD
  exact ite_eq_right (fun hO => G.disjoint C.column (hO.trans hX.symm))

end GridDiagram
end TauCeti
