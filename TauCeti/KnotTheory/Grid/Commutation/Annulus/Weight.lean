/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Horizontal
public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Vertical

/-!
# Monomial weights of commutation annuli

The diagonal rectangle--pentagon terms in a column commutation are thin annuli. Their
constituent domains cover disjoint squares, so each O-marking contributes at most once.
For a vertical annulus the weight is determined by the markings in the two commuted columns
and their positions on the arc from the pentagon's bottom to the turn row in rectangle--pentagon
order, or from the turn row to the pentagon's top in pentagon--rectangle order. A horizontal
annulus covers one row with one square omitted; when it avoids X-markings, the omitted square
is X-marked, and the unique O-marking in the row contributes exactly one variable.

The variables are those of the target diagram. In the pentagon--rectangle order the rectangle
is read back in the original columns before its markings are counted. These formulas supply
the annular weights in the diagonal coefficient of the commutation chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.
-/

public section

namespace TauCeti
namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
variable (R : Type*) [CommSemiring R] {x : GridState n}

/-- A vertical rectangle--pentagon annulus has one factor for each commuted column whose
O-marking is covered. The first column's variable is renamed to the second, and conversely. -/
theorem rectanglePentagonWeight_of_same_side_order
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = C.column) :
    G.rectanglePentagonWeight C R D =
      (if G.O C.column ∉ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow)
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.bottom C.turnRow
        then MvPolynomial.X C.column else 1) := by
  classical
  rw [G.rectanglePentagonWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_of_same_side_order hleft),
    D.coveredSquares_union_of_same_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_union_singleton_product _ _ _ _ _ C.column_ne_next]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- A vertical pentagon--rectangle annulus is weighted by the two covered O-markings after
reading the rectangle back in the original columns. Its cut is at the pentagon's top.
The first column's variable is renamed to the second, and conversely. -/
theorem pentagonRectangleWeight_of_same_side_order
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = C.column) :
    G.pentagonRectangleWeight C R D =
      (if G.O C.column ∈ Grid.cIoo C.turnRow D.pentagon.top
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.top C.turnRow
        then MvPolynomial.X C.column else 1) := by
  classical
  rw [G.pentagonRectangleWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_map_of_same_side_order hleft),
    D.coveredSquares_union_map_of_same_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_union_singleton_product _ _ _ _ _ C.column_ne_next]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- A horizontal rectangle--pentagon annulus contributes the variable of the unique O-marking
in the turn row, with its column renamed by the commutation swap, unless that marking lies in
the omitted square in the first commuted column. -/
theorem rectanglePentagonWeight_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    G.rectanglePentagonWeight C R D =
      if G.O C.column = C.turnRow then 1 else
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow)) := by
  classical
  rw [G.rectanglePentagonWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_of_opposite_side_order hleft hthin),
    D.coveredSquares_union_of_opposite_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_univ_erase_product_singleton]

/-- A horizontal pentagon--rectangle annulus contributes the variable of the unique O-marking
in the turn row of the original diagram, with its column renamed by the commutation swap,
unless that marking lies in the omitted square in the second commuted column. -/
theorem pentagonRectangleWeight_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    G.pentagonRectangleWeight C R D =
      if G.O (finRotate n C.column) = C.turnRow then 1 else
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow)) := by
  classical
  rw [G.pentagonRectangleWeight_eq_prod_OColumnsOfSquares_union C R D
    (D.disjoint_coveredSquares_map_of_opposite_side_order hleft hthin),
    D.coveredSquares_union_map_of_opposite_side_order hleft hthin]
  rw [G.prod_OColumnsOfSquares_univ_erase_product_singleton]

/-- Every counted vertical rectangle--pentagon term has one factor for each covered O-marking
in the commuted columns, with each column's variable renamed to the other column. -/
@[simp]
theorem rectanglePentagonWeight_of_mem_rectanglePentagonSameSideOrder
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonSameSideOrder C x) :
    G.rectanglePentagonWeight C R D =
      (if G.O C.column ∉ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow)
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.bottom C.turnRow
        then MvPolynomial.X C.column else 1) := by
  exact G.rectanglePentagonWeight_of_same_side_order C R D
    ((G.mem_rectanglePentagonSameSideOrder C x D).1 hD).2.1
    (G.pentagon_left_eq_column_of_mem_rectanglePentagonSameSideOrder C x D hD)

/-- Every counted vertical pentagon--rectangle term has one factor for each covered O-marking
in the original commuted columns, with each column's variable renamed to the other column. -/
@[simp]
theorem pentagonRectangleWeight_of_mem_pentagonRectangleSameSideOrder
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleSameSideOrder C x) :
    G.pentagonRectangleWeight C R D =
      (if G.O C.column ∈ Grid.cIoo C.turnRow D.pentagon.top
        then MvPolynomial.X (finRotate n C.column) else 1) *
      (if G.O (finRotate n C.column) ∈ Grid.cIco D.pentagon.top C.turnRow
        then MvPolynomial.X C.column else 1) := by
  exact G.pentagonRectangleWeight_of_same_side_order C R D
    ((G.mem_pentagonRectangleSameSideOrder C x D).1 hD).2.1
    (G.pentagon_left_eq_column_of_mem_pentagonRectangleSameSideOrder C x D hD)

/-- Every counted horizontal rectangle--pentagon term contributes the variable of the unique
O-marking in the turn row, in target-column coordinates. -/
@[simp]
theorem rectanglePentagonWeight_of_mem_rectanglePentagonOppositeSideOrder
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonOppositeSideOrder C x) :
    G.rectanglePentagonWeight C R D =
      MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow)) := by
  have hleft := ((G.mem_rectanglePentagonOppositeSideOrder C x D).1 hD).2.1
  rw [G.rectanglePentagonWeight_of_opposite_side_order C R D hleft
    (G.rectangle_top_eq_finRotate_bottom_of_mem_rectanglePentagonOppositeSideOrder C x D hD)]
  have hX := G.X_column_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder C x D hD
  exact ite_eq_right (fun hO => G.disjoint C.column (hO.trans hX.symm))

/-- Every counted horizontal pentagon--rectangle term contributes the variable of the unique
O-marking in the turn row of the original diagram, with its column renamed by the commutation
swap. -/
@[simp]
theorem pentagonRectangleWeight_of_mem_pentagonRectangleOppositeSideOrder
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleOppositeSideOrder C x) :
    G.pentagonRectangleWeight C R D =
      MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow)) := by
  have hleft := ((G.mem_pentagonRectangleOppositeSideOrder C x D).1 hD).2.1
  rw [G.pentagonRectangleWeight_of_opposite_side_order C R D hleft
    (G.pentagon_top_eq_finRotate_bottom_of_mem_pentagonRectangleOppositeSideOrder C x D hD)]
  have hX := G.X_next_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder C x D hD
  exact ite_eq_right (fun hO => G.disjoint (finRotate n C.column) (hO.trans hX.symm))

end GridDiagram
end TauCeti
