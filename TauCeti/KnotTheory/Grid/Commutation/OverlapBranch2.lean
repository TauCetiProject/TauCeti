/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Direct X-avoidance for the branch-2 recut rectangle

In Branch 2 of the `recutLeftEqLeft` construction, the new rectangle `E.second` spans the
columns `cIco (finRotate n a) D.rectangle.right`. The covered-columns iff
`a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` is `False ↔ True` here, so the
transfer lemma `disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns` cannot apply:
this is a genuine mathematical obstruction, not a missing argument.

Indeed, for the recut rectangle `E.second` with `E.second.left = finRotate n a` and
`E.second.right = D.rectangle.right`:
- `finRotate n a ∈ cIco (finRotate n a) (D.rectangle.right)` is true by `left_mem_cIco`
  (the rectangle is non-degenerate: `D.rectangle.right ≠ finRotate n a` by `HasOneCommonSide`),
- `a ∈ cIco (finRotate n a) (D.rectangle.right)` is false by
  `Grid.notMem_cIco_finRotate_left`.

This file proves the X-avoidance directly via the general column-subinterval transfer
`TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_of_subinterval` (in
`TauCeti.KnotTheory.Grid.Rectangle.Squares`): when a rectangle `R'` has rows contained in
an X-avoiding rectangle `R`'s rows and its columns form a subinterval not containing the
swapped column `a`, the X-avoidance transfers across the column swap by a case analysis on
whether the column is the swapped one.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.branch2_direct_X_avoidance`: the Branch 2
  recut rectangle avoids the X-markings of the column-swapped diagram, from its side data.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {x z : GridState n} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}

/-- Direct X-avoidance for the Branch 2 recut rectangle in the column-swapped diagram.

The recut rectangle `R'` is given by its side data: in Branch 2 it spans the columns
`cIco (finRotate n C.column) D.rectangle.right` with rows contained in `D.rectangle`'s
(`cIco (x C.column) (x D.rectangle.right)`). The branch hypothesis
`finRotate n C.column ∈ cIoo C.column D.rectangle.right` supplies the column-subinterval
inclusion; `Grid.notMem_cIco_finRotate_left` shows `C.column` is not covered.

This is the missing piece for `recutLeftEqLeft` counted-ness in Branch 2, where the
covered-columns iff is false and the transfer lemma does not apply. Only the original
rectangle's X-avoidance is used, so the hypothesis is just its membership in the
unblocked rectangles rather than the full counted decomposition. -/
theorem branch2_direct_X_avoidance
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hrect : D.rectangle ∈ G.unblockedRectangles x D.middle)
    (R' : GridRectangle n)
    (hR'col : R'.coveredColumns = Grid.cIco (finRotate n C.column) D.rectangle.right)
    (hR'row : R'.coveredRows = Grid.cIco (x C.column) (x D.rectangle.right))
    (hbranch : finRotate n C.column ∈ Grid.cIoo C.column D.rectangle.right)
    (hrect_left : D.rectangle.left = C.column) :
    Disjoint R'.coveredSquares (G.swapColumns C.column (finRotate n C.column)).XSet := by
  have hX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet :=
    ((G.mem_unblockedRectangles D.rectangle).mp hrect).2
  have har : C.column ≠ D.rectangle.right := by
    intro h
    exact D.rectangle.left_ne_right (hrect_left.trans h)
  have ha_not_mem : C.column ∉ Grid.cIco (finRotate n C.column) D.rectangle.right :=
    Grid.notMem_cIco_finRotate_left C.column D.rectangle.right
  have hsub : Grid.cIco (finRotate n C.column) D.rectangle.right ⊆
      Grid.cIco C.column D.rectangle.right :=
    Grid.cIco_subset_of_mem_cIoo hbranch
  have hRcol : D.rectangle.toGridRectangle.coveredColumns =
      Grid.cIco C.column D.rectangle.right := by
    rw [GridRectangle.coveredColumns_def, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hrect_left]
  have hRrow : D.rectangle.toGridRectangle.coveredRows =
      Grid.cIco (x C.column) (x D.rectangle.right) := by
    rw [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def, hrect_left]
  have hR'row_sub : R'.coveredRows ⊆ D.rectangle.toGridRectangle.coveredRows := by
    rw [hR'row, hRrow]
  exact G.disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    D.rectangle.toGridRectangle R' hRcol hR'col hR'row_sub hX har ha_not_mem hsub

end GridRectanglePentagonDecomposition

end TauCeti
