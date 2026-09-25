/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic

/-!
# Branch-2 recut rectangle X-avoidance

In Branch 2 of the `recutLeftEqLeft` construction, the new rectangle `E.second` spans the
columns `cIco (finRotate n a) D.rectangle.right`. The covered-columns iff
`a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` is `False ↔ True` here, so the
iff-based transfer lemma `disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns`
does not apply; a subinterval transfer is used instead.

Indeed, for the recut rectangle `E.second` with `E.second.left = finRotate n a` and
`E.second.right = D.rectangle.right`:
- `finRotate n a ∈ cIco (finRotate n a) (D.rectangle.right)` is true by `left_mem_cIco`
  (the rectangle is non-degenerate: `D.rectangle.right ≠ finRotate n a` by `HasOneCommonSide`),
- `a ∈ cIco (finRotate n a) (D.rectangle.right)` is false by
  `Grid.notMem_cIco_finRotate_left`.

This file proves the X-avoidance of the Branch 2 recut rectangle in the column-swapped
diagram, from the original rectangle's X-avoidance alone, via the general
column-subinterval transfer
`TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_of_subinterval` (in
`TauCeti.KnotTheory.Grid.Rectangle.Squares`): when a rectangle `R'` has rows contained in
an X-avoiding rectangle `R`'s rows and its columns form a subinterval not containing the
swapped column `a`, the X-avoidance transfers across the column swap by a case analysis on
whether the column is the swapped one.


## Main results

* `TauCeti.GridRectanglePentagonDecomposition.branch2_recut_rectangle_X_avoidance_swap`:
  the Branch 2 recut rectangle avoids the X-markings of the column-swapped diagram, from
  the original rectangle's X-avoidance and column data alone.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {x z : GridState n} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}

/-- X-avoidance for the Branch 2 recut rectangle in the column-swapped diagram.

The recut rectangle `R'` is given by its side data: in Branch 2 it spans the columns
`cIco (finRotate n a) r` with rows contained in an `X`-avoiding rectangle `R`'s rows,
where `R` spans the columns `cIco a r`. The branch hypothesis
`finRotate n a ∈ cIoo a r` supplies the column-subinterval inclusion;
`Grid.notMem_cIco_finRotate_left` shows `a` is not covered.

Only the original rectangle's X-avoidance is used, so the hypothesis is just that
avoidance rather than membership in the unblocked rectangles or any decomposition data. -/
theorem branch2_recut_rectangle_X_avoidance_swap
    {a r : Fin n}
    (R R' : GridRectangle n)
    (hX : Disjoint R.coveredSquares G.XSet)
    (hRcol : R.coveredColumns = Grid.cIco a r)
    (hR'col : R'.coveredColumns = Grid.cIco (finRotate n a) r)
    (hR'row : R'.coveredRows ⊆ R.coveredRows)
    (har : a ≠ r)
    (hbranch : finRotate n a ∈ Grid.cIoo a r) :
    Disjoint R'.coveredSquares (G.swapColumns a (finRotate n a)).XSet := by
  have ha_not_mem : a ∉ Grid.cIco (finRotate n a) r :=
    Grid.notMem_cIco_finRotate_left a r
  have hsub : Grid.cIco (finRotate n a) r ⊆ Grid.cIco a r :=
    Grid.cIco_subset_of_mem_cIoo hbranch
  exact G.disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    R R' hRcol hR'col hR'row hX har ha_not_mem hsub

end GridRectanglePentagonDecomposition

end TauCeti
