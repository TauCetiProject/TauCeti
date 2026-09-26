/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic
public import TauCeti.KnotTheory.Grid.Commutation.Pentagon

/-!
# X-avoidance pieces for the overlap recut

When `recutLeftEqLeft` promotes the first recut rectangle to a pentagon via `ofRightEq`, the
new pentagon's `coveredSquares` include an extra strip `{finRotate n a} ×ˢ cIco bottom s`
beyond its underlying rectangle, where `bottom` is the recut's first rectangle's bottom row.

## Branch 1

In Branch 1 of the recut (`E.first.left = D.toRectangleDecomposition.first.right`), the
recut's first rectangle's bottom row coincides with the original pentagon's bottom row
(`recut_first_bottom_eq_pentagon_bottom_of_branch1`); both are `x` applied to the original
rectangle's terminal side. The strip's row interval then coincides with the original
pentagon's, so the original X-avoidance applies (`recut_X_not_mem_of_branch1`).

The branch-1 recut *rectangle* `E.second` retains the original rectangle's column sides, but
its row span differs from the original's, so its covered squares are not contained in the
original rectangle's and the naive subset transfer does not apply; its X-avoidance in the
column-swapped diagram needs a separate argument.

## Branch 2

In Branch 2 (`E.first.left = D.toRectangleDecomposition.first.left`), the new pentagon's
bottom row is `x D.rectangle.left`. Its extra strip avoids X by combining the original
rectangle's X-avoidance with the original pentagon's X-avoidance over the two halves of a
cyclic-ordered row interval, via the interval-union lemma
`Grid.notMem_cIco_of_cIco_union`:
`GridPentagonBetween.X_not_mem_strip_of_disjoint` supplies the pentagon half and
`TauCeti.GridDiagram.X_not_mem_coveredRows_of_disjoint` the rectangle half.

The branch-2 recut *rectangle* `E.second` spans the columns `cIco (finRotate n a)
D.rectangle.right`. The covered-columns iff
`a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` is `False ↔ True` here, so the
iff-based transfer lemma
`TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns` does
not apply; the interval-shaped subinterval transfer
`TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_of_cIco` is used
instead, with `a ∈ cIco a r` from `Grid.left_mem_cIco`, `a ∉ cIco (finRotate n a) r` from
`Grid.notMem_cIco_finRotate_left`, and the column inclusion from
`Grid.cIco_subset_of_mem_cIoo`.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recut_first_bottom_eq_pentagon_bottom_of_branch1`:
  in the first recut branch, the recut's first rectangle's bottom row equals the original
  pentagon's bottom row.
* `TauCeti.GridRectanglePentagonDecomposition.recut_X_not_mem_of_branch1`: X-avoidance for
  the `finRotate` strip in the first recut branch, from the original pentagon's X-avoidance.

-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n}
variable {x z : GridState n}

/-- In the first recut branch, the recut's first rectangle's bottom row equals the original
pentagon's bottom row. -/
public theorem recut_first_bottom_eq_pentagon_bottom_of_branch1
    {a s : Fin n}
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirstLeft : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.left = D.toRectangleDecomposition.first.right) :
    (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.bottom = D.pentagon.bottom := by
  have hempty1 : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hempty2 : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle,
      D.toRectangleDecomposition_second_toGridRectangle] using hpentagon
  have hnew : (D.toRectangleDecomposition.recut hone hempty1 hempty2).first.bottom =
      x D.toRectangleDecomposition.first.right := by
    have h1 : (D.toRectangleDecomposition.recut hone hempty1 hempty2).first.bottom =
        x ((D.toRectangleDecomposition.recut hone hempty1 hempty2).first.left) :=
      GridRectangleBetween.bottom_def _
    rw [h1]
    have h2 : ((D.toRectangleDecomposition.recut hone hempty1 hempty2).first).left =
        D.toRectangleDecomposition.first.right := hfirstLeft
    rw [h2]
  have hold : D.pentagon.bottom = x D.toRectangleDecomposition.first.right := by
    have h1 : D.pentagon.bottom = D.middle D.pentagon.left := rfl
    rw [h1, ← hcommon, D.rectangle.map_left, D.toRectangleDecomposition_first_right]
  rw [hnew, hold]

/-- X-avoidance for the `finRotate` strip in the first recut branch. -/
public theorem recut_X_not_mem_of_branch1
    {a s : Fin n}
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hdisjoint : Disjoint D.pentagon.coveredSquares G.XSet)
    (hfirstLeft : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.left = D.toRectangleDecomposition.first.right) :
    G.X (finRotate n a) ∉
      Grid.cIco (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
            hpentagon)).first.bottom s := by
  -- The bottoms coincide, so the shared pentagon strip argument applies.
  have hbot := D.recut_first_bottom_eq_pentagon_bottom_of_branch1 hcommon hone
    hrectangle hpentagon hfirstLeft
  exact D.pentagon.X_not_mem_strip_of_disjoint G hdisjoint _ hbot.symm

/-
Application note (branch 1):

To show the `recutLeftEqLeft`-promoted pentagon is counted, apply
`GridPentagonBetween.disjoint_coveredSquares_XSet_of_column_subset` with `Q := D.pentagon`
and `hX` from the pentagon's counted membership (`((G.mem_pentagons D.pentagon).mp hpent).2`):
- `hcol`: from `Grid.cIco_subset_of_mem_cIoo hbranch` after rewriting the recut
  first rectangle's `left` via the branch-1 side equation and `hcommon`;
- `hbot`: `D.recut_first_bottom_eq_pentagon_bottom_of_branch1`;
- `htop`: both sides are the source state at `finRotate n C.column`, via
  `GridRectangleBetween.top_def`, `D.pentagon.right_eq`, and the fact that the
  column transposition defining `D.middle` fixes `finRotate n C.column`
  (`Equiv.swap_apply_of_ne_of_ne` with `D.pentagon.left_ne_right` and
  `Grid.ne_right_of_mem_cIoo hbranch`).

The promoted pentagon's `left`/`bottom`/`top` agree with the recut first
rectangle's by definition (`recutLeftEqLeft.eq_1` and `ofRightEq_toGridRectangleBetween`);
emptiness is `D.isEmpty_pentagon_recutLeftEqLeft`.  The final membership then follows
from `G.mem_pentagons`.
-/

end GridRectanglePentagonDecomposition

end TauCeti
