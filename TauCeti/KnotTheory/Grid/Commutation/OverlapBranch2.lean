/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapColumns
public import TauCeti.KnotTheory.Grid.Commutation.Decomposition

/-!
# Direct X-avoidance for the branch-2 recut rectangle

In Branch 2 of the `recutLeftEqLeft` construction, the new rectangle `E.second` spans the
columns `cIco (finRotate n a) D.rectangle.right`. The covered-columns iff
`a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` is `False ↔ True` here (see
`OverlapColumns.lean`), so the transfer lemma
`disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns` cannot apply.

This file proves the X-avoidance directly via a general column-subinterval lemma: when a
rectangle `R'` has the same rows as an X-avoiding rectangle `R` and its columns form a
subinterval not containing the swapped column `a`, the X-avoidance transfers across the
column swap by a case analysis on whether the column is the swapped one.

## Main results

* `TauCeti.disjoint_coveredSquares_XSet_swapColumns_of_subinterval`: general transfer for
  column-subinterval rectangles.
* `TauCeti.Grid.cIco_subset_of_mem_cIoo`: the column-subinterval inclusion.
* `TauCeti.GridRectanglePentagonDecomposition.branch2_direct_X_avoidance`: the Branch 2
  recut rectangle avoids the X-markings of the column-swapped diagram, from its side data.
-/

public section

namespace TauCeti

/-- A half-open cyclic interval starting strictly inside another is contained in it. -/
theorem Grid.cIco_subset_of_mem_cIoo {n : ℕ} {a b r : Fin n}
    (h : b ∈ Grid.cIoo a r) : Grid.cIco b r ⊆ Grid.cIco a r := by
  have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo h
  intro x hx
  rw [← hunion]
  exact Finset.mem_union.mpr (Or.inr hx)

/-- X-avoidance transfers across a column swap for a rectangle whose columns form a subinterval
of an X-avoiding rectangle's columns (with the same rows), provided the swapped-out column is
not covered.

For `(c, r')` in `R'`'s squares with `(c, r')` in the swapped X-set:
- if `c = b`, the swap sends it to `(a, r')`, which lies in `R`'s squares (using `a ∈ cIco a r`)
  and contradicts `R`'s X-avoidance;
- otherwise the swap fixes `c` (as `c ≠ a` by `ha_not_mem` and `c ≠ b`), and `(c, r')` lies in
  `R`'s squares via the column subset, again contradicting `R`'s X-avoidance. -/
theorem disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    {n : ℕ} {G : GridDiagram n} {a b r ba ta : Fin n}
    (R R' : GridRectangle n)
    (hRcol : R.coveredColumns = Grid.cIco a r)
    (hRrow : R.coveredRows = Grid.cIco ba ta)
    (hR'col : R'.coveredColumns = Grid.cIco b r)
    (hR'row : R'.coveredRows = Grid.cIco ba ta)
    (hX : Disjoint R.coveredSquares G.XSet)
    (har : a ≠ r)
    (ha_not_mem : a ∉ Grid.cIco b r)
    (hsub : Grid.cIco b r ⊆ Grid.cIco a r) :
    Disjoint R'.coveredSquares (G.swapColumns a b).XSet := by
  rw [Finset.disjoint_left]
  rintro ⟨c, r'⟩ hc hx
  rw [GridRectangle.mem_coveredSquares, hR'col, hR'row] at hc
  obtain ⟨hc_col, hc_row⟩ := hc
  rw [G.mem_XSet_swapColumns] at hx
  by_cases hcb : c = b
  · subst hcb
    rw [Equiv.swap_apply_right] at hx
    have hmem : (a, r') ∈ R.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares, hRcol, hRrow]
      exact ⟨Grid.left_mem_cIco har, hc_row⟩
    exact (Finset.disjoint_left.mp hX) hmem hx
  · have hca : c ≠ a := fun h => ha_not_mem (h ▸ hc_col)
    have hswap : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb
    rw [hswap] at hx
    have hmem : (c, r') ∈ R.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares, hRcol, hRrow]
      exact ⟨hsub hc_col, hc_row⟩
    exact (Finset.disjoint_left.mp hX) hmem hx

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {x z : GridState n} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}

/-- Direct X-avoidance for the Branch 2 recut rectangle in the column-swapped diagram.

The recut rectangle `R'` is given by its side data: in Branch 2 it spans the columns
`cIco (finRotate n C.column) D.rectangle.right` with the same rows
`cIco (x C.column) (x D.rectangle.right)` as `D.rectangle`. The branch hypothesis
`finRotate n C.column ∈ cIoo C.column D.rectangle.right` supplies the column-subinterval
inclusion; `notMem_cIco_finRotate_left` shows `C.column` is not covered.

This is the missing piece for `recutLeftEqLeft` counted-ness in Branch 2, where the
covered-columns iff is false and the transfer lemma does not apply. -/
theorem branch2_direct_X_avoidance
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (R' : GridRectangle n)
    (hR'col : R'.coveredColumns = Grid.cIco (finRotate n C.column) D.rectangle.right)
    (hR'row : R'.coveredRows = Grid.cIco (x C.column) (x D.rectangle.right))
    (hbranch : finRotate n C.column ∈ Grid.cIoo C.column D.rectangle.right)
    (hrect_left : D.rectangle.left = C.column) :
    Disjoint R'.coveredSquares (G.swapColumns C.column (finRotate n C.column)).XSet := by
  have hX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet :=
    ((G.mem_unblockedRectangles D.rectangle).mp
      ((G.mem_rectanglePentagonDecompositions C D).mp hD).1).2
  have har : C.column ≠ D.rectangle.right := by
    intro h
    exact D.rectangle.left_ne_right (hrect_left.trans h)
  have ha_not_mem : C.column ∉ Grid.cIco (finRotate n C.column) D.rectangle.right :=
    GridRectanglePentagonDecomposition.notMem_cIco_finRotate_left C.column D.rectangle.right
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
  exact disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    D.rectangle.toGridRectangle R' hRcol hRrow hR'col hR'row hX har ha_not_mem hsub

end GridRectanglePentagonDecomposition

end TauCeti
