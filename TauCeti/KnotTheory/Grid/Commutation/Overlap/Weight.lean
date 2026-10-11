/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Right

/-!
# Weights of the overlap recuts for grid commutation

Let `C` be a validated column commutation of a grid diagram `G`, commuting the columns `a` and
`b = finRotate n a`, and let `G' = G.swapColumns a b`. The chain-map equation for the pentagon
map compares, coefficient by coefficient, a sum over a rectangle of `G` followed by a pentagon,
weighted by `GridDiagram.rectanglePentagonWeight`, with a sum over a pentagon followed by a
rectangle of `G'`, weighted by `GridDiagram.pentagonRectangleWeight`. When the two domains share
exactly one side, their union is recut the other way (`Overlap/Basic.lean`, `Overlap/Right.lean`),
and `Overlap/Counted.lean` shows that the recuts landing in the other sum are counted there. This
file shows that each of these recuts of a rectangle followed by a pentagon has the weight of the
domain it came from: a recut into the other sum contributes the same monomial there, and the recut
that stays in the same sum has the weight of the term it came from. That is the equal-weight step a
future pairing of such terms within the same sum needs; the pairing itself is not established
here.

Both weights depend only on the composite domain, its squares counted with multiplicity, with a
rectangle of `G'` read in `G` with its two commuted columns exchanged
(`GridDiagram.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq` and
`GridDiagram.rectanglePentagonWeight_eq_of_val_add_val_eq` in `Commutation/Decomposition.lean`).

The recuts preserve the squares covered by the *underlying* rectangles, but a pentagon covers
only part of its underlying rectangle in the two columns next to the replaced grid line: the rows
above the turn row in column `a`, and in column `b` the rows from its bottom row up to the turn
row. Matching the composite domains therefore comes down to a balance in these two columns. In
the second common-initial-side branch it needs the cyclic order of the three corner rows that
emptiness forces (`GridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left`).

## Main results

* `TauCeti.GridDiagram.pentagonRectangleWeight_recutLeftEqLeft`: the recut along a common initial
  side preserves the weight.
* `TauCeti.GridDiagram.pentagonRectangleWeight_recutRightEqRightFirst`: so does the recut along a
  common terminal side when the first new rectangle inherits the replaced grid line.
* `TauCeti.GridDiagram.rectanglePentagonWeight_recutRightEqRightSecond`: so does the recut along a
  common terminal side when the second new rectangle inherits it, a recut that stays in the
  same sum.

## References

The pairing of composite domains in the chain-map equation of a column commutation follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

variable (C : ColumnCommutationData G) (R : Type*) [CommSemiring R] {x z : GridState n}

/-- Recutting a rectangle followed by a pentagon along their common initial side preserves the
weight: the promoted pentagon followed by the remaining rectangle of the commuted diagram has
the weight of the original rectangle followed by the original pentagon. -/
@[simp]
theorem pentagonRectangleWeight_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    G.pentagonRectangleWeight C R (D.recutLeftEqLeft hcommon hone hrectangle hpentagon) =
      G.rectanglePentagonWeight C R D := by
  set E := D.recutLeftEqLeft hcommon hone hrectangle hpentagon with hE
  have hfirst : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hsecond : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle,
      D.toRectangleDecomposition_second_toGridRectangle] using hpentagon
  have hleft : D.toRectangleDecomposition.first.left = D.toRectangleDecomposition.second.left := by
    simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] using hcommon
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft E.toRectangleDecomposition := by
    rw [hE, D.recutLeftEqLeft_toRectangleDecomposition]
    exact D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut hleft hone hfirst hsecond
  apply G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E
    (D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon).isRepartition fun t => ?_
  have hEright := hdata.recut_sides.2
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] at hEright
  have hPbottom : D.pentagon.bottom = x D.rectangle.right := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_left]
  simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEright]
  rcases hdata.recut_branch with ⟨hcol, -, hPleft, hrleft⟩ | ⟨hcol, hmiddle, hPleft, hrleft⟩
  -- The remaining rectangle has the original rectangle's columns, before the two commuted
  -- columns, and the promoted pentagon starts where the original pentagon does.
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      D.pentagon.right_eq] at hcol hPleft hrleft
    have ha : C.column ∉ Grid.cIco D.rectangle.left D.rectangle.right := fun ha =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol) ha
        (Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol))
    have hb : finRotate n C.column ∉ Grid.cIco D.rectangle.left D.rectangle.right := fun hb =>
      Grid.right_notMem_cIco _ _ (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hb hcol)
    rw [hrleft, GridRectangleBetween.bottom_def, hPleft, hPbottom]
    simp only [ha, hb, false_and, ↓reduceIte]
  -- The remaining rectangle starts at the commuted grid line and keeps the original rectangle's
  -- rows, while the promoted pentagon reaches back to the original rectangle's initial row.
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      D.pentagon.right_eq] at hcol hmiddle hPleft hrleft
    have ha : C.column ∉ Grid.cIco (finRotate n C.column) D.rectangle.right := fun ha =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
        (Grid.self_mem_cIco_finRotate (Grid.ne_left_of_mem_cIoo hcol).symm) ha
    have hb : finRotate n C.column ∈ Grid.cIco (finRotate n C.column) D.rectangle.right :=
      Grid.left_mem_cIco (Grid.ne_right_of_mem_cIoo hcol)
    have hord := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hleft
      (by simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
        D.pentagon.right_eq] using (Grid.ne_right_of_mem_cIoo hcol).symm) hfirst hsecond).2
    have hsecondTop := congrArg GridRectangle.top D.toRectangleDecomposition_second_toGridRectangle
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectangleBetween.toGridRectangle_top] at hord hsecondTop
    rw [hsecondTop] at hord
    have hturn := D.pentagon.turn_mem_cIco_bottom_top
    rw [hPbottom] at hturn
    rw [hrleft, GridRectangleBetween.bottom_def, hPleft, hPbottom, hmiddle,
      GridState.swapColumns_apply, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne D.rectangle.left_ne_right.symm
        (Grid.ne_right_of_mem_cIoo hcol).symm]
    simp only [ha, hb, false_and, true_and, ↓reduceIte, zero_add]
    exact Grid.ite_mem_cIco_eq_add_of_mem_cIoo hord hturn t

/-- Recutting a rectangle followed by a pentagon along their common terminal side preserves the
weight when the first new rectangle inherits the replaced grid line: the promoted pentagon
followed by the remaining rectangle of the commuted diagram has the weight of the original
rectangle followed by the original pentagon. -/
@[simp]
theorem pentagonRectangleWeight_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right = D.pentagon.right) :
    G.pentagonRectangleWeight C R
        (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst) =
      G.rectanglePentagonWeight C R D := by
  set E := D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst with hE
  apply G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E
    (D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).isRepartition
    fun t => ?_
  obtain ⟨-, -, -, -, hcols, ha, -⟩ :=
    D.recutRightEqRightFirst_rectangle_geometry hcommon hone hrectangle hpentagon hfirst
  rw [← hE] at hcols ha
  obtain ⟨hcol, -, hleft⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hfirst
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] at hcol hleft
  -- The remaining rectangle lies inside the original rectangle, which stops before the
  -- replaced grid line, and misses the column before that line.
  have hb : finRotate n C.column ∉ E.rectangle.toGridRectangle.coveredColumns :=
    fun hb => Grid.right_notMem_cIco D.rectangle.left (finRotate n C.column) (by
      simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, hcommon, D.pentagon.right_eq] using hcols hb)
  -- The promoted pentagon starts where the original pentagon does.
  have hbottom : E.pentagon.bottom = D.pentagon.bottom := by
    rw [hE, D.recutRightEqRightFirst_pentagon_bottom, GridRectangleBetween.bottom_def, hleft,
      GridRectangleBetween.bottom_def, D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol)
        (Grid.ne_right_of_mem_cIoo hcol)]
  simp only [GridRectangle.mem_coveredSquares, ha, hb, hbottom, false_and, ↓reduceIte]

/-- Recutting a rectangle followed by a pentagon along their common terminal side preserves the
weight when the second new rectangle inherits the replaced grid line: the new rectangle followed
by the promoted pentagon has the weight of the original rectangle followed by the original
pentagon. -/
@[simp]
theorem rectanglePentagonWeight_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    G.rectanglePentagonWeight C R
        (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond) =
      G.rectanglePentagonWeight C R D := by
  apply G.rectanglePentagonWeight_eq_of_val_add_val_eq C R
  refine D.coveredSquares_val_add_val_eq_of_isRepartition_of_bottom_eq _
    (D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).isRepartition ?_
  obtain ⟨hcol, -, hleft, hmiddle⟩ :=
    D.second_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hsecond
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] at hcol hleft hmiddle
  -- The promoted pentagon starts on the original rectangle's initial side, where the recut
  -- state has the row of the original pentagon's initial side.
  rw [D.recutRightEqRightSecond_pentagon_bottom, GridRectangleBetween.bottom_def, hleft, hmiddle,
    GridState.swapColumns_apply, Equiv.swap_apply_right, GridRectangleBetween.bottom_def,
    D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol).symm
      (fun h => D.pentagon.left_ne_right (h.trans hcommon))]

end GridDiagram

end TauCeti
