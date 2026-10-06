/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Basic
public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Thin annuli in the pentagon chain-map equation

The diagonal terms in the pentagon chain-map equation straighten to returning pairs of
rectangles. Both constituent domains are empty, so the returning pair is a thin annulus. In the
same-side-order (vertical) orientation, the pentagon's initial side is therefore the column
immediately before its terminal side, namely the first of the two commuted columns. In the
opposite-side-order (horizontal) orientation, the rectangle or straightened pentagon has
cyclically consecutive boundary rows.

These conclusions isolate the exceptional Case (P-3) configurations: later cancellation
arguments need only analyze the two columns adjacent to the replaced grid line in the vertical
case, and one thin row in the horizontal case.

## Main results

* `TauCeti.GridDiagram.pentagon_left_eq_column_of_mem_rectanglePentagonSameSideOrder` and
  `TauCeti.GridDiagram.pentagon_left_eq_column_of_mem_pentagonRectangleSameSideOrder`: every
  vertical-annulus term uses the first commuted column as the pentagon's initial side.
* `TauCeti.GridDiagram.rectangle_top_eq_finRotate_bottom_of_mem_rectanglePentagonOppositeSideOrder`
  and
  `TauCeti.GridDiagram.pentagon_top_eq_finRotate_bottom_of_mem_pentagonRectangleOppositeSideOrder`:
  every horizontal-annulus term is supported in one cyclic row.

## References

This is the thin-annulus reduction in Case (P-3) of Ozsvath--Stipsicz--Szabo,
*Grid Homology for Knots and Links*, Section 5.1, especially Figures 5.5 and 5.6.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- A same-side-order rectangle--pentagon term has its pentagon's initial side at the first
commuted column. Thus its straightening is a thin vertical annulus between the two commuted
columns. -/
theorem pentagon_left_eq_column_of_mem_rectanglePentagonSameSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonSameSideOrder C x) :
    D.pentagon.left = C.column := by
  have hmem := (G.mem_rectanglePentagonSameSideOrder C x D).1 hD
  have hcount := (G.mem_rectanglePentagonDecompositions C D).1 hmem.1
  have hempty : D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty :=
    ⟨((G.mem_unblockedRectangles D.rectangle).1 hcount.1).1,
      ((G.mem_pentagons D.pentagon).1 hcount.2).1⟩
  have hadj :=
    (D.rectangle.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.pentagon.toGridRectangleBetween hmem.2.1.symm).1 hempty
  apply (finRotate n).injective
  calc
    finRotate n D.pentagon.left = finRotate n D.rectangle.left :=
      congrArg (finRotate n) hmem.2.1.symm
    _ = D.rectangle.right := hadj.symm
    _ = D.pentagon.right := hmem.2.2
    _ = finRotate n C.column := D.pentagon.right_eq

/-- An opposite-side-order rectangle--pentagon term is supported in a thin horizontal annulus:
the top row of its rectangle immediately follows its bottom row. -/
theorem rectangle_top_eq_finRotate_bottom_of_mem_rectanglePentagonOppositeSideOrder
    (x : GridState n) (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonOppositeSideOrder C x) :
    D.rectangle.top = finRotate n D.rectangle.bottom := by
  have hmem := (G.mem_rectanglePentagonOppositeSideOrder C x D).1 hD
  have hcount := (G.mem_rectanglePentagonDecompositions C D).1 hmem.1
  have hempty : D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty :=
    ⟨((G.mem_unblockedRectangles D.rectangle).1 hcount.1).1,
      ((G.mem_pentagons D.pentagon).1 hcount.2).1⟩
  exact
    (D.rectangle.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
      D.pentagon.toGridRectangleBetween hmem.2.2.symm).1 hempty

/-- A same-side-order pentagon--rectangle term has its pentagon's initial side at the first
commuted column. Thus its straightening is a thin vertical annulus between the two commuted
columns. -/
theorem pentagon_left_eq_column_of_mem_pentagonRectangleSameSideOrder (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleSameSideOrder C x) :
    D.pentagon.left = C.column := by
  have hmem := (G.mem_pentagonRectangleSameSideOrder C x D).1 hD
  have hcount := (G.mem_pentagonRectangleDecompositions C D).1 hmem.1
  have hempty : D.pentagon.IsEmpty ∧ D.rectangle.IsEmpty :=
    ⟨((G.mem_pentagons D.pentagon).1 hcount.1).1,
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles D.rectangle).1
        hcount.2).1⟩
  have hadj :=
    (D.pentagon.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.rectangle hmem.2.1).1 hempty
  apply (finRotate n).injective
  calc
    finRotate n D.pentagon.left = D.pentagon.right := hadj.symm
    _ = finRotate n C.column := D.pentagon.right_eq

/-- An opposite-side-order pentagon--rectangle term is supported in a thin horizontal annulus:
the top row of its straightened pentagon immediately follows its bottom row. -/
theorem pentagon_top_eq_finRotate_bottom_of_mem_pentagonRectangleOppositeSideOrder
    (x : GridState n) (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleOppositeSideOrder C x) :
    D.pentagon.top = finRotate n D.pentagon.bottom := by
  have hmem := (G.mem_pentagonRectangleOppositeSideOrder C x D).1 hD
  have hcount := (G.mem_pentagonRectangleDecompositions C D).1 hmem.1
  have hempty : D.pentagon.IsEmpty ∧ D.rectangle.IsEmpty :=
    ⟨((G.mem_pentagons D.pentagon).1 hcount.1).1,
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles D.rectangle).1
        hcount.2).1⟩
  exact
    (D.pentagon.toGridRectangleBetween.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
      D.rectangle hmem.2.1).1 hempty

end GridDiagram

end TauCeti
