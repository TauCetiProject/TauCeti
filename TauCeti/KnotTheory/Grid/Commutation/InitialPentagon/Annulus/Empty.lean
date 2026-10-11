/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Basic
public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Thin initial-side commutation annuli

The two domains in a counted diagonal rectangle--initial-side pentagon term are empty. In the
same-side-order orientation they therefore form a thin vertical annulus: the terminal side of
the first underlying rectangle is the cyclic successor of its initial side. In the
opposite-side-order orientation they form a thin horizontal annulus: the top row is the cyclic
successor of the bottom row.

These conclusions hold in both composition orders. Together with the exhaustive partitions in
`TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Basic`, they reduce every diagonal
initial-side term in the commutation chain-map equation to one of the two thin-annulus geometries.

## Main results

* `rectangle_right_eq_finRotate_left_of_mem_rectangleInitialPentagonSameSideOrder` and
  `pentagon_right_eq_finRotate_left_of_mem_initialPentagonRectangleSameSideOrder` identify the
  thin vertical terms.
* `rectangle_top_eq_finRotate_bottom_of_mem_rectangleInitialPentagonOppositeSideOrder` and
  `pentagon_top_eq_finRotate_bottom_of_mem_initialPentagonRectangleOppositeSideOrder` identify
  the thin horizontal terms.

## References

This is the thin-annulus reduction for the initial-side part of Case (P-3) in
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- In a counted same-side-order rectangle--initial-side pentagon term, the rectangle spans one
cyclic column. -/
theorem rectangle_right_eq_finRotate_left_of_mem_rectangleInitialPentagonSameSideOrder
    (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectangleInitialPentagonSameSideOrder C x) :
    D.first.right = finRotate n D.first.left := by
  have hmem := (G.mem_rectangleInitialPentagonSameSideOrder C x D).1 hD
  have hcount := (G.mem_rectangleInitialPentagonDecompositions C D).1 hmem.1
  have hp := ((G.mem_initialPentagons D.pentagon).1 hcount.2).1
  have hempty : D.first.IsEmpty ∧ D.second.IsEmpty :=
    ⟨((G.mem_unblockedRectangles D.first).1 hcount.1).1, by
      simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
        using hp⟩
  exact (D.first.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
    D.second hmem.2.1.symm).1 hempty

/-- In a counted opposite-side-order rectangle--initial-side pentagon term, the rectangle spans
one cyclic row. -/
theorem rectangle_top_eq_finRotate_bottom_of_mem_rectangleInitialPentagonOppositeSideOrder
    (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectangleInitialPentagonOppositeSideOrder C x) :
    D.first.top = finRotate n D.first.bottom := by
  have hmem := (G.mem_rectangleInitialPentagonOppositeSideOrder C x D).1 hD
  have hcount := (G.mem_rectangleInitialPentagonDecompositions C D).1 hmem.1
  have hp := ((G.mem_initialPentagons D.pentagon).1 hcount.2).1
  have hempty : D.first.IsEmpty ∧ D.second.IsEmpty :=
    ⟨((G.mem_unblockedRectangles D.first).1 hcount.1).1, by
      simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
        using hp⟩
  exact (D.first.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
    D.second hmem.2.2.symm).1 hempty

/-- In a counted same-side-order initial-side pentagon--rectangle term, the pentagon's
underlying rectangle spans one cyclic column. -/
theorem pentagon_right_eq_finRotate_left_of_mem_initialPentagonRectangleSameSideOrder
    (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.initialPentagonRectangleSameSideOrder C x) :
    D.first.right = finRotate n D.first.left := by
  have hmem := (G.mem_initialPentagonRectangleSameSideOrder C x D).1 hD
  have hcount := (G.mem_initialPentagonRectangleDecompositions C D).1 hmem.1
  have hp := ((G.mem_initialPentagons D.pentagon).1 hcount.1).1
  have hempty : D.first.IsEmpty ∧ D.second.IsEmpty :=
    ⟨by
      simpa only [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
        using hp,
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles D.second).1
        hcount.2).1⟩
  exact (D.first.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
    D.second hmem.2.1).1 hempty

/-- In a counted opposite-side-order initial-side pentagon--rectangle term, the pentagon's
underlying rectangle spans one cyclic row. -/
theorem pentagon_top_eq_finRotate_bottom_of_mem_initialPentagonRectangleOppositeSideOrder
    (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.initialPentagonRectangleOppositeSideOrder C x) :
    D.first.top = finRotate n D.first.bottom := by
  have hmem := (G.mem_initialPentagonRectangleOppositeSideOrder C x D).1 hD
  have hcount := (G.mem_initialPentagonRectangleDecompositions C D).1 hmem.1
  have hp := ((G.mem_initialPentagons D.pentagon).1 hcount.1).1
  have hempty : D.first.IsEmpty ∧ D.second.IsEmpty :=
    ⟨by
      simpa only [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
        using hp,
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles D.second).1
        hcount.2).1⟩
  exact (D.first.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
    D.second hmem.2.1).1 hempty

end GridDiagram

end TauCeti
