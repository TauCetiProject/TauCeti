/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Marking
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.RectangleMarking
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Marking
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.RectangleMarking

/-!
# Counted overlap recuts for grid commutation

The pentagon chain-map equation for a column commutation compares a rectangle followed by a
pentagon with a pentagon followed by a rectangle. When the two domains have one common side,
recutting their union gives the contribution on the other side of the equation in two of the
three geometric branches:

* a common initial side always recuts to a pentagon followed by a rectangle;
* at a common terminal side, the same is true when the first recut rectangle inherits the
  replaced grid line.

The recut constructions already preserve emptiness. The marking results for their promoted
pentagons show that they are counted by the pentagon map, while the rectangle marking results
show that their remaining rectangles are counted by the differential of the commuted diagram.
This file packages those facts as membership in the finite decomposition family on the opposite
side of the chain-map equation.

The other common-terminal-side branch recuts to another rectangle--pentagon decomposition and
is paired within the same coefficient sum. Weight preservation and that self-pairing are
separate from membership.

## Main results

* `TauCeti.GridDiagram.recutLeftEqLeft_mem_pentagonRectangleDecompositions`: the
  common-initial-side recut of a counted rectangle--pentagon domain is counted on the other side.
* `TauCeti.GridDiagram.recutRightEqRightFirst_mem_pentagonRectangleDecompositions`: the
  cross-side common-terminal recut is counted on the other side.

## References

This is the overlap case of the pentagon--rectangle juxtaposition in
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

local notation "b" => finRotate n C.column

/-- Recutting a rectangle--pentagon decomposition along a common initial side produces a counted
pentagon--rectangle decomposition when its original domains satisfy the counting conditions. -/
theorem recutLeftEqLeft_mem_pentagonRectangleDecompositions
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet)
    (hPX : Disjoint D.pentagon.coveredSquares G.XSet) :
    D.recutLeftEqLeft hcommon hone hrectangle hpentagon ∈
      G.pentagonRectangleDecompositions C x z := by
  rw [G.mem_pentagonRectangleDecompositions C]
  refine ⟨(G.mem_pentagons _).2 ⟨?_, ?_⟩,
    ((G.swapColumns C.column b).mem_unblockedRectangles _).2 ⟨?_, ?_⟩⟩
  · exact D.isEmpty_pentagon_recutLeftEqLeft hcommon hone hrectangle hpentagon
  · exact D.disjoint_coveredSquares_XSet_pentagon_recutLeftEqLeft
      hcommon hone hrectangle hpentagon G hPX hrectX
  · exact D.isEmpty_rectangle_recutLeftEqLeft hcommon hone hrectangle hpentagon
  · exact D.disjoint_coveredSquares_XSet_rectangle_recutLeftEqLeft
      hcommon hone hrectangle hpentagon G hrectX hPX

/-- In a common-terminal-side overlap, if the first recut rectangle inherits the replaced grid
line, promoting it gives a counted pentagon--rectangle decomposition. -/
theorem recutRightEqRightFirst_mem_pentagonRectangleDecompositions
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet)
    (hPX : Disjoint D.pentagon.coveredSquares G.XSet)
    (hfirst :
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
        D.pentagon.right) :
    D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst ∈
      G.pentagonRectangleDecompositions C x z := by
  rw [G.mem_pentagonRectangleDecompositions C]
  refine ⟨(G.mem_pentagons _).2 ⟨?_, ?_⟩,
    ((G.swapColumns C.column b).mem_unblockedRectangles _).2 ⟨?_, ?_⟩⟩
  · exact D.isEmpty_pentagon_recutRightEqRightFirst
      hcommon hone hrectangle hpentagon hfirst
  · exact D.disjoint_coveredSquares_XSet_pentagon_recutRightEqRightFirst
      hcommon hone hrectangle hpentagon hfirst G hPX hrectX
  · exact D.isEmpty_rectangle_recutRightEqRightFirst
      hcommon hone hrectangle hpentagon hfirst
  · exact D.disjoint_coveredSquares_XSet_rectangle_recutRightEqRightFirst
      hcommon hone hrectangle hpentagon hfirst G hrectX

end TauCeti.GridDiagram
