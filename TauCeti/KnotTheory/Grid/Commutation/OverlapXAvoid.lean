/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.Pentagon

/-!
# X-avoidance for the recut pentagon's extra strip

When `recutLeftEqLeft` promotes the first recut rectangle to a pentagon via `ofRightEq`, the new
pentagon's `coveredSquares` includes an extra strip `{finRotate n a} ×ˢ cIco bottom s` beyond its
underlying rectangle. The new pentagon's bottom row is the recut's first rectangle's bottom row.

This file establishes X-avoidance for that strip in the first recut branch, where the recut's
first rectangle's bottom row coincides with the original pentagon's bottom row. Both are `x`
applied to the original rectangle's terminal side.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}
variable {x z : GridState n}

/-- In the first recut branch, the recut's first rectangle's bottom row equals the original
pentagon's bottom row. -/
public theorem recut_first_bottom_eq_pentagon_bottom_of_branch1
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
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

/-- X-avoidance for the `finRotate` strip in the first recut branch. The strip's row interval
coincides with the original pentagon's, so the original X-avoidance applies. -/
public theorem recut_X_not_mem_of_branch1
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hmem : D.pentagon ∈ G.pentagons C D.middle z)
    (hfirstLeft : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.left = D.toRectangleDecomposition.first.right) :
    G.X (finRotate n C.column) ∉
      Grid.cIco (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
            hpentagon)).first.bottom C.turnRow := by
  have hempty1 : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hempty2 : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle,
      D.toRectangleDecomposition_second_toGridRectangle] using hpentagon
  -- Get X-avoidance of the original pentagon.
  rw [G.mem_pentagons] at hmem
  obtain ⟨-, hdisjoint⟩ := hmem
  -- The bottoms coincide, so the intervals are equal.
  have hbot := D.recut_first_bottom_eq_pentagon_bottom_of_branch1 hcommon hone
    hrectangle hpentagon hfirstLeft
  -- Rewrite the goal to use the explicit recut with named proofs.
  have hgoal : G.X (finRotate n C.column) ∉
      Grid.cIco (D.toRectangleDecomposition.recut hone hempty1 hempty2).first.bottom C.turnRow := by
    have heq : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
            hpentagon)).first.bottom =
        (D.toRectangleDecomposition.recut hone hempty1 hempty2).first.bottom := rfl
    rw [heq]
    rw [hbot]
    intro hXmem
    have hmem' : (finRotate n C.column, G.X (finRotate n C.column)) ∈
        D.pentagon.coveredSquares := by
      rw [D.pentagon.mem_coveredSquares]
      exact Or.inr (Or.inr ⟨rfl, hXmem⟩)
    have hXmem' : (finRotate n C.column, G.X (finRotate n C.column)) ∈ G.XSet := by
      simp [GridDiagram.XSet]
    exact Finset.disjoint_left.mp hdisjoint hmem' hXmem'
  exact hgoal

end GridRectanglePentagonDecomposition

end TauCeti
