/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Right
public import TauCeti.KnotTheory.Grid.Rectangle.Squares

/-!
# X-avoidance of the remaining rectangle in a terminal-side overlap

When a rectangle followed by a pentagon shares its terminal side, recutting their union
promotes one of the new rectangles to a pentagon. The other new rectangle must avoid the
X-markings of the commuted diagram for the recut to contribute to the pentagon chain-map
equation. In the branch where the first new rectangle is promoted, the remaining rectangle
occupies a subinterval of the original rectangle's columns and the same rows. In the other
branch it is a subrectangle of the original pentagon away from the two columns affected by
commutation.

The grid differential's square-zero prerequisite is proved in
`TauCeti.KnotTheory.Grid.Differential.Square.Zero`.

The recut is the common-terminal-side case of Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- In the branch of a common-terminal-side recut where the first new rectangle becomes a
pentagon, the remaining rectangle avoids X-markings after the column swap whenever the original
rectangle does. -/
theorem disjoint_coveredSquares_XSet_rectangle_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right)
    (G : GridDiagram n)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet) :
    Disjoint
      (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon
        hfirst).rectangle.toGridRectangle.coveredSquares
      (G.swapColumns a (finRotate n a)).XSet := by
  let E := D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  obtain ⟨_, _, hbottom, htop, hCols, haNot, ha⟩ :=
    D.recutRightEqRightFirst_rectangle_geometry hcommon hone hrectangle hpentagon hfirst
  have hbottomE : E.rectangle.bottom = D.rectangle.bottom := by
    simpa only [E] using hbottom
  have htopE : E.rectangle.top = D.rectangle.top := by
    simpa only [E] using htop
  have hColsE : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.rectangle.toGridRectangle.coveredColumns := by
    simpa only [E] using hCols
  have haNotE : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    simpa only [E] using haNot
  have hRows : E.rectangle.toGridRectangle.coveredRows ⊆
      D.rectangle.toGridRectangle.coveredRows := by
    simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, hbottomE, htopE]
    exact Finset.Subset.rfl
  exact G.disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    D.rectangle.toGridRectangle E.rectangle.toGridRectangle hRows hrectX ha haNotE hColsE

/-- In the branch of a common-terminal-side recut where the second new rectangle becomes a
pentagon, the remaining rectangle avoids X-markings after the column swap whenever the original
pentagon does. -/
theorem disjoint_coveredSquares_XSet_rectangle_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right)
    (G : GridDiagram n)
    (hPX : Disjoint D.pentagon.coveredSquares G.XSet) :
    Disjoint
      (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon
        hsecond).rectangle.toGridRectangle.coveredSquares
      (G.swapColumns a (finRotate n a)).XSet := by
  let E := D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  obtain ⟨_, _, hbottom, htop, hCols, haNot, hbNot⟩ :=
    D.recutRightEqRightSecond_rectangle_geometry hcommon hone hrectangle hpentagon hsecond
  have hbottomE : E.rectangle.bottom = D.pentagon.bottom := by
    simpa only [E] using hbottom
  have htopE : E.rectangle.top = D.pentagon.top := by
    simpa only [E] using htop
  have hColsE : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.pentagon.toGridRectangle.coveredColumns := by
    simpa only [E] using hCols
  have haNotE : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    simpa only [E] using haNot
  have hbNotE : finRotate n a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    simpa only [E] using hbNot
  have hRows : E.rectangle.toGridRectangle.coveredRows =
      D.pentagon.toGridRectangle.coveredRows := by
    simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, hbottomE, htopE]
  have hEdisj : Disjoint E.rectangle.toGridRectangle.coveredSquares G.XSet := by
    rw [Finset.disjoint_left]
    intro p hp hpX
    have hpcol : p.1 ∈ E.rectangle.toGridRectangle.coveredColumns :=
      (GridRectangle.mem_coveredSquares E.rectangle.toGridRectangle p).mp hp |>.1
    have hpP : p ∈ D.pentagon.toGridRectangle.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares] at hp ⊢
      exact ⟨hColsE hp.1, hRows ▸ hp.2⟩
    exact (Finset.disjoint_left.mp hPX)
      ((D.pentagon.mem_coveredSquares_iff_of_ne
        (fun h => haNotE (h ▸ hpcol)) (fun h => hbNotE (h ▸ hpcol))).2 hpP) hpX
  have hboth : a ∈ E.rectangle.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ E.rectangle.toGridRectangle.coveredColumns :=
    iff_of_false haNotE hbNotE
  exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
    E.rectangle.toGridRectangle hboth).2 hEdisj

end TauCeti.GridRectanglePentagonDecomposition
