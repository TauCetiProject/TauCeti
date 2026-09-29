/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.TerminalMarking
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
  obtain ⟨hcol, _, _⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hfirst
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  obtain ⟨_, hsecondLeft⟩ := hdata.recut_sides
  have hbranch : (D.recutOfIsEmpty hone hrectangle hpentagon).middle =
      x.swapColumns D.pentagon.left D.rectangle.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.left := by
    rcases hdata.recut_branch with h | h
    · have hh := h.2.2.1
      rw [hfirst] at hh
      have hh' : D.rectangle.right = D.rectangle.left := by
        simpa only [toRectangleDecomposition_first_left, hcommon] using hh
      exact False.elim (D.rectangle.left_ne_right hh'.symm)
    · constructor
      · simpa only [toRectangleDecomposition_second_left,
          toRectangleDecomposition_first_right] using h.2.1
      · simpa only [toRectangleDecomposition_second_left] using h.2.2.2
  have hEleft : E.rectangle.left = D.rectangle.left := by
    exact (D.recutRightEqRightFirst_rectangle_left hcommon hone hrectangle hpentagon hfirst).trans
      (hsecondLeft.trans D.toRectangleDecomposition_first_left)
  have hEright : E.rectangle.right = D.pentagon.left :=
    (D.recutRightEqRightFirst_rectangle_right hcommon hone hrectangle hpentagon hfirst).trans
      hbranch.2
  have hEbottom : E.rectangle.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, hEleft,
      D.recutRightEqRightFirst_middle hcommon hone hrectangle hpentagon hfirst,
      hbranch.1, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (Grid.ne_left_of_mem_cIoo hcol).symm
        D.rectangle.left_ne_right, ← GridRectangleBetween.bottom_def]
  have hEtop : E.rectangle.top = D.rectangle.top := by
    rw [GridRectangleBetween.top_def, hEright,
      D.recutRightEqRightFirst_middle hcommon hone hrectangle hpentagon hfirst,
      hbranch.1, GridState.swapColumns_apply, Equiv.swap_apply_left,
      ← GridRectangleBetween.top_def]
  have hRows : E.rectangle.toGridRectangle.coveredRows ⊆
      D.rectangle.toGridRectangle.coveredRows := by
    simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, hEbottom, hEtop]
    exact Finset.Subset.rfl
  have ha : a ∈ D.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hcommon, D.pentagon.right_eq]
    exact Grid.self_mem_cIco_finRotate (by
      intro h
      exact D.rectangle.left_ne_right ((h.trans D.pentagon.right_eq.symm).trans hcommon.symm))
  have haNot : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro haE
    have hcol' : D.pentagon.left ∈ Grid.cIoo D.rectangle.left (finRotate n a) := by
      simpa only [hcommon, D.pentagon.right_eq] using hcol
    have htail : a ∈ Grid.cIco D.pentagon.left (finRotate n a) :=
      Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol')
    exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')) haE htail
  have hCols : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.rectangle.toGridRectangle.coveredColumns := by
    intro c hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright] at hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right]
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol]
    exact Finset.mem_union.mpr (Or.inl hc)
  exact G.disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    D.rectangle.toGridRectangle E.rectangle.toGridRectangle hRows hrectX ha haNot hCols

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
  obtain ⟨hcol, _, _, _⟩ :=
    D.second_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hsecond
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hEleft : E.rectangle.left = D.pentagon.left :=
    (D.recutRightEqRightSecond_rectangle_left hcommon hone hrectangle hpentagon hsecond).trans
      (hdata.recut_sides.1.trans D.toRectangleDecomposition_second_left)
  have hfirstRight : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.rectangle.left := by
    rcases hdata.recut_branch with h | h
    · simpa only [toRectangleDecomposition_first_left] using h.2.2.1
    · have hh : D.pentagon.right = D.pentagon.left := by
        simpa only [toRectangleDecomposition_second_left] using hsecond.symm.trans h.2.2.2
      exact False.elim (D.pentagon.left_ne_right hh.symm)
  have hEright : E.rectangle.right = D.rectangle.left :=
    (D.recutRightEqRightSecond_rectangle_right hcommon hone hrectangle hpentagon hsecond).trans
      hfirstRight
  have hPbottom : D.pentagon.bottom = x D.pentagon.left := by
    rw [GridRectangleBetween.bottom_def]
    exact D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol).symm
      (fun h => D.pentagon.left_ne_right (h.trans hcommon))
  have hPtop : D.pentagon.top = x D.rectangle.left := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_right,
      ← GridRectangleBetween.bottom_def]
  have hEbottom : E.rectangle.bottom = D.pentagon.bottom := by
    rw [GridRectangleBetween.bottom_def, hEleft, ← hPbottom]
  have hEtop : E.rectangle.top = D.pentagon.top := by
    rw [GridRectangleBetween.top_def, hEright, ← hPtop]
  have hcol' : D.rectangle.left ∈ Grid.cIoo D.pentagon.left (finRotate n a) := by
    simpa only [hcommon, D.pentagon.right_eq] using hcol
  have haNot : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro haE
    have htail : a ∈ Grid.cIco D.rectangle.left (finRotate n a) :=
      Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol')
    exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')) haE htail
  have hbNot : finRotate n a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro hb
    exact Grid.right_notMem_cIco D.pentagon.left (finRotate n a)
      (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hb hcol')
  have hRows : E.rectangle.toGridRectangle.coveredRows =
      D.pentagon.toGridRectangle.coveredRows := by
    simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, hEbottom, hEtop]
  have hCols : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.pentagon.toGridRectangle.coveredColumns := by
    intro c hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright] at hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, D.pentagon.right_eq]
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol']
    exact Finset.mem_union.mpr (Or.inl hc)
  have hEdisj : Disjoint E.rectangle.toGridRectangle.coveredSquares G.XSet := by
    rw [Finset.disjoint_left]
    intro p hp hpX
    have hpcol : p.1 ∈ E.rectangle.toGridRectangle.coveredColumns :=
      (GridRectangle.mem_coveredSquares E.rectangle.toGridRectangle p).mp hp |>.1
    have hpP : p ∈ D.pentagon.toGridRectangle.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares] at hp ⊢
      exact ⟨hCols hp.1, hRows ▸ hp.2⟩
    exact (Finset.disjoint_left.mp hPX)
      ((D.pentagon.mem_coveredSquares_iff_of_ne
        (fun h => haNot (h ▸ hpcol)) (fun h => hbNot (h ▸ hpcol))).2 hpP) hpX
  have hboth : a ∈ E.rectangle.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ E.rectangle.toGridRectangle.coveredColumns :=
    iff_of_false haNot hbNot
  exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
    E.rectangle.toGridRectangle hboth).2 hEdisj

end TauCeti.GridRectanglePentagonDecomposition
