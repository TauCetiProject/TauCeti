/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Marking
import TauCeti.KnotTheory.Grid.CyclicInterval

/-!
# X-avoidance of the rectangle in a common-initial-side commutation recut

When a rectangle followed by a pentagon shares its initial side, recutting their union produces
a pentagon followed by a rectangle. The new rectangle must avoid the X-markings in the *commuted*
grid. In one cyclic column order it covers neither commuted column; in the other it covers the
terminal subinterval of the original rectangle, and the column swap replaces a covered column
by the excluded one. The latter case uses the X-avoidance transfer for subintervals.

The recut is the common-initial-side part of the pentagon chain-map argument in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- In the common-initial-side recut, the promoted rectangle avoids X-markings of the commuted
diagram when the original rectangle and pentagon avoid X-markings of the original diagram. -/
theorem disjoint_coveredSquares_XSet_rectangle_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (G : GridDiagram n)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet)
    (hPX : Disjoint D.pentagon.coveredSquares G.XSet) :
    Disjoint
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.toGridRectangle.coveredSquares
      (G.swapColumns a (finRotate n a)).XSet := by
  let E := D.recutLeftEqLeft hcommon hone hrectangle hpentagon
  have hE : E.toRectangleDecomposition = D.recutOfIsEmpty hone hrectangle hpentagon := by
    simpa only [E, D.recutOfIsEmpty_eq_recut] using
      D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut
      (by simpa only [toRectangleDecomposition_first_left,
        toRectangleDecomposition_second_left] using hcommon) hone _ _
  have hEright : E.rectangle.right = D.rectangle.right := by
    have h := hdata.recut_sides.2
    rw [← hE] at h
    simpa only [toRectangleDecomposition_first_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] using h
  rcases hdata.recut_branch with ⟨hcol, _, _, hsecondleft⟩ |
    ⟨hcol, hmiddle, _, hsecondleft⟩
  -- The recut rectangle covers neither swapped column. Repartition reduces its X-avoidance
  -- to that of the original rectangle and pentagon.
  · have hEleft : E.rectangle.left = D.rectangle.left := by
      rw [← hE] at hsecondleft
      simpa only [toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left] using hsecondleft
    have hcol' : D.rectangle.right ∈
        Grid.cIoo D.rectangle.left (finRotate n a) := by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hcol
    have hne : D.rectangle.right ≠ finRotate n a :=
      Grid.ne_right_of_mem_cIoo hcol'
    have haTail : a ∈ Grid.cIco D.rectangle.right (finRotate n a) :=
      Grid.self_mem_cIco_finRotate hne
    have haNot : a ∉ Grid.cIco E.rectangle.left E.rectangle.right := by
      rw [hEleft, hEright]
      exact fun ha => (Finset.disjoint_left.mp
        (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')) ha haTail
    have hbNot : finRotate n a ∉ Grid.cIco E.rectangle.left E.rectangle.right := by
      rw [hEleft, hEright]
      intro hb
      exact Grid.right_notMem_cIco D.rectangle.left (finRotate n a)
        (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hb hcol')
    have hEdisj : Disjoint E.rectangle.toGridRectangle.coveredSquares G.XSet := by
      rw [Finset.disjoint_left]
      intro p hp hpX
      have hpcol : p.1 ∈ Grid.cIco E.rectangle.left E.rectangle.right := by
        simpa only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
          GridRectangleBetween.toGridRectangle_left,
          GridRectangleBetween.toGridRectangle_right] using
          (GridRectangle.mem_coveredSquares E.rectangle.toGridRectangle p).mp hp |>.1
      have h := D.coveredSquares_union_recutLeftEqLeft hcommon hone hrectangle hpentagon
      have hpUnion : p ∈ D.rectangle.toGridRectangle.coveredSquares ∪
          D.pentagon.toGridRectangle.coveredSquares := by
        rw [← h]
        exact Finset.mem_union.mpr (Or.inr hp)
      rcases Finset.mem_union.mp hpUnion with hpR | hpP
      · exact (Finset.disjoint_left.mp hrectX) hpR hpX
      · exact (Finset.disjoint_left.mp hPX)
          ((D.pentagon.mem_coveredSquares_iff_of_ne (fun h => haNot (h ▸ hpcol))
            (fun h => hbNot (h ▸ hpcol))).2 hpP) hpX
    have hboth : a ∈ E.rectangle.toGridRectangle.coveredColumns ↔
        finRotate n a ∈ E.rectangle.toGridRectangle.coveredColumns := by
      simpa only [GridRectangle.mem_coveredColumns,
        GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right] using iff_of_false haNot hbNot
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
      E.rectangle.toGridRectangle hboth).2 hEdisj
  -- The recut rectangle starts at the replaced line. It has the original rectangle's row
  -- interval and a smaller column interval, so subinterval transfer applies.
  · have hEleft : E.rectangle.left = finRotate n a := by
      rw [← hE] at hsecondleft
      simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hsecondleft
    have hcol' : finRotate n a ∈
        Grid.cIoo D.rectangle.left D.rectangle.right := by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hcol
    have hEmiddle : E.middle = x.swapColumns D.rectangle.left (finRotate n a) := by
      rw [← hE] at hmiddle
      simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
        toRectangleDecomposition_first_left, toRectangleDecomposition_second_right,
        D.pentagon.right_eq] using hmiddle
    have hEbottom : E.rectangle.bottom = D.rectangle.bottom := by
      rw [GridRectangleBetween.bottom_def, hEleft, hEmiddle,
        GridState.swapColumns_apply, Equiv.swap_apply_right,
        ← GridRectangleBetween.bottom_def]
    have hEtop : E.rectangle.top = D.rectangle.top := by
      rw [GridRectangleBetween.top_def, hEright, hEmiddle,
        GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne D.rectangle.left_ne_right.symm
          (Grid.ne_right_of_mem_cIoo hcol').symm,
        ← GridRectangleBetween.top_def]
    have hRows : E.rectangle.toGridRectangle.coveredRows ⊆
        D.rectangle.toGridRectangle.coveredRows := by
      simp only [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top, hEbottom, hEtop]
      exact fun _ h => h
    have ha : a ∈ D.rectangle.toGridRectangle.coveredColumns := by
      rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right]
      exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo
        (Grid.self_mem_cIco_finRotate (Grid.ne_left_of_mem_cIoo hcol').symm) hcol'
    have haNot : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
      rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
      simpa only [finRotate_apply] using
        Grid.notMem_cIco_finRotate_left a D.rectangle.right
    have hCols : E.rectangle.toGridRectangle.coveredColumns ⊆
        D.rectangle.toGridRectangle.coveredColumns := by
      intro c hc
      rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, hEleft, hEright] at hc
      rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right]
      exact Grid.cIco_subset_of_mem_cIoo hcol' hc
    exact G.disjoint_coveredSquares_XSet_swapColumns_of_subinterval
      D.rectangle.toGridRectangle E.rectangle.toGridRectangle hRows hrectX ha haNot hCols

end GridRectanglePentagonDecomposition

end TauCeti
