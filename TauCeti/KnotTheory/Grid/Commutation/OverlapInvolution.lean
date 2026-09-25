/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Branch determination for the terminal-side recut

When the rectangle and pentagon share their terminal side, knowing which of the two recut
rectangles inherits the pentagon's terminal side determines the recut branch: the other
rectangle's initial side then lies strictly inside the inheriting rectangle's column interval.
This fixes the column geometry used by the turn-row transports, which must handle the two
cases separately.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recut_branch_of_first_right_eq`: if the first
  recut rectangle ends on the pentagon's terminal side, the original second rectangle's
  initial side lies in the open column interval of the original first rectangle.
* `TauCeti.GridRectanglePentagonDecomposition.recut_branch_of_second_right_eq`: if the second
  recut rectangle ends on the pentagon's terminal side, the original first rectangle's
  initial side lies in the open column interval of the original second rectangle.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- If the first recut rectangle has the pentagon's terminal side, the recut is in the
second branch of `IsRecutOfRightEqRight` (where `E.first.right = D.first.right`). -/
theorem recut_branch_of_first_right_eq
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first.right = D.pentagon.right) :
    D.toRectangleDecomposition.second.left ∈
        Grid.cIoo D.toRectangleDecomposition.first.left
          D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨hcol, -, hEfirst, -⟩ | ⟨hcol, -, -, -⟩
  · -- First branch: E.first.right = D.first.left, so D.first.left = D.pentagon.right
    -- = D.first.right, contradicting left_ne_right.
    exfalso
    rw [hEfirst, hpen_right] at hfirst
    exact D.toRectangleDecomposition.first.left_ne_right hfirst
  · exact hcol

/-- If the second recut rectangle has the pentagon's terminal side, the recut is in the
first branch of `IsRecutOfRightEqRight` (where `E.second.right = D.first.right`). -/
theorem recut_branch_of_second_right_eq
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.left ∈
        Grid.cIoo D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨hcol, -, -, hEsecond⟩ | ⟨-, -, -, hEsecond⟩
  · exact hcol
  · -- Second branch: E.second.right = D.second.left, so D.second.left = D.pentagon.right
    -- = D.first.right = D.second.right (by hcommon'), contradicting left_ne_right.
    exfalso
    rw [hEsecond, hpen_right, hcommon'] at hsecond
    exact D.toRectangleDecomposition.second.left_ne_right hsecond

end GridRectanglePentagonDecomposition

end TauCeti
