/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic

/-!
# Branch determination for the terminal-side recut

When the rectangle and pentagon share their terminal side, knowing which of the two recut
rectangles inherits the pentagon's terminal side determines the recut branch: the other
rectangle's initial side then lies strictly inside the inheriting rectangle's column interval.
This fixes the column geometry used by the turn-row transports, which must handle the two
cases separately.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.first_recut_branch_data_of_right_eq_right`: if the
  first recut rectangle ends on the pentagon's terminal side, the recut branch is forced:
  the first recut rectangle spans from the original second rectangle's left side to the
  original first rectangle's right side, and the original second's left side lies in the
  original first's open column interval.
* `TauCeti.GridRectanglePentagonDecomposition.second_recut_branch_data_of_right_eq_right`: if the
  second recut rectangle ends on the pentagon's terminal side, the recut branch is forced:
  the second recut rectangle spans from the original first rectangle's left side to its
  right side with the column-swapped middle state, and the original first's left side lies
  in the original second's open column interval.

-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Common setup for the terminal-side branch determination: the pentagon's terminal side
is the common right side of the forgotten rectangle decomposition. -/
private theorem terminal_side_common_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.right ∧
      D.pentagon.right = D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  refine ⟨hcommon', ?_⟩
  rw [← toRectangleDecomposition_second_right D, ← hcommon']

/-- If the first recut rectangle carries the pentagon's terminal side, the recut branch is
forced: the first recut rectangle spans from the original second rectangle's left side to
the original first rectangle's right side, and the original second rectangle's left side
lies in the original first rectangle's open column interval. -/
theorem first_recut_branch_data_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recut_of_isEmpty hone hrectangle hpentagon).first.right = D.pentagon.right) :
    D.toRectangleDecomposition.second.left ∈
        Grid.cIoo D.toRectangleDecomposition.first.left
          D.toRectangleDecomposition.first.right ∧
      (D.recut_of_isEmpty hone hrectangle hpentagon).first.right =
        D.toRectangleDecomposition.first.right ∧
      (D.recut_of_isEmpty hone hrectangle hpentagon).first.left =
        D.toRectangleDecomposition.second.left := by
  obtain ⟨hcommon', hpen_right⟩ := D.terminal_side_common_right hcommon
  -- View the branch data as data about the shared recut (definitionally the same
  -- construction, by proof irrelevance of the emptiness arguments).
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recut_of_isEmpty hone hrectangle hpentagon) :=
    D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨-, -, hEfirst, -⟩ | ⟨hcol, -, hEfirstB, -⟩
  · -- First branch: E.first.right = D.first.left, so D.first.left = D.pentagon.right
    -- = D.first.right, contradicting left_ne_right.
    exfalso
    rw [hEfirst, hpen_right] at hfirst
    exact D.toRectangleDecomposition.first.left_ne_right hfirst
  · exact ⟨hcol, hEfirstB, hdata.recut_sides.1⟩

/-- If the second recut rectangle carries the pentagon's terminal side, the recut branch is
forced: the second recut rectangle spans from the original first rectangle's left side to
the original first rectangle's right side with the column-swapped middle state, and the
original first rectangle's left side lies in the original second rectangle's open column
interval. -/
theorem second_recut_branch_data_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recut_of_isEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.left ∈
        Grid.cIoo D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.right ∧
      (D.recut_of_isEmpty hone hrectangle hpentagon).second.right =
        D.toRectangleDecomposition.first.right ∧
      (D.recut_of_isEmpty hone hrectangle hpentagon).second.left =
        D.toRectangleDecomposition.first.left ∧
      (D.recut_of_isEmpty hone hrectangle hpentagon).middle =
        x.swapColumns D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.left := by
  obtain ⟨hcommon', hpen_right⟩ := D.terminal_side_common_right hcommon
  -- View the branch data as data about the shared recut (definitionally the same
  -- construction, by proof irrelevance of the emptiness arguments).
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recut_of_isEmpty hone hrectangle hpentagon) :=
    D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨hcol, hmiddleA, -, hEsecondA⟩ | ⟨-, -, -, hEsecondB⟩
  · exact ⟨hcol, hEsecondA, hdata.recut_sides.2, hmiddleA⟩
  · -- Second branch: E.second.right = D.second.left, so D.second.left = D.pentagon.right
    -- = D.first.right = D.second.right (by hcommon'), contradicting left_ne_right.
    exfalso
    rw [hEsecondB, hpen_right, hcommon'] at hsecond
    exact D.toRectangleDecomposition.second.left_ne_right hsecond

end GridRectanglePentagonDecomposition

end TauCeti
