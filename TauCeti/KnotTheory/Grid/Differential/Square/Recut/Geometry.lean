/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Geometry of mixed-side rectangle recuts

Two composable empty grid rectangles with exactly one common side admit a canonical recut. When
the common side is terminal for one rectangle and initial for the other, the generic recut API
records its rows but not its side columns. This file reconstructs those columns from the source
and intermediate grid states, giving a complete geometric description in both mixed
orientations.

The two alternatives in each result are the two possible cyclic orders of the three corner rows.
In either branch, the displayed side and row equalities determine which recut rectangle can be
promoted to a polygon with prescribed turn data. This is the interface used by juxtaposition
arguments for grid differentials and commutation maps.

## Main results

* `TauCeti.GridRectangleDecomposition.recut_geometry_of_left_eq_right`: the two geometric
  branches when the first rectangle's initial side is the second rectangle's terminal side.
* `TauCeti.GridRectangleDecomposition.recut_geometry_of_right_eq_left`: the two geometric
  branches for the opposite mixed orientation.

## References

The mixed recuts are the overlapping-domain decompositions in Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 4.6. Their use for commutation domains follows
Section 5.1 and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The complete geometry of the canonical recut when the first rectangle's initial side is the
second rectangle's terminal side. The row containing the remaining corner selects whether the
recut rectangles share their initial or terminal side. -/
theorem recut_geometry_of_left_eq_right (D : GridRectangleDecomposition x z)
    (hcommon : D.first.left = D.second.right) (hone : D.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    let E := D.recut hone hfirst hsecond
    (D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
        E.first.left = D.second.left ∧ E.first.right = D.first.left ∧
          E.second.left = D.second.left ∧ E.second.right = D.first.right ∧
            E.first.bottom = D.second.bottom ∧ E.first.top = D.first.bottom ∧
              E.second.bottom = D.first.bottom ∧ E.second.top = D.first.top) ∨
      (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
        E.first.left = D.second.left ∧ E.first.right = D.first.right ∧
          E.second.left = D.first.left ∧ E.second.right = D.first.right ∧
            E.first.bottom = D.second.bottom ∧ E.first.top = D.first.top ∧
              E.second.bottom = D.first.bottom ∧ E.second.top = D.second.bottom) := by
  intro E
  have hother : D.first.right ≠ D.second.left := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, h,
        Finset.pair_comm])
  have hdata := D.isRecutOfLeftEqRight_recut hcommon hone hfirst hsecond
  obtain ⟨hEfirstBottom, hEsecondBottom⟩ := hdata.recut_sides
  have hsecondLeft_ne_firstLeft : D.second.left ≠ D.first.left := fun h =>
    D.second.left_ne_right (h.trans hcommon)
  have hmiddle_secondLeft : D.middle D.second.left = x D.second.left :=
    D.first.map_of_ne D.second.left hsecondLeft_ne_firstLeft hother.symm
  have hDsecondBottom : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, hmiddle_secondLeft]
  rcases hdata.recut_branch with
      ⟨hrow, hmiddle, hEfirstTop, hEsecondTop⟩ |
      ⟨hrow, hmiddle, hEfirstTop, hEsecondTop⟩
  · have hmiddle' : E.middle = x.swapColumns D.second.left D.first.left := by
      rw [hmiddle, hDsecondBottom, GridRectangleBetween.bottom_def,
        GridState.swapColumns_eq_swapRows]
    have hEfirstLeft : E.first.left = D.second.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def, hEfirstBottom, hDsecondBottom]
    have hEfirstRight : E.first.right = D.first.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.top_def, hEfirstTop, GridRectangleBetween.bottom_def]
    have hEsecondLeft : E.second.left =
        Equiv.swap D.second.left D.first.left D.first.left := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.bottom_def, hEsecondBottom,
        GridRectangleBetween.bottom_def]
    have hEsecondRight : E.second.right =
        Equiv.swap D.second.left D.first.left D.first.right := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.top_def, hEsecondTop, GridRectangleBetween.top_def]
    rw [Equiv.swap_apply_right] at hEsecondLeft
    rw [Equiv.swap_apply_of_ne_of_ne hother D.first.left_ne_right.symm] at hEsecondRight
    exact Or.inl ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩
  · have hmiddle' : E.middle = x.swapColumns D.second.left D.first.right := by
      rw [hmiddle, hDsecondBottom, GridRectangleBetween.top_def,
        GridState.swapColumns_eq_swapRows]
    have hEfirstLeft : E.first.left = D.second.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def, hEfirstBottom, hDsecondBottom]
    have hEfirstRight : E.first.right = D.first.right := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.top_def, hEfirstTop, GridRectangleBetween.top_def]
    have hEsecondLeft : E.second.left =
        Equiv.swap D.second.left D.first.right D.first.left := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.bottom_def, hEsecondBottom,
        GridRectangleBetween.bottom_def]
    have hEsecondRight : E.second.right =
        Equiv.swap D.second.left D.first.right D.second.left := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.top_def, hEsecondTop, hDsecondBottom]
    rw [Equiv.swap_apply_of_ne_of_ne hsecondLeft_ne_firstLeft.symm
      D.first.left_ne_right] at hEsecondLeft
    rw [Equiv.swap_apply_left] at hEsecondRight
    exact Or.inr ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩

/-- The complete geometry of the canonical recut when the first rectangle's terminal side is the
second rectangle's initial side. The row containing the remaining corner selects whether the
recut rectangles share their terminal or initial side. -/
theorem recut_geometry_of_right_eq_left (D : GridRectangleDecomposition x z)
    (hcommon : D.first.right = D.second.left) (hone : D.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    let E := D.recut hone hfirst hsecond
    (D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
        E.first.left = D.first.right ∧ E.first.right = D.second.right ∧
          E.second.left = D.first.left ∧ E.second.right = D.second.right ∧
            E.first.bottom = D.first.top ∧ E.first.top = D.second.top ∧
              E.second.bottom = D.first.bottom ∧ E.second.top = D.first.top) ∨
      (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
        E.first.left = D.first.left ∧ E.first.right = D.second.right ∧
          E.second.left = D.first.left ∧ E.second.right = D.first.right ∧
            E.first.bottom = D.first.bottom ∧ E.first.top = D.second.top ∧
              E.second.bottom = D.second.top ∧ E.second.top = D.first.top) := by
  intro E
  have hother : D.first.left ≠ D.second.right := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, h,
        Finset.pair_comm])
  have hdata := D.isRecutOfRightEqLeft_recut hcommon hone hfirst hsecond
  obtain ⟨hEfirstTop, hEsecondTop⟩ := hdata.recut_sides
  have hsecondRight_ne_firstRight : D.second.right ≠ D.first.right := by
    rw [hcommon]
    exact D.second.left_ne_right.symm
  have hmiddle_secondRight : D.middle D.second.right = x D.second.right :=
    D.first.map_of_ne D.second.right hother.symm hsecondRight_ne_firstRight
  have hDsecondTop : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def, hmiddle_secondRight]
  rcases hdata.recut_branch with
      ⟨hrow, hmiddle, hEfirstBottom, hEsecondBottom⟩ |
      ⟨hrow, hmiddle, hEfirstBottom, hEsecondBottom⟩
  · have hmiddle' : E.middle = x.swapColumns D.first.right D.second.right := by
      rw [hmiddle, hDsecondTop, GridRectangleBetween.top_def,
        GridState.swapColumns_eq_swapRows]
    have hEfirstLeft : E.first.left = D.first.right := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def, hEfirstBottom,
        GridRectangleBetween.top_def]
    have hEfirstRight : E.first.right = D.second.right := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.top_def, hEfirstTop, hDsecondTop]
    have hEsecondLeft : E.second.left =
        Equiv.swap D.first.right D.second.right D.first.left := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.bottom_def, hEsecondBottom,
        GridRectangleBetween.bottom_def]
    have hEsecondRight : E.second.right =
        Equiv.swap D.first.right D.second.right D.first.right := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.top_def, hEsecondTop, GridRectangleBetween.top_def]
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right hother] at hEsecondLeft
    rw [Equiv.swap_apply_left] at hEsecondRight
    exact Or.inl ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩
  · have hmiddle' : E.middle = x.swapColumns D.first.left D.second.right := by
      rw [hmiddle, hDsecondTop, GridRectangleBetween.bottom_def,
        GridState.swapColumns_eq_swapRows]
    have hEfirstLeft : E.first.left = D.first.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def, hEfirstBottom,
        GridRectangleBetween.bottom_def]
    have hEfirstRight : E.first.right = D.second.right := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.top_def, hEfirstTop, hDsecondTop]
    have hEsecondLeft : E.second.left =
        Equiv.swap D.first.left D.second.right D.second.right := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.bottom_def, hEsecondBottom, hDsecondTop]
    have hEsecondRight : E.second.right =
        Equiv.swap D.first.left D.second.right D.first.right := by
      apply GridState.eq_swap_of_swapColumns_apply_eq
      rw [← hmiddle']
      rw [← GridRectangleBetween.top_def, hEsecondTop, GridRectangleBetween.top_def]
    rw [Equiv.swap_apply_right] at hEsecondLeft
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right.symm
      hsecondRight_ne_firstRight.symm] at hEsecondRight
    exact Or.inr ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩

end TauCeti.GridRectangleDecomposition
