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

* `TauCeti.GridRectangleDecomposition.IsRecutOfLeftEqRight.recut_geometry`: the two geometric
  branches of any recut when the first rectangle's initial side is the second rectangle's
  terminal side.
* `TauCeti.GridRectangleDecomposition.IsRecutOfRightEqLeft.recut_geometry`: the two geometric
  branches of any recut for the opposite mixed orientation.
* `TauCeti.GridRectangleDecomposition.recut_geometry_of_left_eq_right` and
  `TauCeti.GridRectangleDecomposition.recut_geometry_of_right_eq_left`: the same descriptions
  specialized to the canonical recut.

## References

The mixed recuts are the overlapping-domain decompositions in Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 4.6. Their use for commutation domains follows
Section 5.1 and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The complete geometry of a recut when the first rectangle's initial side is the second
rectangle's terminal side. The row containing the remaining corner selects whether the recut
rectangles share their initial or terminal side. -/
theorem IsRecutOfLeftEqRight.recut_geometry {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfLeftEqRight E) (hone : D.HasOneCommonSide) :
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
  have hcommon := hdata.side_eq
  have hother : D.first.right ≠ D.second.left := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, h,
        Finset.pair_comm])
  obtain ⟨hEfirstBottom, hEsecondBottom⟩ := hdata.recut_sides
  have hsecondLeft_ne_firstLeft : D.second.left ≠ D.first.left := fun h =>
    D.second.left_ne_right (h.trans hcommon)
  have hDsecondBottom : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def,
      D.first.map_of_ne D.second.left hsecondLeft_ne_firstLeft hother.symm]
  rcases hdata.recut_branch with
      ⟨hrow, hmiddle, hEfirstTop, hEsecondTop⟩ |
      ⟨hrow, hmiddle, hEfirstTop, hEsecondTop⟩
  · rw [hDsecondBottom, GridRectangleBetween.bottom_def] at hmiddle
    obtain ⟨hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight⟩ :=
      sides_of_middle_eq_swapRows hmiddle (hEfirstBottom.trans hDsecondBottom) hEfirstTop
        hEsecondBottom hEsecondTop
    rw [Equiv.swap_apply_right] at hEsecondLeft
    rw [Equiv.swap_apply_of_ne_of_ne hother D.first.left_ne_right.symm] at hEsecondRight
    exact Or.inl ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩
  · rw [hDsecondBottom, GridRectangleBetween.top_def] at hmiddle
    obtain ⟨hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight⟩ :=
      sides_of_middle_eq_swapRows hmiddle (hEfirstBottom.trans hDsecondBottom) hEfirstTop
        hEsecondBottom (hEsecondTop.trans hDsecondBottom)
    rw [Equiv.swap_apply_of_ne_of_ne hsecondLeft_ne_firstLeft.symm
      D.first.left_ne_right] at hEsecondLeft
    rw [Equiv.swap_apply_left] at hEsecondRight
    exact Or.inr ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩

/-- The complete geometry of a recut when the first rectangle's terminal side is the second
rectangle's initial side. The row containing the remaining corner selects whether the recut
rectangles share their terminal or initial side. -/
theorem IsRecutOfRightEqLeft.recut_geometry {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfRightEqLeft E) (hone : D.HasOneCommonSide) :
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
  have hcommon := hdata.side_eq
  have hother : D.first.left ≠ D.second.right := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, h,
        Finset.pair_comm])
  obtain ⟨hEfirstTop, hEsecondTop⟩ := hdata.recut_sides
  have hsecondRight_ne_firstRight : D.second.right ≠ D.first.right := by
    rw [hcommon]
    exact D.second.left_ne_right.symm
  have hDsecondTop : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def,
      D.first.map_of_ne D.second.right hother.symm hsecondRight_ne_firstRight]
  rcases hdata.recut_branch with
      ⟨hrow, hmiddle, hEfirstBottom, hEsecondBottom⟩ |
      ⟨hrow, hmiddle, hEfirstBottom, hEsecondBottom⟩
  · rw [hDsecondTop, GridRectangleBetween.top_def] at hmiddle
    obtain ⟨hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight⟩ :=
      sides_of_middle_eq_swapRows hmiddle hEfirstBottom (hEfirstTop.trans hDsecondTop)
        hEsecondBottom hEsecondTop
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right hother] at hEsecondLeft
    rw [Equiv.swap_apply_left] at hEsecondRight
    exact Or.inl ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩
  · rw [hDsecondTop, GridRectangleBetween.bottom_def] at hmiddle
    obtain ⟨hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight⟩ :=
      sides_of_middle_eq_swapRows hmiddle hEfirstBottom (hEfirstTop.trans hDsecondTop)
        (hEsecondBottom.trans hDsecondTop) hEsecondTop
    rw [Equiv.swap_apply_right] at hEsecondLeft
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right.symm
      hsecondRight_ne_firstRight.symm] at hEsecondRight
    exact Or.inr ⟨hrow, hEfirstLeft, hEfirstRight, hEsecondLeft, hEsecondRight,
      hEfirstBottom, hEfirstTop, hEsecondBottom, hEsecondTop⟩

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
              E.second.bottom = D.first.bottom ∧ E.second.top = D.second.bottom) :=
  (D.isRecutOfLeftEqRight_recut hcommon hone hfirst hsecond).recut_geometry hone

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
              E.second.bottom = D.second.top ∧ E.second.top = D.first.top) :=
  (D.isRecutOfRightEqLeft_recut hcommon hone hfirst hsecond).recut_geometry hone

end TauCeti.GridRectangleDecomposition
