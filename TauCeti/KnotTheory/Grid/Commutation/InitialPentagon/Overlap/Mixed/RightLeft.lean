/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Recutting an initial-side pentagon from a mixed terminal--initial side

Consider a rectangle followed by a commutation pentagon turning on its initial side. This file
treats the mixed overlap in which the rectangle's terminal side is the pentagon's initial side.
If the rectangle itself does not contain the turn row, the generic empty-rectangle recut has its
first rectangle starting on the replaced grid line and containing the turn row. It therefore
promotes to an initial-side pentagon followed by a rectangle.

The excluded case, where both original pieces contain the turn row, is the turn-point cut: the
same two underlying rectangles are instead read using the two different kinds of commutation
pentagon. Thus this file supplies the recut for the remaining branch of the `right = left` mixed
overlap in the grid-commutation chain-map equation.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.rightLeftRecut_geometry`: the generic
  recut starts on the replaced line and contains the turn row.
* `TauCeti.GridRectangleInitialPentagonDecomposition.recutRightEqLeft`: the corresponding
  promoted initial-side-pentagon--rectangle decomposition.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A mixed overlap whose rectangle terminal side is the pentagon initial side has exactly one
common side column. -/
theorem hasOneCommonSide_of_right_eq_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right) : D.HasOneCommonSide := by
  apply D.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.first.right, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, hcommon] at hc
    have hfirst := D.first.left_ne_right
    have hsecond := D.second.left_ne_right
    grind

private theorem underlying_second_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.second.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at h ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using h

/-- The generic empty-rectangle recut of a mixed overlap whose first terminal side is the second
initial side. -/
noncomputable def rightLeftRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    GridRectangleDecomposition x z :=
  D.recut (D.hasOneCommonSide_of_right_eq_left hcommon hother)
    hfirst (D.underlying_second_isEmpty hsecond)

/-- The generic construction is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_rightLeftRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    D.IsRecut (D.rightLeftRecut hcommon hother hfirst hsecond) :=
  D.isRecut_recut _ _ _

private theorem second_bottom_eq_first_bottom
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left) :
    D.second.bottom = D.first.bottom := by
  rw [GridRectangleBetween.bottom_def, ← hcommon, D.first.map_right,
    GridRectangleBetween.bottom_def]

/-- If the original rectangle in a mixed `right = left` overlap misses the turn row, the first
rectangle of the generic recut starts on the replaced grid line and contains the turn row. The
remaining equalities record the row geometry of this recut branch. -/
theorem rightLeftRecut_geometry
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    let E := D.rightLeftRecut hcommon hother hfirst hsecond
    E.middle = x.swapRows D.first.top D.second.top ∧
      E.first.left = D.second.left ∧
        E.first.bottom = D.first.top ∧ E.first.top = D.second.top ∧
          E.second.bottom = D.first.bottom ∧ E.second.top = D.first.top ∧
            s ∈ Grid.cIco E.first.bottom E.first.top := by
  let E := D.rightLeftRecut hcommon hother hfirst hsecond
  have hdata := D.isRecutOfRightEqLeft_recut hcommon
    (D.hasOneCommonSide_of_right_eq_left hcommon hother)
    hfirst (D.underlying_second_isEmpty hsecond)
  have hturnWhole : s ∈ Grid.cIco D.first.bottom D.second.top := by
    simpa only [D.second_bottom_eq_first_bottom hcommon] using D.second_turn_mem
  rcases hdata.recut_branch with hbranch | hbranch
  · have hfirstLeft : E.first.left = D.second.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def]
      simp only [E, rightLeftRecut, hbranch.2.2.1, ← hcommon,
        GridRectangleBetween.top_def]
    have hfirstBottom : E.first.bottom = D.first.top := by
      simpa only [E, rightLeftRecut] using hbranch.2.2.1
    have hfirstTop : E.first.top = D.second.top := by
      simpa only [E, rightLeftRecut] using hdata.recut_sides.1
    have hsecondTop : E.second.top = D.first.top := by
      simpa only [E, rightLeftRecut] using hdata.recut_sides.2
    have hturnParts :
        s ∈ Grid.cIco D.first.bottom D.first.top ∪
          Grid.cIco D.first.top D.second.top := by
      rw [Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hbranch.1]
      exact hturnWhole
    have hturnFirst : s ∈ Grid.cIco E.first.bottom E.first.top := by
      rw [Finset.mem_union] at hturnParts
      rcases hturnParts with hleft | hright
      · exact (hturn hleft).elim
      · rw [hfirstBottom, hfirstTop]
        exact hright
    exact ⟨hbranch.2.1, hfirstLeft, hbranch.2.2.1, hfirstTop,
      hbranch.2.2.2, hsecondTop, hturnFirst⟩
  · have : s ∈ Grid.cIco D.first.bottom D.first.top :=
      Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hturnWhole hbranch.1
    exact (hturn this).elim

/-- The first rectangle of the generic recut starts on the initial side of the original
pentagon. -/
@[simp]
theorem rightLeftRecut_first_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    (D.rightLeftRecut hcommon hother hfirst hsecond).first.left = D.second.left := by
  obtain ⟨_, hleft, _⟩ :=
    D.rightLeftRecut_geometry hcommon hother hfirst hsecond hturn
  exact hleft

/-- The first rectangle of the generic recut contains the turn row. -/
theorem rightLeftRecut_first_turn_mem
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    s ∈ Grid.cIco (D.rightLeftRecut hcommon hother hfirst hsecond).first.bottom
      (D.rightLeftRecut hcommon hother hfirst hsecond).first.top := by
  obtain ⟨_, _, _, _, _, _, hturn'⟩ :=
    D.rightLeftRecut_geometry hcommon hother hfirst hsecond hturn
  exact hturn'

/-- Promote the first generic recut rectangle to an initial-side pentagon. This is the recut of
a mixed `right = left` overlap outside the turn-point-cut family. -/
noncomputable def recutRightEqLeft
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridRectangleDecomposition := D.rightLeftRecut hcommon hother hfirst hsecond
  first_left_eq := (D.rightLeftRecut_first_left hcommon hother hfirst hsecond hturn).trans
    D.second_left_eq
  first_turn_mem := D.rightLeftRecut_first_turn_mem hcommon hother hfirst hsecond hturn

/-- Forgetting the promoted pentagon gives the generic recut. -/
@[simp]
theorem recutRightEqLeft_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    (D.recutRightEqLeft hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition =
      D.rightLeftRecut hcommon hother hfirst hsecond :=
  (rfl)

end TauCeti.GridRectangleInitialPentagonDecomposition
