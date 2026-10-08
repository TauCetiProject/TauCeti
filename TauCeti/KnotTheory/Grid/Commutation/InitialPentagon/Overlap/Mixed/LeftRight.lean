/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Recutting an initial-side pentagon across a mixed common side

Consider a rectangle followed by a commutation pentagon turning on its initial side. This file
treats the mixed overlap in which the rectangle's initial side is the pentagon's terminal side.
The generic empty-rectangle recut always starts on the replaced grid line. If its first rectangle
contains the turn row, it promotes to an initial-side pentagon followed by a rectangle. Otherwise
the second recut rectangle also starts on the replaced line and contains the turn row, so it
promotes to a rectangle followed by an initial-side pentagon.

Thus every such mixed overlap stays among the two coefficient sums involving initial-side
pentagons. These two promoted recuts are the geometric input for cancelling this family in the
grid-commutation chain-map equation.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqRight_turn`: the turn row lies
  in the first recut rectangle, or it lies in the second and that rectangle starts on the
  replaced line.
* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqRightFirst` and
  `recutLeftEqRightSecond`: the two corresponding promoted recuts.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A mixed overlap whose rectangle initial side is the pentagon terminal side has exactly one
common side column. -/
theorem hasOneCommonSide_of_left_eq_right
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left) : D.HasOneCommonSide := by
  apply D.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.first.left, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, hcommon] at hc
    have hfirst := D.first.left_ne_right
    have hsecond := D.second.left_ne_right
    grind

private theorem underlying_first_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.first.IsEmpty) :
    D.toGridRectangleDecomposition.first.IsEmpty :=
  h

private theorem underlying_second_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.second.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at h ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using h

/-- The generic empty-rectangle recut of a mixed overlap whose first initial side is the second
terminal side. -/
noncomputable def leftRightRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    GridRectangleDecomposition x z :=
  D.recut (D.hasOneCommonSide_of_left_eq_right hcommon hother)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)

/-- The generic construction is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_leftRightRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    D.IsRecut (D.leftRightRecut hcommon hother hfirst hsecond) :=
  D.isRecut_recut _ _ _

private theorem second_bottom_eq
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left) :
    D.second.bottom = x D.second.left := by
  rw [GridRectangleBetween.bottom_def]
  exact D.first.map_of_ne D.second.left
    (fun h => D.second.left_ne_right (h.trans hcommon)) hother.symm

private theorem second_top_eq_first_top
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right) : D.second.top = D.first.top := by
  rw [GridRectangleBetween.top_def, hcommon.symm, GridRectangleBetween.top_def]
  exact D.first.map_left

/-- The first rectangle in the generic recut starts on the replaced grid line. -/
@[simp]
theorem leftRightRecut_first_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    (D.leftRightRecut hcommon hother hfirst hsecond).first.left = D.second.left := by
  let E := D.leftRightRecut hcommon hother hfirst hsecond
  have hdata := D.isRecutOfLeftEqRight_recut hcommon
    (D.hasOneCommonSide_of_left_eq_right hcommon hother)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
  have hbottom : E.first.bottom = D.second.bottom := by
    simpa only [E, leftRightRecut] using hdata.recut_sides.1
  apply x.toPerm.injective
  rw [← GridRectangleBetween.bottom_def, hbottom, D.second_bottom_eq hcommon hother]

/-- In a mixed `left = right` overlap, either the first recut rectangle contains the turn row,
or the second recut rectangle starts on the replaced line and contains the turn row. -/
theorem recutLeftEqRight_turn
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    let E := D.leftRightRecut hcommon hother hfirst hsecond
    (s ∈ Grid.cIco E.first.bottom E.first.top) ∨
      (E.second.left = D.second.left ∧ s ∈ Grid.cIco E.second.bottom E.second.top) := by
  let E := D.leftRightRecut hcommon hother hfirst hsecond
  by_cases hturn : s ∈ Grid.cIco E.first.bottom E.first.top
  · exact Or.inl hturn
  · right
    have hdata := D.isRecutOfLeftEqRight_recut hcommon
      (D.hasOneCommonSide_of_left_eq_right hcommon hother)
      (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
    have hfirstBottom : E.first.bottom = D.second.bottom := by
      simpa only [E, leftRightRecut] using hdata.recut_sides.1
    have hsecondBottom : E.second.bottom = D.first.bottom := by
      simpa only [E, leftRightRecut] using hdata.recut_sides.2
    rcases hdata.recut_branch with hbranch | hbranch
    · have hmiddle : E.middle = x.swapRows D.second.bottom D.first.bottom := by
        simpa only [E, leftRightRecut] using hbranch.2.1
      have hfirstTop : E.first.top = D.first.bottom := by
        simpa only [E, leftRightRecut] using hbranch.2.2.1
      have hsecondTop : E.second.top = D.first.top := by
        simpa only [E, leftRightRecut] using hbranch.2.2.2
      have hsecondLeft : E.second.left = D.second.left := by
        apply E.middle.toPerm.injective
        rw [← GridRectangleBetween.bottom_def, hsecondBottom, hmiddle,
          GridState.swapRows_apply, D.second_bottom_eq hcommon hother,
          Equiv.swap_apply_left]
      refine ⟨hsecondLeft, ?_⟩
      have hturnWhole : s ∈ Grid.cIco D.second.bottom D.first.top := by
        simpa only [D.second_top_eq_first_top hcommon] using D.second_turn_mem
      have hparts := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hbranch.1
      have hturnParts :
          s ∈ Grid.cIco D.second.bottom D.first.bottom ∪
            Grid.cIco D.first.bottom D.first.top := by
        rw [hparts]
        exact hturnWhole
      rw [Finset.mem_union] at hturnParts
      rcases hturnParts with hleft | hright
      · exact (hturn (by simpa only [hfirstBottom, hfirstTop] using hleft)).elim
      · rw [hsecondBottom, hsecondTop]
        exact hright
    · have hfirstTop : E.first.top = D.first.top := by
        simpa only [E, leftRightRecut] using hbranch.2.2.1
      have hturnWhole : s ∈ Grid.cIco D.second.bottom D.first.top := by
        simpa only [D.second_top_eq_first_top hcommon] using D.second_turn_mem
      exact (hturn (by simpa only [hfirstBottom, hfirstTop] using hturnWhole)).elim

/-- Promote the first generic recut rectangle to an initial-side pentagon when it contains the
turn row. -/
noncomputable def recutLeftEqRightFirst
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridRectangleDecomposition := D.leftRightRecut hcommon hother hfirst hsecond
  first_left_eq := (D.leftRightRecut_first_left hcommon hother hfirst hsecond).trans
    D.second_left_eq
  first_turn_mem := hturn

/-- Promote the second generic recut rectangle to an initial-side pentagon when the first does
not contain the turn row. -/
noncomputable def recutLeftEqRightSecond
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridRectangleDecomposition := D.leftRightRecut hcommon hother hfirst hsecond
  second_left_eq := (D.recutLeftEqRight_turn hcommon hother hfirst hsecond).resolve_left hturn |>.1
    |>.trans D.second_left_eq
  second_turn_mem :=
    (D.recutLeftEqRight_turn hcommon hother hfirst hsecond).resolve_left hturn |>.2

/-- Forgetting the first promoted pentagon gives the generic recut. -/
@[simp]
theorem recutLeftEqRightFirst_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    (D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition =
      D.leftRightRecut hcommon hother hfirst hsecond :=
  (rfl)

/-- Forgetting the second promoted pentagon gives the generic recut. -/
@[simp]
theorem recutLeftEqRightSecond_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    (D.recutLeftEqRightSecond hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition =
      D.leftRightRecut hcommon hother hfirst hsecond :=
  (rfl)

end TauCeti.GridRectangleInitialPentagonDecomposition
