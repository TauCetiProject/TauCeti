/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapRight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapInvolution
public import TauCeti.KnotTheory.Grid.Commutation.OverlapCounted

/-!
# Turn-row transports for the terminal-side recut

This file discharges the `hturn` hypotheses in
`OverlapRight.recutRightEqRight_first`/`_second`: when the rectangle and pentagon share
their terminal side, the turn row `s` lies in the row span of whichever recut rectangle
inherits the pentagon's terminal side.

The proof mirrors `turn_mem_recut_first_of_left_eq_left` in `Overlap.lean` (the
common-initial-side case), using `cyclicOrder_of_isEmpty_of_right_eq_right` for the row
cyclic order and the branch equations from `IsRecutOfRightEqRight.recut_branch`.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.turn_mem_recut_first_of_right_eq_right`:
  the turn row lies in the first recut rectangle's row span when it carries the pentagon's
  terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.turn_mem_recut_second_of_right_eq_right`:
  the turn row lies in the second recut rectangle's row span when it carries the pentagon's
  terminal side.

Roadmap: CombinatorialHeegaardFloer
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The two rectangles have different initial sides when they share their terminal side
and have exactly one common side. -/
private theorem left_ne_left_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide) :
    D.toRectangleDecomposition.first.left ≠ D.toRectangleDecomposition.second.left := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  rcases D.toRectangleDecomposition.side_eq_cases_of_hasOneCommonSide hone with
    ⟨_, hne⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · -- first.right ≠ second.right: contradicts hcommon'.
    exact absurd hcommon' hne
  · -- first.left = second.right: with hcommon', first.left = first.right.
    exfalso
    exact D.toRectangleDecomposition.first.left_ne_right (h.trans hcommon'.symm)
  · -- first.right = second.left: with hcommon', second.left = second.right.
    exfalso
    exact D.toRectangleDecomposition.second.left_ne_right (h.symm.trans hcommon')
  · exact h

/-- In the common-terminal-side overlap, the first rectangle of the recut still contains the
pentagon's turn row in its row span, when it carries the pentagon's terminal side. -/
theorem turn_mem_recut_first_of_right_eq_right
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
    s ∈ Grid.cIco
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.bottom
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.top := by
  -- Work in the forgotten rectangle decomposition.
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hleft := D.left_ne_left_of_right_eq_right hcommon hone
  -- The cyclic row order: first.bottom ∈ cIoo second.bottom first.top.
  have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_right
    hcommon' hleft hempty.1 hempty.2).2
  -- The pentagon's turn row lies in the second rectangle's row span.
  have hturn : s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
    simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right] using
      D.pentagon.turn_mem
  -- The recut branch is forced by hfirst: E.first.right = D.pentagon.right = D.first.right,
  -- so we are in Branch B (E.first.right = D.first.right).
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨-, -, hEfirst, -⟩ | ⟨hcolB, hmiddleB, hEfirstB, -⟩
  · -- Branch A: E.first.right = D.first.left, so D.first.left = D.pentagon.right
    -- = D.first.right, contradicting left_ne_right.
    exfalso
    rw [hEfirst, hpen_right] at hfirst
    exact D.toRectangleDecomposition.first.left_ne_right hfirst
  · -- Branch B: E.first has the same row span as the original pentagon's underlying
    -- rectangle, up to the cyclic interval nesting.
    -- E.first.bottom = x E.first.left = x D.second.left
    -- E.first.top = x E.first.right = x D.first.right
    have hEfirst_left : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.left = D.toRectangleDecomposition.second.left :=
      hdata.recut_sides.1
    -- Express the row intervals via corner rows.
    -- D.second.bottom = x D.second.left, D.second.top = x D.first.left.
    -- D.second : GridRectangleBetween D.middle z, and D.middle agrees with x on
    -- D.second.left (not a swapped column, by the Branch B column facts).
    have hsecondBottom : D.toRectangleDecomposition.second.bottom =
        x D.toRectangleDecomposition.second.left := by
      have hne1 : D.toRectangleDecomposition.second.left ≠
          D.toRectangleDecomposition.first.left := hleft.symm
      have hne2 : D.toRectangleDecomposition.second.left ≠
          D.toRectangleDecomposition.first.right := by
        intro h
        exact D.toRectangleDecomposition.second.left_ne_right
          (h.trans hcommon')
      -- D.second.bottom = D.middle D.second.left = x D.second.left
      -- via D.first.map_of_ne (D.first : GridRectangleBetween x D.middle).
      have hmid : D.toRectangleDecomposition.middle D.toRectangleDecomposition.second.left =
          x D.toRectangleDecomposition.second.left :=
        D.toRectangleDecomposition.first.map_of_ne _ hne1 hne2
      simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def] using hmid
    have hsecondTop : D.toRectangleDecomposition.second.top =
        x D.toRectangleDecomposition.first.left := by
      -- D.second.top = D.middle D.second.right = D.middle D.first.right
      -- = x D.first.left via D.first.map_right.
      have htop : D.toRectangleDecomposition.middle D.toRectangleDecomposition.second.right =
          x D.toRectangleDecomposition.first.left := by
        rw [← hcommon']
        exact D.toRectangleDecomposition.first.map_right
      simpa only [toRectangleDecomposition_middle, GridRectangleBetween.top_def] using htop
    -- The cyclic row order in corner-row form:
    -- x D.first.left ∈ cIoo (x D.second.left) (x D.first.right).
    have hrow' : x D.toRectangleDecomposition.first.left ∈
        Grid.cIoo (x D.toRectangleDecomposition.second.left)
          (x D.toRectangleDecomposition.first.right) := by
      have hfirstBottom : D.toRectangleDecomposition.first.bottom =
          x D.toRectangleDecomposition.first.left :=
        D.toRectangleDecomposition.first.bottom_def
      have hfirstTop : D.toRectangleDecomposition.first.top =
          x D.toRectangleDecomposition.first.right :=
        D.toRectangleDecomposition.first.top_def
      simpa only [hfirstBottom, hfirstTop, hsecondBottom] using hrow
    -- Transfer s from cIco (x D.second.left) (x D.first.left) to
    -- cIco (x D.second.left) (x D.first.right) via interval nesting.
    have hturn' : s ∈ Grid.cIco (x D.toRectangleDecomposition.second.left)
        (x D.toRectangleDecomposition.first.right) := by
      have hmem : s ∈ Grid.cIco (x D.toRectangleDecomposition.second.left)
          (x D.toRectangleDecomposition.first.left) := by
        simpa only [hsecondBottom, hsecondTop] using hturn
      exact Grid.cIco_subset_cIco_of_mem_cIco hmem hrow'
    -- E.first.bottom = x D.second.left, E.first.top = x D.first.right.
    -- E.first : GridRectangleBetween x E.middle, so bottom_def/top_def are rfl.
    have hgoal : s ∈ Grid.cIco (x D.toRectangleDecomposition.second.left)
        (x D.toRectangleDecomposition.first.right) := hturn'
    have hEfirst_bottom : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.bottom = x D.toRectangleDecomposition.second.left := by
      calc (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).first.bottom
          = x (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).first.left := rfl
        _ = x D.toRectangleDecomposition.second.left := by rw [hEfirst_left]
    have hEfirst_top : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first.top = x D.toRectangleDecomposition.first.right := by
      calc (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).first.top
          = x (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).first.right := rfl
        _ = x D.toRectangleDecomposition.first.right := by rw [hEfirstB]
    rw [hEfirst_bottom, hEfirst_top]
    exact hgoal

/-- In the common-terminal-side overlap, the second rectangle of the recut still contains the
pentagon's turn row in its row span, when it carries the pentagon's terminal side. -/
theorem turn_mem_recut_second_of_right_eq_right
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
    s ∈ Grid.cIco
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.bottom
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.top := by
  -- Work in the forgotten rectangle decomposition.
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hleft := D.left_ne_left_of_right_eq_right hcommon hone
  -- The cyclic row order: first.bottom ∈ cIoo second.bottom first.top.
  have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_right
    hcommon' hleft hempty.1 hempty.2).2
  -- The pentagon's turn row lies in the second rectangle's row span.
  have hturn : s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
    simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right] using
      D.pentagon.turn_mem
  -- The recut branch is forced by hsecond: E.second.right = D.pentagon.right
  -- = D.first.right, so we are in Branch A (E.second.right = D.first.right).
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨hcolA, hmiddleA, -, hEsecondA⟩ | ⟨-, -, -, hEsecondB⟩
  · -- Branch A: E.second.left = D.first.left, E.second.right = D.first.right.
    -- E.second.bottom = E.middle E.second.left = x D.second.left
    -- E.second.top = E.middle E.second.right = x D.first.right
    have hEsecond_left : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.left = D.toRectangleDecomposition.first.left :=
      hdata.recut_sides.2
    -- D.second.bottom = x D.second.left, D.second.top = x D.first.left.
    -- (Same computation as in the first theorem; the Branch A column facts give the
    -- needed inequalities via hleft.)
    have hsecondBottom : D.toRectangleDecomposition.second.bottom =
        x D.toRectangleDecomposition.second.left := by
      have hne1 : D.toRectangleDecomposition.second.left ≠
          D.toRectangleDecomposition.first.left := hleft.symm
      have hne2 : D.toRectangleDecomposition.second.left ≠
          D.toRectangleDecomposition.first.right := by
        intro h
        exact D.toRectangleDecomposition.second.left_ne_right
          (h.trans hcommon')
      have hmid : D.toRectangleDecomposition.middle D.toRectangleDecomposition.second.left =
          x D.toRectangleDecomposition.second.left :=
        D.toRectangleDecomposition.first.map_of_ne _ hne1 hne2
      simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def] using hmid
    have hsecondTop : D.toRectangleDecomposition.second.top =
        x D.toRectangleDecomposition.first.left := by
      have htop : D.toRectangleDecomposition.middle D.toRectangleDecomposition.second.right =
          x D.toRectangleDecomposition.first.left := by
        rw [← hcommon']
        exact D.toRectangleDecomposition.first.map_right
      simpa only [toRectangleDecomposition_middle, GridRectangleBetween.top_def] using htop
    -- The cyclic row order gives D.second.top ∈ cIoo D.second.bottom D.first.top.
    have htop_mem : D.toRectangleDecomposition.second.top ∈
        Grid.cIoo D.toRectangleDecomposition.second.bottom
          D.toRectangleDecomposition.first.top := by
      have hfirstTop : D.toRectangleDecomposition.first.top =
          x D.toRectangleDecomposition.first.right :=
        D.toRectangleDecomposition.first.top_def
      rw [hsecondTop, hsecondBottom, hfirstTop]
      have hfirstBottom : D.toRectangleDecomposition.first.bottom =
          x D.toRectangleDecomposition.first.left :=
        D.toRectangleDecomposition.first.bottom_def
      simpa only [hfirstBottom, hsecondBottom, hfirstTop] using hrow
    -- Transfer s from cIco D.second.bottom D.second.top to
    -- cIco D.second.bottom D.first.top via interval nesting.
    have hturn' : s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
        D.toRectangleDecomposition.first.top :=
      Grid.cIco_subset_cIco_of_mem_cIco hturn htop_mem
    -- E.second.bottom = D.second.bottom, E.second.top = D.first.top.
    -- We prove the middle-state evaluations separately to avoid dependent rewrites.
    have hEbottom : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.bottom = D.toRectangleDecomposition.second.bottom := by
      -- E.second.bottom = E.middle E.second.left (bottom_def is rfl).
      -- E.second.left = D.first.left, E.middle D.first.left = x D.second.left.
      have hmid_eval : (D.toRectangleDecomposition.recut hone
          (by
            simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
              D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
          (by
            simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
              D.toRectangleDecomposition_middle,
              D.toRectangleDecomposition_second_toGridRectangle] using
            hpentagon)).middle D.toRectangleDecomposition.first.left =
          x D.toRectangleDecomposition.second.left := by
        rw [hmiddleA, GridState.swapColumns_apply, Equiv.swap_apply_right]
      calc (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).second.bottom
          = (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).middle
            (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).second.left := rfl
        _ = (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).middle D.toRectangleDecomposition.first.left := by
          rw [hEsecond_left]
        _ = x D.toRectangleDecomposition.second.left := hmid_eval
        _ = D.toRectangleDecomposition.second.bottom := hsecondBottom.symm
    have hEtop : (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.top = D.toRectangleDecomposition.first.top := by
      -- E.second.top = E.middle E.second.right (top_def is rfl).
      -- E.second.right = D.first.right, E.middle D.first.right = x D.first.right.
      have hne1 : D.toRectangleDecomposition.first.right ≠
          D.toRectangleDecomposition.second.left := by
        intro h
        -- h : first.right = second.left, hcommon' : first.right = second.right,
        -- so second.left = second.right, contradiction.
        exact D.toRectangleDecomposition.second.left_ne_right
          (h.symm.trans hcommon')
      have hne2 : D.toRectangleDecomposition.first.right ≠
          D.toRectangleDecomposition.first.left :=
        fun h => D.toRectangleDecomposition.first.left_ne_right h.symm
      have hmid_eval : (D.toRectangleDecomposition.recut hone
          (by
            simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
              D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
          (by
            simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
              D.toRectangleDecomposition_middle,
              D.toRectangleDecomposition_second_toGridRectangle] using
            hpentagon)).middle D.toRectangleDecomposition.first.right =
          x D.toRectangleDecomposition.first.right := by
        rw [hmiddleA, GridState.swapColumns_apply,
          Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      calc (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).second.top
          = (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).middle
            (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).second.right := rfl
        _ = (D.toRectangleDecomposition.recut hone
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
            (by
              simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
                D.toRectangleDecomposition_middle,
                D.toRectangleDecomposition_second_toGridRectangle] using
              hpentagon)).middle D.toRectangleDecomposition.first.right := by
          rw [hEsecondA]
        _ = x D.toRectangleDecomposition.first.right := hmid_eval
        _ = D.toRectangleDecomposition.first.top :=
          D.toRectangleDecomposition.first.top_def.symm
    rw [hEbottom, hEtop]
    exact hturn'
  · -- Branch B: E.second.right = D.second.left, so D.second.left = D.pentagon.right
    -- = D.first.right = D.second.right (by hcommon'), contradicting left_ne_right.
    exfalso
    rw [hEsecondB, hpen_right, hcommon'] at hsecond
    exact D.toRectangleDecomposition.second.left_ne_right hsecond

end GridRectanglePentagonDecomposition

end TauCeti
