/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapInvolution

/-!
# Turn-row transports for the terminal-side recut

This file discharges the `hturn` hypotheses in
`OverlapRight.recutRightEqRightFirst`/`recutRightEqRightSecond`: when the rectangle and
pentagon share their terminal side, the turn row `s` lies in the row span of whichever
recut rectangle inherits the pentagon's terminal side.

The proof mirrors `turn_mem_recut_first_of_left_eq_left` in `Overlap.lean` (the
common-initial-side case), using `cyclicOrder_of_isEmpty_of_right_eq_right` for the row
cyclic order and the forced branch data from `OverlapInvolution`
(`first_terminal_recut_branch_data` / `second_terminal_recut_branch_data`).

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.turn_mem_recut_first_of_right_eq_right`:
  the turn row lies in the first recut rectangle's row span when it carries the pentagon's
  terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.turn_mem_recut_second_of_right_eq_right`:
  the turn row lies in the second recut rectangle's row span when it carries the pentagon's
  terminal side.

The shared reasoning — the second rectangle's corner rows, the pentagon's turn-row
membership, and the cyclic-order interval nesting — is factored into private lemmas below
so the two transports do not duplicate it.
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

/-- The second rectangle's bottom corner row is `x` applied to its left side: the middle
state agrees with `x` there since that column is neither swapped column. -/
private theorem toRectangleDecomposition_second_bottom
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide) :
    D.toRectangleDecomposition.second.bottom = x D.toRectangleDecomposition.second.left := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hleft := D.left_ne_left_of_right_eq_right hcommon hone
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

/-- The second rectangle's top corner row is `x` applied to the first rectangle's left side:
the middle state agrees with `x` on the common right side via `map_right`. -/
private theorem toRectangleDecomposition_second_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) :
    D.toRectangleDecomposition.second.top = x D.toRectangleDecomposition.first.left := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  -- D.second.top = D.middle D.second.right = D.middle D.first.right
  -- = x D.first.left via D.first.map_right.
  have htop : D.toRectangleDecomposition.middle D.toRectangleDecomposition.second.right =
      x D.toRectangleDecomposition.first.left := by
    rw [← hcommon']
    exact D.toRectangleDecomposition.first.map_right
  simpa only [toRectangleDecomposition_middle, GridRectangleBetween.top_def] using htop

/-- The pentagon's turn row lies in the second rectangle's row span. -/
private theorem turn_mem_second_row_span
    (D : GridRectanglePentagonDecomposition a s x z) :
    s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
  simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def,
    GridRectangleBetween.top_def,
    toRectangleDecomposition_second_left, toRectangleDecomposition_second_right] using
    D.pentagon.turn_mem

/-- The turn row transfers into the corner-row row span: in the common-terminal-side
overlap, `s` lies in `cIco (x D.second.left) (x D.first.right)`.

The pentagon's turn row lies in the second rectangle's row span; the cyclic row order
forced by emptiness nests the second rectangle's top corner row strictly inside the
interval from the second rectangle's bottom corner row to the first rectangle's top
corner row, so interval nesting extends the membership. -/
private theorem turn_mem_row_span_of_terminal_side
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    s ∈ Grid.cIco (x D.toRectangleDecomposition.second.left)
      (x D.toRectangleDecomposition.first.right) := by
  have hsecondBottom := D.toRectangleDecomposition_second_bottom hcommon hone
  have hsecondTop := D.toRectangleDecomposition_second_top hcommon
  have hturn := D.turn_mem_second_row_span
  -- The cyclic row order in corner-row form:
  -- x D.first.left ∈ cIoo (x D.second.left) (x D.first.right).
  have hrow' : x D.toRectangleDecomposition.first.left ∈
      Grid.cIoo (x D.toRectangleDecomposition.second.left)
        (x D.toRectangleDecomposition.first.right) := by
    have hcommon' : D.toRectangleDecomposition.first.right =
        D.toRectangleDecomposition.second.right := by
      simpa only [toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right] using hcommon
    have hleft := D.left_ne_left_of_right_eq_right hcommon hone
    have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
        D.toRectangleDecomposition.second.IsEmpty :=
      ⟨by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
        by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
    have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_right
      hcommon' hleft hempty.1 hempty.2).2
    have hfirstBottom : D.toRectangleDecomposition.first.bottom =
        x D.toRectangleDecomposition.first.left :=
      D.toRectangleDecomposition.first.bottom_def
    have hfirstTop : D.toRectangleDecomposition.first.top =
        x D.toRectangleDecomposition.first.right :=
      D.toRectangleDecomposition.first.top_def
    simpa only [hfirstBottom, hfirstTop, hsecondBottom] using hrow
  have hmem : s ∈ Grid.cIco (x D.toRectangleDecomposition.second.left)
      (x D.toRectangleDecomposition.first.left) := by
    simpa only [hsecondBottom, hsecondTop] using hturn
  exact Grid.cIco_subset_cIco_of_mem_cIco hmem hrow'

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
  -- The forced branch data: the first recut rectangle spans from the original second
  -- rectangle's left side to the original first rectangle's right side.
  obtain ⟨-, hEfirst_right, hEfirst_left⟩ :=
    D.first_terminal_recut_branch_data hcommon hone hrectangle hpentagon hfirst
  -- The turn row lies in the corner-row row span.
  have hturn := D.turn_mem_row_span_of_terminal_side hcommon hone hrectangle hpentagon
  -- E.first.bottom = x E.first.left and E.first.top = x E.first.right by rfl
  -- (bottom_def/top_def), then the forced side equations.
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
      _ = x D.toRectangleDecomposition.first.right := by rw [hEfirst_right]
  rw [hEfirst_bottom, hEfirst_top]
  exact hturn

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
  -- The forced branch data: the second recut rectangle spans from the original first
  -- rectangle's left side to the original first rectangle's right side, with the
  -- column-swapped middle state.
  obtain ⟨-, hEsecond_right, hEsecond_left, hmiddle_eq⟩ :=
    D.second_terminal_recut_branch_data hcommon hone hrectangle hpentagon hsecond
  -- The turn row lies in the corner-row row span.
  have hturn := D.turn_mem_row_span_of_terminal_side hcommon hone hrectangle hpentagon
  have hsecondBottom := D.toRectangleDecomposition_second_bottom hcommon hone
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  -- E.second.bottom = E.middle E.second.left = x D.second.left = D.second.bottom.
  have hEbottom : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.bottom = D.toRectangleDecomposition.second.bottom := by
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
      rw [hmiddle_eq, GridState.swapColumns_apply, Equiv.swap_apply_right]
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
  -- E.second.top = E.middle E.second.right = x D.first.right = D.first.top.
  have hEtop : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second.top = D.toRectangleDecomposition.first.top := by
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
      rw [hmiddle_eq, GridState.swapColumns_apply,
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
        rw [hEsecond_right]
      _ = x D.toRectangleDecomposition.first.right := hmid_eval
      _ = D.toRectangleDecomposition.first.top :=
        D.toRectangleDecomposition.first.top_def.symm
  rw [hEbottom, hEtop, hsecondBottom, D.toRectangleDecomposition.first.top_def]
  exact hturn

end GridRectanglePentagonDecomposition

end TauCeti
