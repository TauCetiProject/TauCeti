/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Stabilization.Basic

/-!
# Rectangles under grid-point insertion

This file transports an oriented rectangle between grid states along the insertion of a common
point into its source and target. It characterizes the sides and covered squares of the transported
rectangle, proves that transport is a bijection onto the rectangles between states containing the
inserted point, and compares emptiness before and after transport.

## Main definitions

* `TauCeti.GridRectangleBetween.insertPoint`: an oriented rectangle between two grid states,
  transported to the states obtained by inserting one point.

## Main results

* `TauCeti.GridRectangleBetween.exists_insertPoint_eq`: every rectangle between two states with
  a common inserted point is transported from the smaller grid.
* `TauCeti.GridRectangleBetween.succAbove_mem_coveredSquares_insertPoint`: transport preserves
  membership of embedded squares in the covered region.
* `TauCeti.GridRectangleBetween.mem_coveredSquares_insertPoint_succ_succ`: covered-square
  membership for insertion immediately after specified coordinates is detected by collapsing
  those coordinates with `Fin.predAbove`.
* `TauCeti.GridRectangleBetween.isEmpty_insertPoint_iff`: a transported rectangle is empty
  exactly when the original one is and the inserted point is not in its interior.

## References

The rectangle-transport organization adapts the formalization pattern used in
`TauCeti/KnotTheory/Grid/Differential/CyclicPermutation.lean` to point insertion.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- An oriented rectangle from `x` to `y`, transported to the states obtained from `x` and `y`
by inserting the point `(p, q)`. Its side columns are the embedded side columns. -/
def insertPoint (R : GridRectangleBetween x y) (p q : Fin (n + 1)) :
    GridRectangleBetween (x.insertPoint p q) (y.insertPoint p q) where
  left := p.succAbove R.left
  right := p.succAbove R.right
  left_ne_right := p.succAbove_right_injective.ne R.left_ne_right
  map_left := by simp [R.map_left]
  map_right := by simp [R.map_right]
  map_of_ne c := by
    induction c using Fin.succAboveCases p with
    | x => simp
    | p c =>
      intro hl hr
      simp only [GridState.insertPoint_apply_succAbove]
      rw [R.map_of_ne c (fun h => hl (h ▸ rfl)) fun h => hr (h ▸ rfl)]

variable (R : GridRectangleBetween x y) (p q : Fin (n + 1))

/-- The initial side of a transported rectangle is the embedded initial side. -/
@[simp]
theorem insertPoint_left : (R.insertPoint p q).left = p.succAbove R.left :=
  (rfl)

/-- The terminal side of a transported rectangle is the embedded terminal side. -/
@[simp]
theorem insertPoint_right : (R.insertPoint p q).right = p.succAbove R.right :=
  (rfl)

/-- The bottom row of a transported rectangle is the embedded bottom row. -/
@[simp]
theorem insertPoint_bottom : (R.insertPoint p q).bottom = q.succAbove R.bottom := by
  simp [bottom_def]

/-- The top row of a transported rectangle is the embedded top row. -/
@[simp]
theorem insertPoint_top : (R.insertPoint p q).top = q.succAbove R.top := by
  simp [top_def]

/-- Transporting rectangles along an inserted point is injective. -/
theorem insertPoint_injective :
    Function.Injective fun R : GridRectangleBetween x y => R.insertPoint p q := by
  intro R S h
  have hl := congrArg GridRectangleBetween.left h
  have hr := congrArg GridRectangleBetween.right h
  simp only [insertPoint_left, insertPoint_right] at hl hr
  exact sidePair_injective (Prod.ext (p.succAbove_right_injective hl)
    (p.succAbove_right_injective hr))

variable {p q} in
/-- Every rectangle between two states containing the same inserted point is transported from a
rectangle of the smaller grid. The inserted column is not a side column, since both states use
the inserted row there. -/
theorem exists_insertPoint_eq
    (S : GridRectangleBetween (x.insertPoint p q) (y.insertPoint p q)) :
    ∃ R : GridRectangleBetween x y, R.insertPoint p q = S := by
  have hleft : S.left ≠ p := by
    intro h
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (h ▸ S.left_ne_right.symm)
    have hmap := S.map_left
    rw [h, GridState.insertPoint_apply_newColumn, ← hr,
      GridState.insertPoint_apply_succAbove] at hmap
    exact q.succAbove_ne _ hmap.symm
  have hright : S.right ≠ p := by
    intro h
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (h ▸ S.left_ne_right)
    have hmap := S.map_right
    rw [h, GridState.insertPoint_apply_newColumn, ← hl,
      GridState.insertPoint_apply_succAbove] at hmap
    exact q.succAbove_ne _ hmap.symm
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hleft
  obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hright
  refine ⟨⟨l, r, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro rfl
    exact S.left_ne_right (hl.symm.trans hr)
  · apply q.succAbove_right_injective
    simpa [← hl, ← hr] using S.map_left
  · apply q.succAbove_right_injective
    simpa [← hl, ← hr] using S.map_right
  · intro c hcl hcr
    apply q.succAbove_right_injective
    simpa using S.map_of_ne (p.succAbove c) (hl ▸ p.succAbove_right_injective.ne hcl)
      (hr ▸ p.succAbove_right_injective.ne hcr)
  · exact sidePair_injective (Prod.ext hl hr)

/-- A transported rectangle covers the embedded image of a square exactly when the original
rectangle covers that square. -/
theorem succAbove_mem_coveredSquares_insertPoint (c r : Fin n) :
    (p.succAbove c, q.succAbove r) ∈ (R.insertPoint p q).toGridRectangle.coveredSquares ↔
      (c, r) ∈ R.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, Grid.succAbove_mem_cIco_succAbove_succAbove]

/-- When the point is inserted immediately after the column `i` and the row `j`, a square of
the larger grid is covered by a transported rectangle exactly when its collapse under
`Fin.predAbove` is covered by the original rectangle. -/
theorem mem_coveredSquares_insertPoint_succ_succ (i j : Fin n) (a : Fin (n + 1) × Fin (n + 1)) :
    a ∈ (R.insertPoint i.succ j.succ).toGridRectangle.coveredSquares ↔
      (i.predAbove a.1, j.predAbove a.2) ∈ R.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, Grid.mem_cIco_succ_succAbove_succ_succAbove_iff]

/-- A transported rectangle is empty exactly when the original rectangle is empty and the
inserted point does not lie in the interior of the transported rectangle. -/
@[simp]
theorem isEmpty_insertPoint_iff :
    (R.insertPoint p q).IsEmpty ↔
      R.IsEmpty ∧ (p, q) ∉ (R.insertPoint p q).toGridRectangle.interior := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo,
    Fin.forall_iff_succAbove p, and_comm]
  simp only [GridRectangle.mem_interior, GridRectangle.mem_columnInterior,
    GridRectangle.mem_rowInterior, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, GridState.insertPoint_apply_newColumn,
    GridState.insertPoint_apply_succAbove, Grid.succAbove_mem_cIoo_succAbove_succAbove, not_and]

end GridRectangleBetween

end TauCeti
