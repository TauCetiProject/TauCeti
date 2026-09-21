/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Basic
public import TauCeti.KnotTheory.Grid.Unknot.Basic

/-!
# Rectangles in the standard unknot grid

This file characterizes when a rectangle in a standard unknot grid avoids all markings. Since the
`O` markings lie on the diagonal and the `X` markings one row above it, the condition can be read
off column by column.

In grid number three the characterization leaves no freedom at all: both the column arc and the
row arc must be single, the row arc must be the one row the column arc does not forbid, and the
source state is pinned down to the *subdiagonal* state `GridState.subdiagonal 3`, the only
diagonal state of a `3 × 3` grid carrying no marking.

## Main results

* `TauCeti.GridRectangle.avoidsMarkings_unknot_iff`: marking avoidance in the standard unknot
  grid of any size.
* `TauCeti.GridRectangleBetween.avoidsMarkings_unknot_one_iff`: in grid number three a rectangle
  avoids the markings exactly when it leaves the subdiagonal state through two cyclically
  consecutive columns.

## References

The diagram and rectangle conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ}

/-- A rectangle of the standard unknot grid avoids the markings exactly when, for every column
it covers, neither the diagonal row of that column nor the row above it is covered. -/
theorem avoidsMarkings_unknot_iff (R : GridRectangle (n + 2)) :
    R.AvoidsMarkings (GridDiagram.unknot n) ↔
      ∀ c ∈ Grid.cIco R.left R.right,
        c ∉ Grid.cIco R.bottom R.top ∧ c + 1 ∉ Grid.cIco R.bottom R.top := by
  simp only [R.avoidsMarkings_iff_forall, mem_columnSquares, mem_rowSquares,
    GridDiagram.unknot_O_apply, GridDiagram.unknot_X_apply_eq_add_one]

end GridRectangle

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState (n + 2)}

/-- A rectangle between states of the standard unknot grid avoids the markings exactly when, for
every column it covers, neither the diagonal row of that column nor the row above it is covered. -/
theorem avoidsMarkings_unknot_iff (R : GridRectangleBetween x y) :
    R.AvoidsMarkings (GridDiagram.unknot n) ↔
      ∀ c ∈ Grid.cIco R.left R.right,
        c ∉ Grid.cIco (x R.left) (x R.right) ∧ c + 1 ∉ Grid.cIco (x R.left) (x R.right) := by
  simpa only [toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
    toGridRectangle_top, bottom_def, top_def] using
      (R.avoidsMarkings_iff_forall (GridDiagram.unknot n)).trans
        ((R.toGridRectangle.avoidsMarkings_iff_forall (GridDiagram.unknot n)).symm.trans
          R.toGridRectangle.avoidsMarkings_unknot_iff)

end GridRectangleBetween

/-! ### Grid number three -/

/-- In three columns a half-open arc of columns `[l, r)` and the arc of rows the unknot markings
force it to avoid leave room for a nonempty row arc `[b, t)` only when `r = l + 1` and the row
arc is the single row `l + 2`. -/
private theorem unknot_one_sides : ∀ l r b t : Fin 3, l ≠ r → b ≠ t →
    (∀ c : Fin 3, c ∈ Grid.cIco l r → c ∉ Grid.cIco b t ∧ c + 1 ∉ Grid.cIco b t) →
    r = l + 1 ∧ b = l + 2 ∧ t = l := by
  simp only [Grid.mem_cIco]
  decide

/-- In three columns the single row below the diagonal of the column `l` is disjoint from the two
rows that the column `l` forces a rectangle to avoid. -/
private theorem unknot_one_avoids : ∀ l c : Fin 3, c ∈ Grid.cIco l (l + 1) →
    c ∉ Grid.cIco (l - 1) (l + 1 - 1) ∧ c + 1 ∉ Grid.cIco (l - 1) (l + 1 - 1) := by
  simp only [Grid.mem_cIco]
  decide

/-- Two consecutive values determine a three-column grid state with those values. -/
private theorem eq_subdiagonal_of_apply (x : GridState 3) (l : Fin 3)
    (h₁ : x l = l + 2) (h₂ : x (l + 1) = l) : x = GridState.subdiagonal 3 := by
  revert x l
  decide

namespace GridRectangleBetween

variable {x y : GridState 3}

/-- A rectangle of the `3 × 3` unknot grid avoids the markings exactly when it leaves the
subdiagonal state and its two side columns are cyclically consecutive. -/
theorem avoidsMarkings_unknot_one_iff (R : GridRectangleBetween x y) :
    R.AvoidsMarkings (GridDiagram.unknot 1) ↔
      x = GridState.subdiagonal 3 ∧ R.right = R.left + 1 := by
  rw [R.avoidsMarkings_unknot_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨hr, hb, ht⟩ := unknot_one_sides R.left R.right (x R.left) (x R.right)
      R.left_ne_right (fun e => R.left_ne_right (x.toPerm.injective e)) h
    have hsucc : x (R.left + 1) = R.left := by
      rw [← hr]
      exact ht
    exact ⟨eq_subdiagonal_of_apply x R.left hb hsucc, hr⟩
  · rintro ⟨rfl, hr⟩
    rw [hr, GridState.subdiagonal_apply_eq_sub_one, GridState.subdiagonal_apply_eq_sub_one]
    exact unknot_one_avoids R.left

end GridRectangleBetween

end TauCeti
