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

## Main results

* `TauCeti.GridRectangleBetween.avoidsMarkings_unknot_iff`: marking avoidance in the standard
  unknot grid of any size.

## References

The diagram and rectangle conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState (n + 2)}

/-- A rectangle of the standard unknot grid avoids the markings exactly when, for every column
it covers, neither the diagonal row of that column nor the row above it is covered. -/
theorem avoidsMarkings_unknot_iff (R : GridRectangleBetween x y) :
    R.AvoidsMarkings (GridDiagram.unknot n) ↔
      ∀ c ∈ Grid.cIco R.left R.right,
        c ∉ Grid.cIco (x R.left) (x R.right) ∧ c + 1 ∉ Grid.cIco (x R.left) (x R.right) := by
  simp only [R.avoidsMarkings_iff_forall, GridRectangle.mem_columnSquares,
    GridRectangle.mem_rowSquares, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, bottom_def, top_def,
    GridDiagram.unknot_O_apply, GridDiagram.unknot_X_apply_eq_add_one]

end GridRectangleBetween

end TauCeti
