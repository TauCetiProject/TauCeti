/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import TauCeti.KnotTheory.Grid.Rectangle

/-!
# Fully blocked empty rectangles in grid diagrams

This file packages the finite rectangle counts used by the fully blocked grid differential.
For grid states `x` and `y`, the already-defined `GridRectangleBetween x y` records an
oriented toroidal rectangle from `x` to `y`. Here we filter the generic empty-rectangle
enumeration to rectangles whose interiors avoid all `O` and `X` markings of a grid diagram.

The final count is valued in `ZMod 2`, matching the first coefficient system used in the grid
homology roadmap.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedRectangles`: empty rectangles avoiding all markings.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount`: the corresponding count in `ZMod 2`.

## References

This supplies a prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.3, "The complexes and `∂² = 0`",
where the fully blocked grid complex over `𝔽₂` counts rectangles avoiding all markings. The
objects and terminology follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (x y : GridState n)

/-- The finite set of fully blocked empty rectangles from `x` to `y` in a grid diagram.

"Fully blocked" means that the rectangle is empty for the source grid state and its interior
avoids every `O` and `X` marking. This is the rectangle set whose parity gives the coefficient
of `y` in the fully blocked grid differential applied to `x`. -/
noncomputable def fullyBlockedRectangles : Finset (GridRectangleBetween x y) := by
  classical
  exact (GridRectangleBetween.emptyRectangles x y).filter fun R => R.AvoidsMarkings G

/-- Membership in the fully blocked rectangle set is emptiness together with marking
avoidance. -/
@[simp]
theorem mem_fullyBlockedRectangles (R : GridRectangleBetween x y) :
    R ∈ G.fullyBlockedRectangles x y ↔ R.IsEmpty ∧ R.AvoidsMarkings G := by
  classical
  simp [fullyBlockedRectangles]

/-- Every fully blocked rectangle is empty. -/
theorem isEmpty_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.IsEmpty :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.1

/-- Every fully blocked rectangle avoids the `O` and `X` markings. -/
theorem avoidsMarkings_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.AvoidsMarkings G :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.2

/-- Fully blocked rectangles are a subset of the empty rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_emptyRectangles :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.emptyRectangles x y := by
  classical
  intro R hR
  exact (GridRectangleBetween.mem_emptyRectangles R).mpr
    ((G.mem_fullyBlockedRectangles x y R).mp hR |>.1)

/-- Fully blocked rectangles are a subset of all rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_all :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.all x y :=
  G.fullyBlockedRectangles_subset_emptyRectangles x y |>.trans
    (GridRectangleBetween.emptyRectangles_subset_all x y)

/-- The number of fully blocked empty rectangles from `x` to `y`, reduced modulo `2`. -/
noncomputable def fullyBlockedRectangleCount : ZMod 2 :=
  (G.fullyBlockedRectangles x y).card

/-- The fully blocked rectangle count is the cardinality of `fullyBlockedRectangles`, coerced
to `ZMod 2`. -/
theorem fullyBlockedRectangleCount_def :
    G.fullyBlockedRectangleCount x y = ((G.fullyBlockedRectangles x y).card : ZMod 2) :=
  rfl

/-- The set of fully blocked rectangles from a grid state to itself is empty. -/
@[simp]
theorem fullyBlockedRectangles_self (x : GridState n) : G.fullyBlockedRectangles x x = ∅ := by
  classical
  simp [fullyBlockedRectangles]

/-- The fully blocked rectangle count from a grid state to itself is zero. -/
@[simp]
theorem fullyBlockedRectangleCount_self (x : GridState n) :
    G.fullyBlockedRectangleCount x x = 0 := by
  simp [fullyBlockedRectangleCount]

end GridDiagram

end TauCeti
