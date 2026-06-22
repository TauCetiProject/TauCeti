/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Gradings
import TauCeti.KnotTheory.Grid.RectangleSwap

/-!
# Grading changes across a rectangle move

This file records how the Maslov and Alexander gradings of two grid states differ, first as a
pure identity between the grading formulas of any two states, then localized to the four corners
of a rectangle move.

The two Maslov gradings split the same way: their difference is the change in the state's
`J`-self-pairing minus twice the change in the marking pairing,
`M_O(x) - M_O(y) = (J(x, x) - J(y, y)) - 2 (J_O(x) - J_O(y))`, and similarly for `M_X`. The
state-self-pairing term is identical in both Maslov gradings, so it cancels in the Alexander
grading, leaving the clean marking-only identity
`A(x) - A(y) = (J_X(x) - J_X(y)) - (J_O(x) - J_O(y))`. None of these three reductions needs any
relationship between `x` and `y`.

When `y` is obtained from `x` by a rectangle move `R : GridRectangleBetween x y`, the two states
share all but two of their occupied squares (`RectangleSwap.lean`), so each marking pairing
`J_O(x) - J_O(y)` collapses to a difference of four corner `J`-singletons: the source corners
`(left, bottom)`, `(right, top)` against the target corners `(left, top)`, `(right, bottom)`.
Feeding those corner formulas back into the Maslov and Alexander reductions expresses every
grading change across a rectangle move through the four corners and the markings, with the shared
part of the two states cancelling.

## Main results

* `TauCeti.GridDiagram.maslovO_sub`, `TauCeti.GridDiagram.maslovX_sub`: the difference of a
  Maslov grading at two states splits into the state self-pairing change and twice the marking
  pairing change.
* `TauCeti.GridDiagram.alexander_sub`: the Alexander grading change is the difference of the two
  marking pairing changes; the state self-pairing cancels.
* `TauCeti.GridDiagram.JO_sub_JO`, `TauCeti.GridDiagram.JX_sub_JX`: across a rectangle move the
  marking pairing change is a difference of four corner `J`-singletons.
* `TauCeti.GridDiagram.alexander_change_rectangle`,
  `TauCeti.GridDiagram.maslovO_change_rectangle`,
  `TauCeti.GridDiagram.maslovX_change_rectangle`: the grading changes across a rectangle move,
  localized to the four corners.

## References

This supplies the rectangle grading-change part of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2, "Gradings. The `J`-function,
`M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a rectangle." The
formulas follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4, where
the Maslov and Alexander grading changes across a rectangle are read off the markings it covers.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- Splitting a two-point insertion out of the left argument of the `J`-function. The two fresh
points contribute their singleton pairings and the rest is untouched; this is the bookkeeping a
corner-localized grading-change computation rests on. -/
private theorem J_insert_pair_left {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.J (insert a (insert b S)) P =
      GridPoint.J {a} P + GridPoint.J {b} P + GridPoint.J S P := by
  rw [GridPoint.J_insert_left hab, GridPoint.J_insert_left hb, add_assoc]

end GridPoint

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The difference of the `O`-Maslov grading at two grid states splits into the change in the
state self-pairing and twice the change in the `O`-marking pairing. The two states need not be
related: this is the algebraic shape of the grading formula. -/
theorem maslovO_sub (x y : GridState n) :
    G.maslovO x - G.maslovO y =
      (GridState.J x x - GridState.J y y) - 2 * (G.JO x - G.JO y) := by
  rw [maslovO_eq, maslovO_eq]
  ring

/-- The difference of the `X`-Maslov grading at two grid states splits into the change in the
state self-pairing and twice the change in the `X`-marking pairing. -/
theorem maslovX_sub (x y : GridState n) :
    G.maslovX x - G.maslovX y =
      (GridState.J x x - GridState.J y y) - 2 * (G.JX x - G.JX y) := by
  rw [maslovX_eq, maslovX_eq]
  ring

/-- The Alexander grading change at two grid states is the difference of the two marking pairing
changes. The state self-pairing term is common to both Maslov gradings and the normalization
shift depends only on the grid size, so both cancel, leaving a marking-only identity that needs
no relationship between `x` and `y`. -/
theorem alexander_sub (x y : GridState n) :
    G.alexander x - G.alexander y = (G.JX x - G.JX y) - (G.JO x - G.JO y) := by
  rw [alexander_eq, alexander_eq]
  ring

variable {x y : GridState n}

/-- Across a rectangle move the `O`-marking pairing change collapses to the four corners: the
source corners `(left, bottom)`, `(right, top)` against the target corners `(left, top)`,
`(right, bottom)`. The two states share all but their corners, and the shared part cancels. -/
theorem JO_sub_JO (R : GridRectangleBetween x y) :
    G.JO x - G.JO y =
      (GridPoint.J {(R.left, R.bottom)} G.OSet + GridPoint.J {(R.right, R.top)} G.OSet) -
        (GridPoint.J {(R.left, R.top)} G.OSet + GridPoint.J {(R.right, R.bottom)} G.OSet) := by
  have hsrc :
      (R.left, R.bottom) ∉ insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_bottom_notMem_inter⟩
  have htgt :
      (R.left, R.top) ∉ insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_top_notMem_inter⟩
  have key₁ :=
    GridPoint.J_insert_pair_left (P := G.OSet) hsrc R.right_top_notMem_inter
  have key₂ :=
    GridPoint.J_insert_pair_left (P := G.OSet) htgt R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  rw [JO_def, JO_def, key₁, key₂]
  ring

/-- Across a rectangle move the `X`-marking pairing change collapses to the four corners. -/
theorem JX_sub_JX (R : GridRectangleBetween x y) :
    G.JX x - G.JX y =
      (GridPoint.J {(R.left, R.bottom)} G.XSet + GridPoint.J {(R.right, R.top)} G.XSet) -
        (GridPoint.J {(R.left, R.top)} G.XSet + GridPoint.J {(R.right, R.bottom)} G.XSet) := by
  have hsrc :
      (R.left, R.bottom) ∉ insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_bottom_notMem_inter⟩
  have htgt :
      (R.left, R.top) ∉ insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_top_notMem_inter⟩
  have key₁ :=
    GridPoint.J_insert_pair_left (P := G.XSet) hsrc R.right_top_notMem_inter
  have key₂ :=
    GridPoint.J_insert_pair_left (P := G.XSet) htgt R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  rw [JX_def, JX_def, key₁, key₂]
  ring

/-- The Alexander grading change across a rectangle move, localized to the four corners: it is the
four `X`-corner pairings minus the four `O`-corner pairings, in each case the two source corners
against the two target corners. The state self-pairing cancels (`alexander_sub`) and the shared
squares cancel (`JX_sub_JX`, `JO_sub_JO`). -/
theorem alexander_change_rectangle (R : GridRectangleBetween x y) :
    G.alexander x - G.alexander y =
      ((GridPoint.J {(R.left, R.bottom)} G.XSet + GridPoint.J {(R.right, R.top)} G.XSet) -
          (GridPoint.J {(R.left, R.top)} G.XSet + GridPoint.J {(R.right, R.bottom)} G.XSet)) -
        ((GridPoint.J {(R.left, R.bottom)} G.OSet + GridPoint.J {(R.right, R.top)} G.OSet) -
          (GridPoint.J {(R.left, R.top)} G.OSet + GridPoint.J {(R.right, R.bottom)} G.OSet)) := by
  rw [alexander_sub, JX_sub_JX G R, JO_sub_JO G R]

/-- The `O`-Maslov grading change across a rectangle move: the state self-pairing change minus
twice the corner-localized `O`-marking pairing change. -/
theorem maslovO_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovO x - G.maslovO y =
      (GridState.J x x - GridState.J y y) -
        2 * ((GridPoint.J {(R.left, R.bottom)} G.OSet + GridPoint.J {(R.right, R.top)} G.OSet) -
          (GridPoint.J {(R.left, R.top)} G.OSet + GridPoint.J {(R.right, R.bottom)} G.OSet)) := by
  rw [maslovO_sub, JO_sub_JO G R]

/-- The `X`-Maslov grading change across a rectangle move: the state self-pairing change minus
twice the corner-localized `X`-marking pairing change. -/
theorem maslovX_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovX x - G.maslovX y =
      (GridState.J x x - GridState.J y y) -
        2 * ((GridPoint.J {(R.left, R.bottom)} G.XSet + GridPoint.J {(R.right, R.top)} G.XSet) -
          (GridPoint.J {(R.left, R.top)} G.XSet + GridPoint.J {(R.right, R.bottom)} G.XSet)) := by
  rw [maslovX_sub, JX_sub_JX G R]

end GridDiagram

end TauCeti
