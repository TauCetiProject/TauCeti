/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.RectangleSwap
import TauCeti.KnotTheory.Grid.Gradings

/-!
# The Alexander grading change across a grid rectangle

A rectangle `R : GridRectangleBetween x y` exchanges two side columns of the source state `x`,
so the two point sets `x` and `y` agree on `n - 2` shared squares and differ only at the four
corners of `R`. This file turns that corner/shared-square decomposition into four-corner
formulas for the change in `J`-pairings and in the Alexander grading.

The `J`-pairing of a state against a fixed marking set is additive over the disjoint corners
plus the shared part, so the contribution of the `n - 2` shared squares is the *same* for `x`
and for `y`. In the difference it cancels, leaving a formula in the four corners alone. For the
`O`- and `X`-marking pairings this is `JO_source_sub_JO_target` and `JX_source_sub_JX_target`.

Combining those rectangle-specific formulas with the grading definitions gives the headline
theorem `alexander_source_sub_alexander_target`: the Alexander grading change across a rectangle
depends only on the four corners of `R` and the markings, never on the `n - 2` shared squares.

## Main results

* `TauCeti.GridRectangleBetween.J_source_pointSet_eq`,
  `TauCeti.GridRectangleBetween.J_target_pointSet_eq`: the `J`-pairing of the source or target
  state against any point set splits as its two corners plus the shared part.
* `TauCeti.GridRectangleBetween.J_source_sub_J_target`: the corresponding difference, with the
  shared part cancelled.
* `TauCeti.GridDiagram.JO_source_sub_JO_target`,
  `TauCeti.GridDiagram.JX_source_sub_JX_target`: the four-corner formula for the `O`- and
  `X`-marking pairings.
* `TauCeti.GridDiagram.alexander_sub_alexander_eq_JX_sub_JX_sub_JO_sub_JO`: the general
  Alexander grading difference in terms of the `X`- and `O`-marking pairings.
* `TauCeti.GridDiagram.alexander_source_sub_alexander_target`: the four-corner formula for the
  Alexander grading change across a rectangle.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2 ("Gradings.
[...] grading-change formulas across a rectangle"), building on the corner/shared-square
decomposition that `RectangleSwap.lean` was written to support. The formula follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.
-/

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- The `J`-pairing of the source state against any point set splits as the contributions of its
two source corners `(R.left, R.bottom)` and `(R.right, R.top)` plus the contribution of the
`n - 2` squares it shares with the target state. -/
theorem J_source_pointSet_eq (s : Finset (Fin n × Fin n)) :
    GridPoint.J x.pointSet s =
      GridPoint.J {(R.left, R.bottom)} s + GridPoint.J {(R.right, R.top)} s +
        GridPoint.J (x.pointSet ∩ y.pointSet) s := by
  have hb : (R.right, R.top) ∉ x.pointSet ∩ y.pointSet := R.right_top_notMem_inter
  have ha : (R.left, R.bottom) ∉
      insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (congrArg Prod.fst h), R.left_bottom_notMem_inter⟩
  conv_lhs => rw [R.source_pointSet_eq]
  rw [GridPoint.J_insert_left ha, GridPoint.J_insert_left hb]
  ring

/-- The `J`-pairing of the target state against any point set splits as the contributions of its
two target corners `(R.left, R.top)` and `(R.right, R.bottom)` plus the contribution of the
`n - 2` squares it shares with the source state. -/
theorem J_target_pointSet_eq (s : Finset (Fin n × Fin n)) :
    GridPoint.J y.pointSet s =
      GridPoint.J {(R.left, R.top)} s + GridPoint.J {(R.right, R.bottom)} s +
        GridPoint.J (x.pointSet ∩ y.pointSet) s := by
  have hd : (R.right, R.bottom) ∉ x.pointSet ∩ y.pointSet := R.right_bottom_notMem_inter
  have hc : (R.left, R.top) ∉
      insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (congrArg Prod.fst h), R.left_top_notMem_inter⟩
  conv_lhs => rw [R.target_pointSet_eq]
  rw [GridPoint.J_insert_left hc, GridPoint.J_insert_left hd]
  ring

/-- The change in the `J`-pairing against a fixed point set from the source state to the target
state of a rectangle, with the shared `n - 2` squares cancelled: only the four corners remain. -/
theorem J_source_sub_J_target (s : Finset (Fin n × Fin n)) :
    GridPoint.J x.pointSet s - GridPoint.J y.pointSet s =
      GridPoint.J {(R.left, R.bottom)} s + GridPoint.J {(R.right, R.top)} s -
        GridPoint.J {(R.left, R.top)} s - GridPoint.J {(R.right, R.bottom)} s := by
  rw [R.J_source_pointSet_eq s, R.J_target_pointSet_eq s]
  ring

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

/-- The change in the `O`-marking `J`-pairing across a rectangle is determined by the four
corners alone. -/
theorem JO_source_sub_JO_target (R : GridRectangleBetween x y) :
    G.JO x - G.JO y =
      GridPoint.J {(R.left, R.bottom)} G.OSet + GridPoint.J {(R.right, R.top)} G.OSet -
        GridPoint.J {(R.left, R.top)} G.OSet - GridPoint.J {(R.right, R.bottom)} G.OSet := by
  rw [JO_def, JO_def]
  exact R.J_source_sub_J_target G.OSet

/-- The change in the `X`-marking `J`-pairing across a rectangle is determined by the four
corners alone. -/
theorem JX_source_sub_JX_target (R : GridRectangleBetween x y) :
    G.JX x - G.JX y =
      GridPoint.J {(R.left, R.bottom)} G.XSet + GridPoint.J {(R.right, R.top)} G.XSet -
        GridPoint.J {(R.left, R.top)} G.XSet - GridPoint.J {(R.right, R.bottom)} G.XSet := by
  rw [JX_def, JX_def]
  exact R.J_source_sub_J_target G.XSet

/-- The difference of Alexander gradings of two grid states is the corresponding difference of
the `X`-marking pairings minus the corresponding difference of the `O`-marking pairings. The
normalization shift in the Alexander grading cancels in the difference. -/
theorem alexander_sub_alexander_eq_JX_sub_JX_sub_JO_sub_JO (x y : GridState n) :
    G.alexander x - G.alexander y = (G.JX x - G.JX y) - (G.JO x - G.JO y) := by
  rw [alexander_def, alexander_def, maslovO_eq, maslovX_eq, maslovO_eq, maslovX_eq]
  ring

/-- The Alexander grading change across a rectangle, as a four-corner formula: it is the
alternating sum over the four corners of the `X`-marking pairing minus the same alternating sum of
the `O`-marking pairing. In particular it depends only on the four corners of the rectangle and
the markings, not on the `n - 2` squares the source and target states share. -/
theorem alexander_source_sub_alexander_target (R : GridRectangleBetween x y) :
    G.alexander x - G.alexander y =
      (GridPoint.J {(R.left, R.bottom)} G.XSet + GridPoint.J {(R.right, R.top)} G.XSet -
          GridPoint.J {(R.left, R.top)} G.XSet - GridPoint.J {(R.right, R.bottom)} G.XSet) -
        (GridPoint.J {(R.left, R.bottom)} G.OSet + GridPoint.J {(R.right, R.top)} G.OSet -
          GridPoint.J {(R.left, R.top)} G.OSet - GridPoint.J {(R.right, R.bottom)} G.OSet) := by
  rw [G.alexander_sub_alexander_eq_JX_sub_JX_sub_JO_sub_JO x y,
    G.JX_source_sub_JX_target R, G.JO_source_sub_JO_target R]

end GridDiagram

end TauCeti
