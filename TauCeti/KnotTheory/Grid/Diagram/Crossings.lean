/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Basic
public import TauCeti.Order.Interval.Set.UnorderedInterval

/-!
# Crossings of the planar diagram of a grid diagram

A grid diagram `G` of grid number `n` is drawn in the plane as follows (Ozsváth–Stipsicz–Szabó,
Section 3.1). In each column a vertical segment joins the `X`-marking to the `O`-marking, and in
each row a horizontal segment joins the `O`-marking to the `X`-marking; the link is oriented from
`X` to `O` along the columns and from `O` to `X` along the rows. Wherever a vertical segment meets
a horizontal one away from the markings, the vertical segment crosses over the horizontal one.

* **Crossings.** The vertical segment of column `c` and the horizontal segment of row `r` meet in
  the square `(c, r)` exactly when `r` lies strictly between the rows of the two markings of
  column `c` and `c` strictly between the columns of the two markings of row `r`
  (`TauCeti.GridDiagram.IsCrossing`); the segments of a column and of a row sharing a marking meet
  only at that marking, which is a corner of the diagram rather than a crossing. The crossings form
  the finite set `TauCeti.GridDiagram.crossings`.
* **Signs.** The vertical strand at a crossing passes over, so the crossing is positive, in the
  right-handed convention of Lickorish, exactly when a counterclockwise quarter turn takes the
  direction of the vertical strand to that of the horizontal one: the vertical strand runs up and
  the horizontal one to the left, or down and to the right (`TauCeti.GridDiagram.crossingSign`).

## Main definitions

* `TauCeti.GridDiagram.IsCrossing`, `TauCeti.GridDiagram.crossings`: the crossings of the planar
  diagram of a grid.
* `TauCeti.GridDiagram.crossingSign`: the sign of a crossing.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Section 3.1, for the planar diagram of a grid diagram.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  crossing signs.
-/

public section

open Set

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The square `(c, r)` is a **crossing** of the planar diagram of the grid diagram `G`: the row
`r` lies strictly between the rows of the `O`- and `X`-markings of column `c`, so that the
vertical segment of column `c` runs through the square, and the column `c` lies strictly between
the columns of the two markings of row `r`, so that the horizontal segment of row `r` runs
through it. -/
def IsCrossing (p : Fin n × Fin n) : Prop :=
  p.2 ∈ uIoo (G.O p.1) (G.X p.1) ∧ p.1 ∈ uIoo (G.O.transpose p.2) (G.X.transpose p.2)

/-- The defining property of a crossing. -/
theorem isCrossing_iff {p : Fin n × Fin n} :
    G.IsCrossing p ↔
      p.2 ∈ uIoo (G.O p.1) (G.X p.1) ∧ p.1 ∈ uIoo (G.O.transpose p.2) (G.X.transpose p.2) :=
  Iff.rfl

instance : DecidablePred G.IsCrossing := fun p =>
  decidable_of_iff ((G.O p.1 < p.2 ∧ p.2 < G.X p.1 ∨ G.X p.1 < p.2 ∧ p.2 < G.O p.1) ∧
      (G.O.transpose p.2 < p.1 ∧ p.1 < G.X.transpose p.2 ∨
        G.X.transpose p.2 < p.1 ∧ p.1 < G.O.transpose p.2))
    (by rw [isCrossing_iff, mem_uIoo, mem_uIoo])

/-- The crossings of the planar diagram of a grid diagram. -/
def crossings : Finset (Fin n × Fin n) :=
  {p | G.IsCrossing p}

@[simp]
theorem mem_crossings {p : Fin n × Fin n} : p ∈ G.crossings ↔ G.IsCrossing p := by
  simp [crossings]

/-- The **sign** of the crossing in the square `(c, r)`. The vertical strand of column `c`, running
from the `X`-marking to the `O`-marking, passes over the horizontal strand of row `r`, running
from the `O`-marking to the `X`-marking. The crossing is positive when the vertical strand runs up
and the horizontal one to the left, or down and to the right, and negative otherwise. -/
def crossingSign (p : Fin n × Fin n) : ℤˣ :=
  if (G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) then 1 else -1

/-- A crossing is positive exactly when its vertical strand runs up while its horizontal strand
runs to the left, or down while it runs to the right. -/
theorem crossingSign_eq_one_iff {p : Fin n × Fin n} :
    G.crossingSign p = 1 ↔ (G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- A crossing is negative exactly when it is not positive. -/
theorem crossingSign_eq_neg_one_iff {p : Fin n × Fin n} :
    G.crossingSign p = -1 ↔ ¬(G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_false (by decide) (not_not_intro h)
  · exact iff_of_true rfl h

end GridDiagram

end TauCeti
