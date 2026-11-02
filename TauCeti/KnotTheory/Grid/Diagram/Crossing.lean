/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Basic
public import TauCeti.Order.Interval.Set.Fin

/-!
# The crossings of a grid diagram

A grid diagram `G` of size `n` is drawn as a planar link diagram in the square `[0, n] × [0, n]`:
in every column, a vertical segment joins the centres of the squares of its `X` and `O` markings,
and in every row, a horizontal segment joins the centres of the squares of its `O` and `X`
markings. The link is oriented from `X` to `O` along the vertical segments and from `O` to `X`
along the horizontal ones, which is the traversal recorded by `TauCeti.GridDiagram.componentPerm`,
and at every crossing the vertical segment passes over the horizontal one.

The vertical segment of column `c` runs through the squares of the rows strictly between `X c` and
`O c`, and the horizontal segment of row `r` through the squares of the columns strictly between
the columns `O.transpose r` and `X.transpose r` of its two markings. So the two segments cross,
at the centre of the square `(c, r)`, exactly when `r` lies strictly between the two markings of
column `c` and `c` strictly between the two markings of row `r`
(`TauCeti.GridDiagram.IsCrossing`). These are the crossings of the diagram
(`TauCeti.GridDiagram.crossings`).

The sign of a crossing (`TauCeti.GridDiagram.crossingSign`) follows the right-hand rule of
Lickorish, Chapter 1: seen from above, the crossing is positive when a counterclockwise quarter
turn takes the direction of the over-strand to that of the under-strand. The over-strand is
vertical, running upwards when `X c < O c`, and the under-strand is horizontal, running to the
right when `O.transpose r < X.transpose r`; the crossing is positive when the vertical strand
runs upwards and the horizontal one to the left, or downwards and to the right
(`TauCeti.GridDiagram.crossingSign_eq_one_iff`).

## Main definitions

* `TauCeti.GridDiagram.IsCrossing G c r`: the vertical segment of column `c` crosses the horizontal
  segment of row `r`.
* `TauCeti.GridDiagram.crossings G`: the finite set of crossings, as squares `(c, r)`.
* `TauCeti.GridDiagram.crossingSign G c r`: the sign of the crossing in the square `(c, r)`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208 (2015), Section 3.1, for the planar link diagram of a grid diagram,
  with vertical segments crossing over horizontal ones.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  crossing signs.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The vertical segment of column `c` crosses the horizontal segment of row `r` of the planar
diagram of `G`, at the centre of the square `(c, r)`: the row `r` lies strictly between the rows
`X c` and `O c` of the two markings of column `c`, and the column `c` lies strictly between the
columns `O.transpose r` and `X.transpose r` of the two markings of row `r`. -/
def IsCrossing (c r : Fin n) : Prop :=
  r ∈ Set.uIoo (G.X c) (G.O c) ∧ c ∈ Set.uIoo (G.O.transpose r) (G.X.transpose r)

theorem isCrossing_iff {c r : Fin n} :
    G.IsCrossing c r ↔
      r ∈ Set.uIoo (G.X c) (G.O c) ∧ c ∈ Set.uIoo (G.O.transpose r) (G.X.transpose r) :=
  Iff.rfl

/-- The crossing condition as four strict inequalities between the row `r`, the column `c` and
the markings of column `c` and row `r`. -/
theorem isCrossing_iff_lt {c r : Fin n} :
    G.IsCrossing c r ↔
      (min (G.X c) (G.O c) < r ∧ r < max (G.X c) (G.O c)) ∧
        (min (G.O.transpose r) (G.X.transpose r) < c ∧
          c < max (G.O.transpose r) (G.X.transpose r)) := by
  rw [isCrossing_iff, ← Set.Ioo_min_max, ← Set.Ioo_min_max, Set.mem_Ioo, Set.mem_Ioo]

instance (c r : Fin n) : Decidable (G.IsCrossing c r) :=
  decidable_of_iff _ G.isCrossing_iff_lt.symm

/-- The crossings of the planar diagram of `G`, as the squares `(c, r)` at whose centres they
lie. -/
def crossings : Finset (Fin n × Fin n) :=
  {p | G.IsCrossing p.1 p.2}

@[simp]
theorem mem_crossings {p : Fin n × Fin n} : p ∈ G.crossings ↔ G.IsCrossing p.1 p.2 := by
  simp [crossings]

/-- The sign of the crossing in the square `(c, r)`: positive when the vertical over-strand runs
upwards (`X c < O c`) and the horizontal under-strand to the left (`X.transpose r < O.transpose r`),
or the vertical strand downwards and the horizontal one to the right, and negative otherwise. The
value is meaningful at the crossings of `G`. -/
def crossingSign (c r : Fin n) : ℤˣ :=
  if (G.X c < G.O c ↔ G.X.transpose r < G.O.transpose r) then 1 else -1

/-- **The sign of a crossing.** The crossing in the square `(c, r)` is positive exactly when its
vertical strand runs upwards and its horizontal strand to the left, or its vertical strand
downwards and its horizontal strand to the right. -/
theorem crossingSign_eq_one_iff (c r : Fin n) :
    G.crossingSign c r = 1 ↔ (G.X c < G.O c ↔ G.X.transpose r < G.O.transpose r) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- The crossing in the square `(c, r)` is negative exactly when its vertical and horizontal
strands run upwards and to the right, or downwards and to the left. -/
theorem crossingSign_eq_neg_one_iff (c r : Fin n) :
    G.crossingSign c r = -1 ↔ ¬(G.X c < G.O c ↔ G.X.transpose r < G.O.transpose r) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_false (by decide) (not_not_intro h)
  · exact iff_of_true rfl h

end GridDiagram

end TauCeti
