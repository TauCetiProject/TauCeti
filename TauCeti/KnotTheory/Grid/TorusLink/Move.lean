/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# The diagonal reflection of torus link grid links

The standard grid of the `(p + 1, q + 1)` torus link reflects to the standard grid of the
`(q + 1, p + 1)` torus link (`GridDiagram.transpose_torusLink`), so the diagonal reflection of
grid links (`GridLink.transpose`) exchanges the grid links the two grids present. In particular
every standard `(1, q + 1)` torus link grid presents the unknot, and when `p + 1` and `q + 1` are
coprime the standard `(p + 1, q + 1)` torus link grid presents a grid knot
(`GridLink.isKnot_toGridLink_torusLink`).

## Main results

* `TauCeti.GridLink.isKnot_toGridLink_torusLink`: for coprime `p + 1` and `q + 1`, the standard
  `(p + 1, q + 1)` torus link grid presents a grid knot.
* `TauCeti.GridLink.toGridLink_transpose_torusLink`: the reflection exchanges the grid links of
  the standard `(p + 1, q + 1)` and `(q + 1, p + 1)` torus link grids.
* `TauCeti.GridDiagram.toGridLink_torusLink_zero_left`: the standard `(1, q + 1)` torus link grid
  presents the unknot.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 3: grid diagrams, their symmetries, and grid moves.
-/

public section

namespace TauCeti

namespace GridLink

/-- When `p + 1` and `q + 1` are coprime, the standard `(p + 1, q + 1)` torus link grid presents a
grid knot. -/
theorem isKnot_toGridLink_torusLink {p q : ℕ} (h : (p + 1).Coprime (q + 1)) :
    (GridDiagram.torusLink p q).toGridLink.IsKnot :=
  (isKnot_toGridLink _).mpr ((GridDiagram.isKnot_torusLink_iff p q).mpr h)

/-- The diagonal reflection exchanges the grid links of the standard `(p + 1, q + 1)` and
`(q + 1, p + 1)` torus link grids. -/
theorem toGridLink_transpose_torusLink (p q : ℕ) :
    (GridDiagram.torusLink p q).transpose.toGridLink = (GridDiagram.torusLink q p).toGridLink := by
  rw [GridDiagram.transpose_torusLink, GridDiagram.toGridLink_cast]

end GridLink

namespace GridDiagram

/-- The standard grid of the `(1, q + 1)` torus link presents the unknot: it is the diagonal
reflection of the standard `(q + 1, 1)` torus link grid, which is a standard unknot grid. -/
@[simp]
theorem toGridLink_torusLink_zero_left (q : ℕ) :
    (torusLink 0 q).toGridLink = GridLink.unknot := by
  rw [← GridLink.toGridLink_transpose_torusLink, torusLink_zero_right,
    ← GridLink.transpose_toGridLink, toGridLink_unknot, GridLink.transpose_unknot]

end GridDiagram

end TauCeti
