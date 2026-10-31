/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Move.Unknot

/-!
# The diagonal reflection of grid links

The diagonal reflection `GridDiagram.transpose` exchanges the rows and the columns of a grid
diagram. It carries a cyclic permutation of the rows to a cyclic permutation of the columns and
back, exchanges row and column commutations (`GridDiagram.isCommutation_transpose`), and carries
stabilizations to stabilizations (`GridDiagram.isStabilization_transpose`). So it carries grid
moves to grid moves and descends to an involution `GridLink.transpose` of grid links. It fixes the
unknot and preserves the number of components.

The standard grid of the `(p + 1, q + 1)` torus link reflects to the standard grid of the
`(q + 1, p + 1)` torus link (`GridDiagram.transpose_torusLink`), so the two present grid links
exchanged by the reflection (`GridLink.toGridLink_transpose_torusLink`). In particular every
standard `(1, q + 1)` torus link grid presents the unknot.

Read as a planar diagram whose vertical segments cross over the horizontal ones, the reflection of
a grid diagram presents the reverse of its link: reflecting the plane in the diagonal and changing
every crossing compose to a rotation of space, and the orientation conventions of vertical and
horizontal segments are exchanged. As with the other classical readings of grid diagrams, this
is motivation only and is not formalized here.

## Main definitions

* `TauCeti.GridLink.transpose`: the diagonal reflection of grid links.

## Main results

* `TauCeti.GridDiagram.movesTo_transpose_iff`: the reflection preserves the grid move relation.
* `TauCeti.GridLink.transpose_toGridLink`: the reflection of the grid link of a diagram is the
  grid link of the reflected diagram.
* `TauCeti.GridLink.transpose_transpose`: the reflection is an involution.
* `TauCeti.GridLink.transpose_unknot`, `TauCeti.GridLink.componentCount_transpose`: it fixes the
  unknot and preserves the number of components.
* `TauCeti.GridLink.toGridLink_transpose_torusLink`: it exchanges the grid links of the standard
  `(p + 1, q + 1)` and `(q + 1, p + 1)` torus link grids.
* `TauCeti.GridDiagram.toGridLink_torusLink_zero_left`: the standard `(1, q + 1)` torus link grid
  presents the unknot.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 3: grid diagrams, their symmetries, and grid moves.
-/

public section

namespace TauCeti

namespace GridLink

/-- Reflecting a cyclic permutation of the rows gives a cyclic permutation of the columns. -/
private theorem toGridLink_transpose_relabelRows {n : ℕ} (G : GridDiagram n) :
    G.transpose.toGridLink = (G.relabelRows (finRotate n)).transpose.toGridLink := by
  rw [GridDiagram.relabelRows_transpose, ← GridDiagram.cyclicColumns_toGridLink_eq]

/-- Reflecting a cyclic permutation of the columns gives a cyclic permutation of the rows. -/
private theorem toGridLink_transpose_relabelColumns {n : ℕ} (G : GridDiagram n) :
    G.transpose.toGridLink = (G.relabelColumns (finRotate n)).transpose.toGridLink := by
  rw [GridDiagram.relabelColumns_transpose, ← GridDiagram.cyclicRows_toGridLink_eq]

/-- Reflecting a commutation gives a commutation. -/
private theorem toGridLink_transpose_of_isCommutation {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsCommutation G') : G.transpose.toGridLink = G'.transpose.toGridLink :=
  ((GridDiagram.isCommutation_transpose _ _).mpr h).toGridLink_eq

/-- Reflecting a stabilization gives a stabilization. -/
private theorem toGridLink_transpose_of_isStabilization {n : ℕ} {G : GridDiagram n}
    {G' : GridDiagram (n + 1)} (h : G.IsStabilization G') :
    G.transpose.toGridLink = G'.transpose.toGridLink :=
  ((GridDiagram.isStabilization_transpose _ _).mpr h).toGridLink_eq

/-- The diagonal reflection of grid links: the grid link of the diagonal reflection of any
presenting diagram (`GridLink.transpose_toGridLink`). It is well defined because the reflection
exchanges cyclic permutations of rows and of columns, exchanges row and column commutations, and
carries stabilizations to stabilizations. -/
def transpose : GridLink → GridLink :=
  lift (fun _ G => G.transpose.toGridLink) toGridLink_transpose_relabelRows
    toGridLink_transpose_relabelColumns toGridLink_transpose_of_isCommutation
    toGridLink_transpose_of_isStabilization

/-- The reflection of the grid link of a diagram is the grid link of the reflected diagram. -/
@[simp]
theorem transpose_toGridLink {n : ℕ} (G : GridDiagram n) :
    G.toGridLink.transpose = G.transpose.toGridLink :=
  lift_toGridLink _ toGridLink_transpose_relabelRows toGridLink_transpose_relabelColumns
    toGridLink_transpose_of_isCommutation toGridLink_transpose_of_isStabilization G

/-- The diagonal reflection of grid links is an involution. -/
@[simp]
theorem transpose_transpose (L : GridLink) : L.transpose.transpose = L :=
  ind (motive := fun L => L.transpose.transpose = L)
    (fun G => by rw [transpose_toGridLink, transpose_toGridLink, GridDiagram.transpose_transpose]) L

/-- The diagonal reflection of grid links is an involution. -/
theorem transpose_involutive : Function.Involutive transpose :=
  transpose_transpose

/-- The diagonal reflection of grid links is injective. -/
theorem transpose_injective : Function.Injective transpose :=
  transpose_involutive.injective

/-- Two grid links have equal reflections exactly when they are equal. -/
@[simp]
theorem transpose_inj {L L' : GridLink} : L.transpose = L'.transpose ↔ L = L' :=
  transpose_injective.eq_iff

/-- The standard `2 × 2` unknot grid is symmetric under the diagonal reflection. -/
private theorem transpose_unknot_zero :
    (GridDiagram.unknot 0).transpose = GridDiagram.unknot 0 := by
  refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_)
  · rw [GridDiagram.transpose_O, GridState.transpose_apply, Equiv.symm_apply_eq,
      GridDiagram.unknot_O_toPerm, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  · rw [GridDiagram.transpose_X, GridState.transpose_apply, Equiv.symm_apply_eq,
      GridDiagram.unknot_X_toPerm]
    fin_cases c <;> decide

/-- The diagonal reflection fixes the unknot. -/
@[simp]
theorem transpose_unknot : unknot.transpose = unknot := by
  rw [← GridDiagram.toGridLink_unknot 0, transpose_toGridLink, transpose_unknot_zero]

/-- The diagonal reflection preserves the number of components of a grid link. -/
@[simp]
theorem componentCount_transpose (L : GridLink) : L.transpose.componentCount = L.componentCount :=
  ind (motive := fun L => L.transpose.componentCount = L.componentCount)
    (fun G => by
      rw [transpose_toGridLink, componentCount_toGridLink, componentCount_toGridLink,
        GridDiagram.componentCount_transpose]) L

/-- The diagonal reflection of a grid link is a knot exactly when the grid link is. -/
@[simp]
theorem isKnot_transpose {L : GridLink} : L.transpose.IsKnot ↔ L.IsKnot := by
  rw [isKnot_def, isKnot_def, componentCount_transpose]

/-- The diagonal reflection exchanges the grid links of the standard `(p + 1, q + 1)` and
`(q + 1, p + 1)` torus link grids. -/
theorem toGridLink_transpose_torusLink (p q : ℕ) :
    (GridDiagram.torusLink p q).transpose.toGridLink = (GridDiagram.torusLink q p).toGridLink := by
  rw [GridDiagram.transpose_torusLink, GridDiagram.toGridLink_cast]

end GridLink

namespace GridDiagram

/-- The diagonal reflection preserves the grid move relation. -/
@[simp]
theorem movesTo_transpose_iff {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m} :
    G.transpose.MovesTo G'.transpose ↔ G.MovesTo G' := by
  rw [← toGridLink_eq_iff_movesTo, ← toGridLink_eq_iff_movesTo, ← GridLink.transpose_toGridLink,
    ← GridLink.transpose_toGridLink, GridLink.transpose_inj]

/-- The standard grid of the `(1, q + 1)` torus link presents the unknot: it is the diagonal
reflection of the standard `(q + 1, 1)` torus link grid, which is a standard unknot grid. -/
theorem toGridLink_torusLink_zero_left (q : ℕ) :
    (torusLink 0 q).toGridLink = GridLink.unknot := by
  rw [← GridLink.toGridLink_transpose_torusLink, torusLink_zero_right,
    ← GridLink.transpose_toGridLink, toGridLink_unknot, GridLink.transpose_unknot]

end GridDiagram

end TauCeti
