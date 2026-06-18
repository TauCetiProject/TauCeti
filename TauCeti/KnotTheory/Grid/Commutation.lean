/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Diagram

/-!
# Row and column swaps for grid diagrams

This file records the elementary row and column swap operations on grid states and grid
diagrams. These swaps are the diagram-level operations underlying commutation moves; the
later commutation maps and invariance proofs can add the non-interleaving hypotheses and
rectangle-counting constructions on top of these total operations.

## Main definitions

* `TauCeti.GridState.swapRows`, `TauCeti.GridState.swapColumns`: row and column swaps of
  grid states.
* `TauCeti.GridDiagram.swapRows`, `TauCeti.GridDiagram.swapColumns`: row and column swaps.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.5,
"Invariance over `𝔽₂`. Grid moves = commutation + (de)stabilization." It isolates the
underlying grid-diagram relabeling used by row and column commutations in the grid homology
construction of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Swapping two rows in a grid state. -/
def swapRows (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid state. -/
def swapColumns (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelColumns (Equiv.swap a b)

/-- Row swaps evaluate by swapping the row selected by the old state. -/
@[simp]
theorem swapRows_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapRows a b c = Equiv.swap a b (x c) :=
  rfl

/-- Column swaps evaluate by reading the old state at the swapped column. -/
@[simp]
theorem swapColumns_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapColumns a b c = x (Equiv.swap a b c) := by
  simp [swapColumns, relabelColumns]

/-- Swapping the same pair of rows twice is the identity on grid states. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).swapRows a b = x := by
  ext c
  simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid states. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp [swapColumns]

end GridState

namespace GridDiagram

variable {n : ℕ}

/-- Swapping two rows in a grid diagram. -/
def swapRows (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid diagram. -/
def swapColumns (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelColumns (Equiv.swap a b)

/-- The `O` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_O (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).O = G.O.swapRows a b :=
  rfl

/-- The `X` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_X (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).X = G.X.swapRows a b :=
  rfl

/-- The `O` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_O (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).O = G.O.swapColumns a b :=
  rfl

/-- The `X` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_X (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).X = G.X.swapColumns a b :=
  rfl

/-- Swapping the same pair of rows twice is the identity on grid diagrams. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).swapRows a b = G := by
  simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid diagrams. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).swapColumns a b = G := by
  simp [swapColumns]

end GridDiagram

end TauCeti
