/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.Basic
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# Rectangles into the `X`-marking state of a torus link grid

In the standard torus link grid `torusLink p q` the `X`-markings occupy the diagonal shifted up by
`q + 1` rows, so the `X`-marking permutation is a power of the cyclic shift `finRotate`
(`torusLink_X_toPerm`). This file specialises the cyclic-shift results of `Unblocked.lean` to the
torus grids: the unblocked differential counts every rectangle into the `X`-marking state `G.X`,
the grid state whose points are the lower-left corners of the `X`-marked squares
(`unblockedRectangles_torusLink_X`), and each grid state has none or two of them
(`even_card_unblockedRectangles_torusLink_X`). This parity is the hypothesis under which the class
of `G.X` in unblocked grid homology is not torsion.

## Main results

* `TauCeti.GridDiagram.unblockedRectangles_torusLink_X`: every rectangle into the `X`-marking
  state of a torus link grid is empty and avoids the `X`-markings.
* `TauCeti.GridDiagram.even_card_unblockedRectangles_torusLink_X`: each grid state has an even
  number of counted rectangles into the `X`-marking state.

## References

The diagram follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3; the
`X`-marking state is the canonical generator of Chapter 6 there.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {p q : ℕ} (y : GridState (p + 1 + (q + 1)))

/-- The unblocked differential of a torus link grid counts every rectangle into the `X`-marking
state. -/
@[simp]
theorem unblockedRectangles_torusLink_X :
    (torusLink p q).unblockedRectangles y (torusLink p q).X = Finset.univ :=
  (torusLink p q).unblockedRectangles_X_of_X_toPerm_eq_finRotate_pow y (torusLink_X_toPerm p q)

/-- Every grid state of a torus link grid has an even number, zero or two, of rectangles into the
`X`-marking state counted by the unblocked differential. -/
theorem even_card_unblockedRectangles_torusLink_X :
    Even ((torusLink p q).unblockedRectangles y (torusLink p q).X).card :=
  (torusLink p q).even_card_unblockedRectangles_X_of_X_toPerm_eq_finRotate_pow y
    (torusLink_X_toPerm p q)

end GridDiagram

end TauCeti
