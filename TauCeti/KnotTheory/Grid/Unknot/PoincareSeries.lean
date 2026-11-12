/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.FullyBlocked
public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.SmallGrid.Homology
public import TauCeti.KnotTheory.Grid.Stabilization.FullyBlocked.Homology

/-!
# The fully blocked homology of the standard unknot grids

The fully blocked grid homology `GH~` (written $\widetilde{GH}$ in the literature) of a grid
diagram of size `n` presenting a knot `K` is `GH^(K) ⊗ W ^ (n - 1)`, where `W` is the
two-dimensional bigraded space with generators in bidegrees `(0, 0)` and `(-1, -1)`. For the
unknot `GH^` is one-dimensional in bidegree `(0, 0)`, so the standard unknot grid of size `n + 2`
has Poincaré series `W ^ (n + 1)` (`bigradedFullyBlockedHomologyPoincareSeries_unknot`). In
particular `GH~` genuinely depends on the size of the grid, not only on the knot it presents.

The proof is by induction on the size. The standard `2 × 2` grid has series `W`. The south-west
`X`-stabilization of the standard grid of size `n + 2` splitting the `X`-marking of its first
column multiplies the series by `W`
(`OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_stabilizeX`), and it differs
from the standard grid of size `n + 3` by a column commutation exchanging the two columns of the
new block, which does not change the series
(`OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation`).

## Main results

* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_unknot`: the
  standard unknot grid of size `n + 2` has fully blocked Poincaré series `W ^ (n + 1)`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2 (the identification
`GH~(G) ≅ GH^(K) ⊗ W ^ (n - 1)`) and Section 4.3 (the standard unknot grids).
-/

public section

namespace TauCeti.OddComponentGridDiagram

/-- **The fully blocked homology of the unknot grids.** The standard unknot grid of size `n + 2`
has fully blocked Poincaré series `W ^ (n + 1)`: its fully blocked homology is `W ^ (n + 1)` as a
bigraded vector space. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_unknot (n : ℕ) :
    bigradedFullyBlockedHomologyPoincareSeries
        (GridDiagram.isKnot_unknot n).toOddComponentGridDiagram =
      Bigraded.W ^ (n + 1) := by
  induction n with
  | zero =>
    have h : (GridDiagram.isKnot_unknot 0).toOddComponentGridDiagram = twoByTwo :=
      Subtype.ext GridDiagram.unknot_zero
    rw [h, bigradedFullyBlockedHomologyPoincareSeries_twoByTwo, zero_add, pow_one]
  | succ n ih =>
    have h : GridDiagram.IsColumnCommutation
        ((GridDiagram.isKnot_unknot n).toOddComponentGridDiagram.stabilizeX 0).1
        (GridDiagram.unknot (n + 1)) := by
      rw [val_stabilizeX, GridDiagram.unknot_X_apply_eq_add_one, zero_add, Fin.castSucc_zero,
        Fin.castSucc_one]
      exact GridDiagram.isColumnCommutation_stabilizeX_zero_unknot n
    rw [← bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation
      (G' := (GridDiagram.isKnot_unknot (n + 1)).toOddComponentGridDiagram) h,
      bigradedFullyBlockedHomologyPoincareSeries_stabilizeX, ih, ← pow_succ]

end TauCeti.OddComponentGridDiagram
