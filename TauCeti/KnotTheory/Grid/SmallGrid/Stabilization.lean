/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SmallGrid.Homology
public import TauCeti.KnotTheory.Grid.Stabilization.FullyBlocked.Homology

/-!
# The bigraded stabilization factor on small grids

The standard `2 × 2` grid has fully blocked Poincaré series `W`, and stabilization splitting an
`X`-marking multiplies the series by `W`. So the `3 × 3` unknot grids obtained by stabilizing the
standard `2 × 2` grid have series `W ^ 2`: the dependence of fully blocked homology on the grid
size is visible in the bigrading.

## Main results

* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_twoByTwo_stabilizeX`:
  the stabilizations of the standard `2 × 2` grid have Poincaré series `W ^ 2`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2.
-/

public section

namespace TauCeti.OddComponentGridDiagram

/-- The `3 × 3` unknot grids obtained by stabilizing the standard `2 × 2` grid have Poincaré
series `W ^ 2`: their fully blocked homology is `W ⊗ W`. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_twoByTwo_stabilizeX (s : Fin 2) :
    (twoByTwo.stabilizeX s).bigradedFullyBlockedHomologyPoincareSeries = Bigraded.W ^ 2 := by
  rw [bigradedFullyBlockedHomologyPoincareSeries_stabilizeX,
    bigradedFullyBlockedHomologyPoincareSeries_twoByTwo, sq]

end TauCeti.OddComponentGridDiagram
