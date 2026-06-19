/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-!
# Grid diagram commutation moves

This file is reserved for commutation-specific grid diagram constructions. The total row and
column swap operations used as the underlying relabelings live in
`TauCeti.KnotTheory.Grid.Diagram`, next to the general row and column relabeling API. Later
commutation maps and invariance proofs can add the non-interleaving hypotheses and
rectangle-counting constructions here.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.5,
"Invariance over `𝔽₂`. Grid moves = commutation + (de)stabilization." It isolates the
underlying grid-diagram relabeling used by row and column commutations in the grid homology
construction of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

end TauCeti
