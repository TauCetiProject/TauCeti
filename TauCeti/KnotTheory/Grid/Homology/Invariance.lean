/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Invariance
public import TauCeti.KnotTheory.Grid.Homology.Tau

/-!
# Invariance of the Alexander-graded `GH⁻` and of `τ` under grid moves

The unblocked grid homology `GH⁻` of a knot grid, as an Alexander-graded `K[U]`-module, does not
change under any sequence of grid moves: knot grids connected by grid moves have isomorphic `GH⁻`
in the sense of `GridDiagram.IsKnot.UnblockedHomologyIsomorphic`
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`). This forgets the Maslov grading in
the invariance of `GH⁻` as an `(O-Maslov, Alexander)`-bigraded `K[U]`-module
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`), since the Alexander
grading is the coarsening of the bigrading. Consequently the diagram invariant
`GridDiagram.IsKnot.tau` is unchanged by grid moves (`GridDiagram.IsKnot.tau_eq_of_movesTo`).

This establishes independence of the presenting diagram for the isomorphism class of the
Alexander-graded `K[U]`-module `GH⁻`, and hence for `τ`. It does not identify the homology maps
associated to different move sequences.

## Main results

* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`: **invariance of `GH⁻`**,
  knot grids connected by grid moves have isomorphic Alexander-graded `GH⁻`.
* `TauCeti.GridDiagram.IsKnot.tau_eq_of_movesTo`: knot grids connected by grid moves have the
  same invariant `τ`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 5 and 6, in particular
the invariance of `GH⁻` under grid moves in Chapter 5 and the definition of `τ` in Chapter 6.
-/

public section

namespace TauCeti.GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **Invariance of `GH⁻` under grid moves.** Knot grid diagrams connected by arbitrary grid
moves have isomorphic unblocked grid homologies as Alexander-graded `K[U]`-modules. -/
theorem unblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.UnblockedHomologyIsomorphic hG' K :=
  (hG.bigradedUnblockedHomologyIsomorphic_of_movesTo K hG' h).unblockedHomologyIsomorphic

/-- Knot grid diagrams connected by arbitrary grid moves have the same invariant `τ`. -/
theorem tau_eq_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.tau K = hG'.tau K :=
  (hG.unblockedHomologyIsomorphic_of_movesTo K hG' h).tau_eq

end TauCeti.GridDiagram.IsKnot
