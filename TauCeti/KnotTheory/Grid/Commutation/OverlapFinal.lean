/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapRight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapWeight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapCounted
public import TauCeti.KnotTheory.Grid.Commutation.OverlapBijection
public import TauCeti.KnotTheory.Grid.Commutation.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Decomposition

/-!
# Final assembly: pentagon chain-map for grid commutation

This module records the assembly status for the pentagon chain-map proof and proves the
pieces that follow directly from the established infrastructure.

## Assembly status

The pentagon chain-map identity reduces via `pentagonMap_unblockedDifferential_single_eq_iff`
to the weight identity over decompositions. The infrastructure now in place:

**Disjoint part** (complete):
- `disjointCommuteEquiv` (Pairing.lean): bijection between disjoint rectangle-pentagon
  and pentagon-rectangle decompositions, with `commute_commute` involution.

**Overlap part** (infrastructure complete, assembly open):
- `recutLeftEqLeft` (Overlap.lean): forward recut for common-initial-side overlap,
  with `OMonomial_mul_OMonomial_recutLeftEqLeft` (weight preservation at the monomial level)
  and `turn_mem_recut_first_of_left_eq_left` (turn-row transport).
- `recutRightEqRight_first`/`_second` (OverlapRight.lean): terminal-side promotions
  (turn-row as explicit `hturn` hypothesis).
- `OverlapWeight.lean`: pentagon weight correction formula; correction = 1 when the
  column strips below the turn avoid O-markings.
- `OverlapCounted.lean`, `OverlapXAvoid.lean`, `OverlapColumns.lean`,
  `OverlapBranch2.lean`, `OverlapBijection.lean`: X-avoidance pieces for countedness.

**Remaining for the full chain map**:
1. Turn-row transports discharging the `hturn` hypotheses in `OverlapRight`
   (needs right-side cyclic-order transport analogous to `turn_mem_recut_first_of_left_eq_left`).
2. Countedness of the recut outputs (assembling the X-avoidance pieces into
   `mem_pentagons` / `mem_unblockedRectangles` membership).
3. Involution / reverse map on the overlap locus.
4. Finite-sum weight identity combining disjoint + overlap.
5. Chain-map theorem via the iff.

Roadmap: CombinatorialHeegaardFloer
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

variable (R : Type*) [CommSemiring R]

/-!
## The weight identity implies the chain map

This is the final implication, proved from `pentagonMap_unblockedDifferential_single_eq_iff`.
Once the weight identity (step 4 above) is established, the chain-map property follows
immediately.
-/

/-- The pentagon chain-map property follows from the decomposition weight identity.

This is the bridge from combinatorics to the Floer-theoretic statement: the pentagon
counting map intertwines the unblocked differentials. -/
theorem pentagon_chain_map_of_weight_identity
    (hweight : ∀ x z : GridState n,
      (∑ D ∈ G.rectanglePentagonDecompositions C x z,
          G.rectanglePentagonWeight C R D) =
        ∑ D ∈ G.pentagonRectangleDecompositions C x z,
          G.pentagonRectangleWeight C R D)
    (x : GridState n) :
    G.pentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) =
      (G.swapColumns C.column b).unblockedDifferential R
        (G.pentagonMap R C (Finsupp.single x 1)) :=
  (pentagonMap_unblockedDifferential_single_eq_iff G C R x).mpr (hweight x)

end GridDiagram

end TauCeti
