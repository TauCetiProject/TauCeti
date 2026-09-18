/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra

/-!
# The signless relator of a simple graph

For the doubled quiver `TauCeti.DoubledQuiver G` of a simple graph `G`, the signless preprojective
relator `TauCeti.signlessPreprojectiveRelator` at a vertex `v` is `∑_{j ∼ v} (v → j → v)`, the sum
of the backtracks along the edges at `v`. This is the relation which Huerfano and Khovanov find in
the quadratic dual of the zigzag algebra of `G`.

## Main results

* `TauCeti.signlessPreprojectiveRelator_vertex`: for a simple graph the relator is the sum of the
  backtracks `TauCeti.DoubledQuiver.backtrackElem` over the neighbours.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u w

variable (k : Type w) {V : Type u} [Semiring k] (G : SimpleGraph V)

/-- The star of the doubled quiver of `G` at `v` is finite, being in bijection with the neighbour
set of `v`. -/
noncomputable local instance (v : V) [Fintype (G.neighborSet v)] :
    Fintype (Quiver.Star (DoubledQuiver.vertex G v)) :=
  Fintype.ofEquiv _ (DoubledQuiver.starEquivNeighborSet G v).symm

/-- **The signless relator of a simple graph** at `v` is `∑_{j ∼ v} (v → j → v)`, the sum of the
backtracks along the edges at `v`. -/
theorem signlessPreprojectiveRelator_vertex (v : V) [Fintype (G.neighborSet v)] :
    signlessPreprojectiveRelator k (DoubledQuiver.vertex G v) =
      ∑ w : G.neighborSet v, DoubledQuiver.backtrackElem G k ((G.mem_neighborSet v w).1 w.2) := by
  rw [signlessPreprojectiveRelator_def,
    ← (DoubledQuiver.starEquivNeighborSet G v).symm.sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [DoubledQuiver.starEquivNeighborSet_symm_apply, DoubledQuiver.backtrackElem_eq_ofPath,
    DoubledQuiver.backtrackPath_eq_comp, DoubledQuiver.arrowPath_eq_toPath,
    DoubledQuiver.arrowPath_eq_toPath]
  -- The reverse of the arrow along `w` is the arrow of the symmetric adjacency.
  rfl

end TauCeti
