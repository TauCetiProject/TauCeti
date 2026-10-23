/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.Group.Generation

/-!
# Finiteness of `H¹` over a topologically finitely generated group

A continuous `1`-cocycle into a `T1` module is determined by its values on a topological generating
set (`TauCeti.ContCohomology.eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top`). Over a
topologically finitely generated group, restriction to a finite topological generating set is
therefore an injection of the continuous `1`-cocycles with values in a finite discrete module into
a finite set, so the cocycles form a finite group, and so does `H¹(G, M)`.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.finite_Z1` and
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_H1`: over a topologically finitely generated
  group, `Z¹(G, M)` and `H¹(G, M)` are finite for every finite discrete `G`-module `M`.
-/

public section

namespace TauCeti

open ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]

/-- **Finiteness of the continuous `1`-cocycles.** Over a topologically finitely generated group,
the continuous `1`-cocycles with values in a finite discrete module form a finite group: restriction
to a finite topological generating set is injective. -/
theorem IsTopologicallyFinitelyGenerated.finite_Z1 (hG : IsTopologicallyFinitelyGenerated G)
    [Finite M] : Finite (Z1 G M) := by
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.1 hG
  refine Finite.of_injective (fun f : Z1 G M ↦ fun x : s ↦ (f : G → M) x) fun f f' h ↦ ?_
  exact Subtype.ext (eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top f.2 f'.2 hs
    fun x hx ↦ congrFun h ⟨x, hx⟩)

/-- **Finiteness of `H¹`.** Over a topologically finitely generated group, `H¹(G, M)` is finite for
every finite discrete `G`-module `M`. -/
theorem IsTopologicallyFinitelyGenerated.finite_H1 (hG : IsTopologicallyFinitelyGenerated G)
    [ContinuousSMul G M] [Finite M] : Finite (H1 G M) :=
  have := hG.finite_Z1 (M := M)
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective ((B1 G M).addSubgroupOf (Z1 G M)))

end TauCeti
