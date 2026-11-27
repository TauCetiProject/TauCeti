/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import TauCeti.MeasureTheory.MeasurableSpace.Relation

/-!
# Measurability of connectedness, of infinite components and of being a tree

For simple graphs on a countable type `V`, with Mathlib's σ-algebra on `SimpleGraph V` (pulled
back along adjacency), reachability, connectedness, having an infinite connected component and
being a tree are measurable sets of graphs.
Reachability is a countable union over finite paths, connectedness is a countable intersection of
reachability conditions, and acyclicity says that every edge is a bridge, a reachability condition
in the graph with that edge deleted. The connected component of `u` is infinite exactly when, for
each of the countably many finite sets `t` of vertices, some vertex outside `t` is reachable from
`u`; some component is infinite exactly when this holds for one of the countably many `u`. These
are the events of percolation theory, where the open cluster of a point is its connected component
in the random graph of open edges. A family of graphs `G : α → SimpleGraph V` with measurable
adjacency is a measurable map (`SimpleGraph.measurable_iff_adj`), so these sets pull back along it.

## Main results

* `TauCeti.measurableSet_setOf_reachable`: reachability is measurable.
* `TauCeti.measurableSet_setOf_connected`: connectedness is measurable.
* `TauCeti.measurableSet_setOf_supp_infinite`: the connected component of a vertex being infinite
  is measurable.
* `TauCeti.measurableSet_setOf_exists_supp_infinite`: some connected component being infinite is
  measurable.
* `TauCeti.measurableSet_setOf_isTree`: being a tree is measurable.

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS, 2018, the two
  displays on p. 2, for the infinite-component events.
-/

public section

open Set

namespace TauCeti

variable {V : Type*} [Countable V]

/-- Reachability in a simple graph on a countable type is a measurable set of graphs. -/
theorem measurableSet_setOf_reachable (u v : V) :
    MeasurableSet {G : SimpleGraph V | G.Reachable u v} := by
  simp only [SimpleGraph.reachable_iff_reflTransGen]
  exact measurableSet_setOf_reflTransGen
    (fun a b => measurableSet_setOfPred.2 (by fun_prop)) u v

/-- Connectedness of a simple graph on a countable type is a measurable set of graphs. -/
theorem measurableSet_setOf_connected : MeasurableSet {G : SimpleGraph V | G.Connected} := by
  simp only [SimpleGraph.connected_iff, SimpleGraph.Preconnected, ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v =>
    measurableSet_setOf_reachable u v).inter (MeasurableSet.const _)

/-- The connected component of a vertex being infinite is a measurable set of simple graphs on a
countable type. -/
theorem measurableSet_setOf_supp_infinite (u : V) :
    MeasurableSet {G : SimpleGraph V | (G.connectedComponentMk u).supp.Infinite} := by
  have : {G : SimpleGraph V | (G.connectedComponentMk u).supp.Infinite} =
      ⋂ t : Finset V, ⋃ v ∈ (t : Set V)ᶜ, {G | G.Reachable u v} := by
    ext G
    have hmem (v : V) : v ∈ (G.connectedComponentMk u).supp ↔ G.Reachable u v := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
        SimpleGraph.reachable_comm]
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, Finset.mem_coe, exists_prop]
    refine ⟨fun h t => ?_, fun h hfin => ?_⟩
    · obtain ⟨v, hv, hvt⟩ := h.exists_notMem_finset t
      exact ⟨v, hvt, (hmem v).1 hv⟩
    · obtain ⟨v, hvt, huv⟩ := h hfin.toFinset
      exact hvt (hfin.mem_toFinset.2 ((hmem v).2 huv))
  rw [this]
  exact .iInter fun t => .biUnion (to_countable _) fun v _ => measurableSet_setOf_reachable u v

/-- Some connected component being infinite is a measurable set of simple graphs on a countable
type. -/
theorem measurableSet_setOf_exists_supp_infinite :
    MeasurableSet {G : SimpleGraph V | ∃ u, (G.connectedComponentMk u).supp.Infinite} := by
  simpa only [ofPred_exists] using MeasurableSet.iUnion measurableSet_setOf_supp_infinite

/-- Being a tree is a measurable set of simple graphs on a countable type: the graph is
connected, and every edge is a bridge. -/
theorem measurableSet_setOf_isTree : MeasurableSet {G : SimpleGraph V | G.IsTree} := by
  have hD (s : Set (Sym2 V)) : Measurable fun G : SimpleGraph V => G.deleteEdges s := by
    simp only [SimpleGraph.measurable_iff_adj, SimpleGraph.deleteEdges_adj]
    fun_prop
  have hA (u v : V) : MeasurableSet {G : SimpleGraph V | G.Adj u v} :=
    measurableSet_setOfPred.2 (by fun_prop)
  have hT : {G : SimpleGraph V | G.IsTree} = {G | G.Connected} ∩
      ⋂ u, ⋂ v, {G | G.Adj u v}ᶜ ∪
        (fun G : SimpleGraph V => G.deleteEdges {s(u, v)}) ⁻¹' {G | G.Reachable u v}ᶜ := by
    ext G
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff,
      mem_preimage, SimpleGraph.isTree_iff, SimpleGraph.isAcyclic_iff_forall_adj_isBridge,
      SimpleGraph.isBridge_iff, imp_iff_not_or]
  rw [hT]
  exact measurableSet_setOf_connected.inter
    (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v =>
      (hA u v).compl.union ((measurableSet_setOf_reachable u v).compl.preimage (hD _)))

end TauCeti
