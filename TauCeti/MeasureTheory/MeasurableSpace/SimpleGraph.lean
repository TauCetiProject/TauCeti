/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.MeasureTheory.MeasurableSpace.Relation

/-!
# Measurability of connectedness and of being a tree

Let `G : α → SimpleGraph V` be a family of simple graphs on a countable type `V`, parametrised by
a measurable space `α`, whose adjacency `{x | (G x).Adj a b}` is measurable for all `a` and `b`.
Then reachability, connectedness and being a tree are measurable conditions on `x`.
Reachability is a countable union over finite paths, connectedness is a countable intersection of
reachability conditions, and acyclicity says that every edge is a bridge, a reachability condition
in the graph with that edge deleted.

## Main results

* `TauCeti.measurableSet_setOf_reachable`: reachability is measurable.
* `TauCeti.measurableSet_setOf_connected`: connectedness is measurable.
* `TauCeti.measurableSet_setOf_isTree`: being a tree is measurable.
-/

public section

open Set

namespace TauCeti

variable {α V : Type*} [MeasurableSpace α] [Countable V] {G : α → SimpleGraph V}

/-- Reachability in a family of simple graphs on a countable type with measurable adjacency is
measurable. -/
theorem measurableSet_setOf_reachable (hG : ∀ a b, MeasurableSet {x | (G x).Adj a b}) (u v : V) :
    MeasurableSet {x | (G x).Reachable u v} := by
  simp only [SimpleGraph.reachable_iff_reflTransGen]
  exact measurableSet_setOf_reflTransGen hG u v

/-- Connectedness of a family of simple graphs on a countable type with measurable adjacency is
measurable. -/
theorem measurableSet_setOf_connected (hG : ∀ a b, MeasurableSet {x | (G x).Adj a b}) :
    MeasurableSet {x | (G x).Connected} := by
  simp only [SimpleGraph.connected_iff, SimpleGraph.Preconnected, ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v =>
    measurableSet_setOf_reachable hG u v).inter (MeasurableSet.const _)

/-- Being a tree is measurable in a family of simple graphs on a countable type with measurable
adjacency: the graph is connected, and every edge is a bridge. -/
theorem measurableSet_setOf_isTree (hG : ∀ a b, MeasurableSet {x | (G x).Adj a b}) :
    MeasurableSet {x | (G x).IsTree} := by
  have hB (u v : V) : MeasurableSet {x | ((G x).deleteEdges {s(u, v)}).Reachable u v} := by
    refine measurableSet_setOf_reachable (fun a b => ?_) u v
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, ofPred_and]
    exact (hG a b).inter (MeasurableSet.const _)
  have hT : {x | (G x).IsTree} = {x | (G x).Connected} ∩
      ⋂ u, ⋂ v, {x | (G x).Adj u v}ᶜ ∪ {x | ((G x).deleteEdges {s(u, v)}).Reachable u v}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff,
      SimpleGraph.isTree_iff, SimpleGraph.isAcyclic_iff_forall_adj_isBridge,
      SimpleGraph.isBridge_iff, imp_iff_not_or]
  rw [hT]
  exact (measurableSet_setOf_connected hG).inter
    (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v =>
      (hG u v).compl.union (hB u v).compl)

end TauCeti
