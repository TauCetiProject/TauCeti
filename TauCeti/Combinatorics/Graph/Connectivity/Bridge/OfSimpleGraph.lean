/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph

/-!
# Bridges of simple graphs viewed as multigraphs

Regarding a simple graph `H` as the multigraph `Graph.ofSimpleGraph H` preserves its actual
bridge edges.  The qualification by edge membership is essential: Mathlib's
`SimpleGraph.IsBridge` also holds for a non-edge whose endpoints lie in different connected
components, whereas a bridge of a `Graph` is always an actual edge.

The bridge correspondence also identifies multigraph forests with Mathlib's acyclic simple
graphs.  These results let bridge and ear arguments move between the two graph representations
without changing the cycle or edge identities involved.
-/

public section

open Set

universe u

namespace Graph

variable {α : Type u} {H : SimpleGraph α} {e : Sym2 α}

private theorem isBridge_ofSimpleGraph_iff_of_mem (he : e ∈ H.edgeSet) :
    (Graph.ofSimpleGraph H).IsBridge e ↔ H.IsBridge e := by
  rw [Graph.isBridge_iff_forall_cycle_notMem (by simpa),
    SimpleGraph.isBridge_iff_forall_cycle_notMem he]
  constructor
  · intro h x p hp
    simpa using h p.toGraph (SimpleGraph.Walk.isCycle_toGraph_iff p |>.mpr hp)
  · intro h x p hp
    simpa using h p.toSimpleGraph (Graph.Walk.isCycle_toSimpleGraph_iff p |>.mpr hp)

/-- A bridge of `Graph.ofSimpleGraph H` is exactly an actual edge that is a bridge of `H`.

The edge-membership conjunct cannot be dropped: `SimpleGraph.IsBridge` may hold for a non-edge
joining two different connected components. -/
@[simp]
theorem isBridge_ofSimpleGraph_iff :
    (Graph.ofSimpleGraph H).IsBridge e ↔ e ∈ H.edgeSet ∧ H.IsBridge e := by
  constructor
  · intro h
    have he : e ∈ H.edgeSet := by simpa using h.mem_edgeSet
    exact ⟨he, (isBridge_ofSimpleGraph_iff_of_mem he).mp h⟩
  · rintro ⟨he, h⟩
    exact (isBridge_ofSimpleGraph_iff_of_mem he).mpr h

/-- The bridge set of a simple graph viewed as a multigraph consists of its actual simple-graph
bridges. -/
@[simp]
theorem bridgeSet_ofSimpleGraph :
    (Graph.ofSimpleGraph H).bridgeSet = {e ∈ H.edgeSet | H.IsBridge e} := by
  ext e
  simp

/-- A simple graph is acyclic exactly when its associated multigraph is a forest. -/
@[simp]
theorem isForest_ofSimpleGraph_iff :
    (Graph.ofSimpleGraph H).IsForest ↔ H.IsAcyclic := by
  rw [Graph.isForest_iff_forall_isBridge, SimpleGraph.isAcyclic_iff_forall_isBridge]
  exact ⟨fun h e he ↦ (isBridge_ofSimpleGraph_iff.mp (h (by simpa using he))).2,
    fun h e he ↦ isBridge_ofSimpleGraph_iff.mpr ⟨by simpa using he, h (by simpa using he)⟩⟩

end Graph
