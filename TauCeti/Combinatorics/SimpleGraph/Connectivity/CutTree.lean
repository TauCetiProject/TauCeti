/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Graph

/-!
# Cut trees for finite simple graphs

This file gives the native simple-graph specialization of the Gomory--Hu cut-tree theorem.
The unit cut capacity of a vertex set counts graph edges crossing to its complement. A cut tree
for this function records local edge reachability as the minimum weight on each tree path, and a
minimum-weight path edge recovers an actual minimum cut of the original simple graph.

The threshold form says that deleting tree edges of weight below `k` leaves precisely the local
`k`-edge-reachability classes. When the vertex type has at least two elements, a minimum-weight
tree edge also records the global edge connectivity.

## Main results

* `SimpleGraph.unitCutCapacity`: the number of graph edges crossing a vertex cut.
* `SimpleGraph.exists_isUnitCutTree`: every nonempty finite simple graph has a unit cut tree.
* `IsFlowEquivalentTree.reachable_deleteEdges_iff_simpleGraph_edgeReachability`: the threshold
  partition of a unit cut tree is local edge reachability in the original graph.
* `IsCutTree.simpleGraph_edgeReachability_eq_unitCutCapacity_edgeSide`: a minimum-weight tree-path
  edge recovers a minimum cut in the original graph.
* `IsFlowEquivalentTree.exists_edge_simpleGraph_edgeConnectivity_eq_weight`: global edge
  connectivity is the minimum tree-edge weight.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.

The multigraph existence and query interface adapted here is developed in
`TauCeti.Combinatorics.Network.MinimumCut.Graph`, especially
`Graph.exists_isUnitCutTree`, `IsFlowEquivalentTree.reachable_deleteEdges_iff_edgeReachability`,
and `IsCutTree.edgeReachability_eq_edgeCutCapacity_edgeSide`.
-/

public section

open Finset
open scoped Graph

namespace SimpleGraph

variable {V : Type*}

/-- Every nonempty finite simple graph has a cut tree for unit edge capacities. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree G.unitCutCapacity T w := by
  classical
  have hcapacity := funext G.unitCutCapacity_def
  rw [hcapacity]
  apply TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity
  intro x y _
  simp

end SimpleGraph

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit cut tree of a simple graph, some minimum-weight edge on every nontrivial tree path
has weight equal to the local edge reachability of its endpoints. -/
theorem exists_weight_eq_simpleGraph_edgeReachability
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w)
    {s t : V} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) ∧
      ∀ e' ∈ p.edges, w e ≤ w e' := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_, fun e' he' ↦ hwe.trans_le (hT.le_weight hp he')⟩
  rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst, ← hwe]

/-- Deleting the cut-tree edges of weight below `k` leaves two vertices connected exactly when
they are locally `k`-edge-reachable in the original simple graph. -/
theorem reachable_deleteEdges_iff_simpleGraph_edgeReachability
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      G.IsEdgeReachable (k : ℕ∞) s t := by
  rw [hT.reachable_deleteEdges_iff,
    SimpleGraph.isEdgeReachable_iff_le_edgeReachability]
  by_cases hst : s = t
  · simp [hst]
  · simp only [hst, false_or]
    rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]
    exact_mod_cast Iff.rfl

/-- The global edge connectivity of a finite simple graph with at least two vertices is the
minimum weight of an edge in any unit flow-equivalent tree. The witness includes the
minimum-weight certificate. -/
theorem exists_edge_simpleGraph_edgeConnectivity_eq_weight [Nontrivial V]
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    ∃ u v, T.Adj u v ∧ (∀ e ∈ T.edgeSet, w s(u, v) ≤ w e) ∧
      G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  obtain ⟨u, v, huv, hmin, hpair⟩ := hT.exists_edge_weight_le_pairMinimumValue
  refine ⟨u, v, huv, hmin, le_antisymm ?_ ?_⟩
  · calc
      G.edgeConnectivity ≤ G.edgeReachability u v := G.edgeConnectivity_le_edgeReachability u v
      _ = ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity u v : ℕ) : ℕ∞) :=
        G.edgeReachability_eq_pairMinimumValue_unitCutCapacity huv.ne
      _ = (w s(u, v) : ℕ∞) := by rw [hT.weight_eq huv]
  · rw [G.edgeConnectivity_eq_iInf_edgeReachability]
    refine le_iInf fun x ↦ le_iInf fun y ↦ ?_
    by_cases hxy : x = y
    · subst y
      rw [G.edgeReachability_self]
      exact le_top
    · rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hxy]
      exact_mod_cast hpair x y hxy

end TauCeti.TerminalCut.IsFlowEquivalentTree

namespace TauCeti.TerminalCut.IsCutTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- A minimum-weight edge on a unit cut-tree path recovers a minimum simple-graph cut. Its unit
cut capacity equals the local edge reachability of the path endpoints. -/
theorem simpleGraph_edgeReachability_eq_unitCutCapacity_edgeSide
    (hT : IsCutTree G.unitCutCapacity T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v) :
    G.edgeReachability s t =
      ((G.unitCutCapacity (T.edgeSide u v) : ℕ) : ℕ∞) := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hcut.admissible.ne,
    hcut.pairMinimumValue_eq]

end TauCeti.TerminalCut.IsCutTree
