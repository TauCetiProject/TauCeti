/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Graph

/-!
# Cut trees for simple graphs

This file gives the unit-capacity Gomory--Hu theory directly on a finite simple graph. The
capacity of an unordered pair is one exactly on the graph's edges and zero elsewhere. A cut tree
for this capacity records the graph's native local edge reachability: the minimum weight on the
tree path between two distinct vertices is their local edge connectivity, and deleting a
minimum-weight path edge recovers a minimum cut in the original graph.

The results are stated on the original vertex type, rather than the vertex subtype of
`Graph.ofSimpleGraph G`. The comparison with the multigraph cut theory uses the canonical vertex
equivalence and preserves every cut side. The unit cut-tree interface and its path-weight,
threshold, cut-recovery, and global-connectivity proofs adapt
`TauCeti.Combinatorics.Network.MinimumCut.Graph`.

## Main results

* `SimpleGraph.exists_isUnitCutTree`: every nonempty finite simple graph has a unit cut tree.
* `SimpleGraph.edgeReachability_eq_pairMinimumValue_unitPairCapacity`: unit pair cuts compute
  native local edge reachability between distinct vertices.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.reachable_deleteEdges_iff_simpleGraphEdgeReachability`:
  threshold components are the local edge-reachability classes.
* `TauCeti.TerminalCut.IsCutTree.simpleGraphEdgeReachability_eq_pairCutCapacity_edgeSide`: a
  minimum-weight path edge recovers a minimum cut in the simple graph.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.exists_edge_simpleGraphEdgeConnectivity_eq_weight`:
  for graphs with at least two vertices, global edge connectivity is the minimum tree-edge weight.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Every nonempty finite simple graph has a cut tree for unit edge capacities. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w := by
  exact TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity G.unitPairCapacity
    fun _ _ _ ↦ Nat.zero_le _

end SimpleGraph

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit-capacity simple-graph flow-equivalent tree, some edge on the path between distinct
vertices `s` and `t` has weight equal to `G.edgeReachability s t`. -/
theorem exists_weight_eq_simpleGraphEdgeReachability
    (hT : IsFlowEquivalentTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w)
    {s t : V} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_⟩
  rw [G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hst, ← hwe]

/-- Deleting the tree edges of weight below `k` leaves two vertices connected exactly when they
are natively `k`-edge-reachable. -/
theorem reachable_deleteEdges_iff_simpleGraphEdgeReachability
    (hT : IsFlowEquivalentTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w)
    (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      G.IsEdgeReachable k s t := by
  rw [hT.reachable_deleteEdges_iff]
  rw [G.isEdgeReachable_iff_le_edgeReachability]
  by_cases hst : s = t
  · simp [hst]
  · simp only [hst, false_or]
    rw [G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hst]
    exact_mod_cast Iff.rfl

end TauCeti.TerminalCut.IsFlowEquivalentTree

namespace TauCeti.TerminalCut.IsCutTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- A minimum-weight edge on a unit cut-tree path recovers a minimum simple-graph cut. Its unit
pair capacity equals native local edge reachability. -/
theorem simpleGraphEdgeReachability_eq_pairCutCapacity_edgeSide
    (hT : IsCutTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v) :
    G.edgeReachability s t =
      ((TauCeti.pairCutCapacity G.unitPairCapacity (T.edgeSide u v) : ℕ) : ℕ∞) := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  rw [G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hcut.admissible.ne,
    hcut.pairMinimumValue_eq]

end TauCeti.TerminalCut.IsCutTree

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- The global edge connectivity of a finite simple graph with at least two vertices is the
minimum weight of an edge in any unit-capacity flow-equivalent tree. The witness includes the
minimum-weight certificate. -/
theorem exists_edge_simpleGraphEdgeConnectivity_eq_weight [Nontrivial V]
    (hT : IsFlowEquivalentTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w) :
    ∃ u v, T.Adj u v ∧ (∀ e ∈ T.edgeSet, w s(u, v) ≤ w e) ∧
      G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  obtain ⟨u, v, huv, hmin, hvalue⟩ := hT.exists_edge_iInf_pairMinimumValue_eq_weight
    (Nat.castOrderEmbedding : ℕ ↪o ℕ∞).toOrderHom
  refine ⟨u, v, huv, hmin, ?_⟩
  rw [G.edgeConnectivity_eq_iInf_edgeReachability]
  have hreach (s t : V) :
      G.edgeReachability s t =
        ⨅ (_ : s ≠ t),
          ((TauCeti.TerminalCut.pairMinimumValue
            (TauCeti.pairCutCapacity G.unitPairCapacity) s t : ℕ) : ℕ∞) := by
    by_cases hst : s = t
    · subst t
      simp
    · simp [hst, G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hst]
  simp_rw [hreach]
  exact hvalue

end TauCeti.TerminalCut.IsFlowEquivalentTree
