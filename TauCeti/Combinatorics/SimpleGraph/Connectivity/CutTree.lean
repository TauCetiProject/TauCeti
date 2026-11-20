/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Graph
import TauCeti.Combinatorics.SimpleGraph.Finite

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
-/

public section

open Finset
open scoped Graph

namespace SimpleGraph

variable {V : Type*}

/-- The unit capacity of a vertex cut in a simple graph. Every graph edge crossing the cut
contributes one, while nonedges and diagonal pairs contribute zero. -/
noncomputable def unitCutCapacity [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ 1) S

/-- The defining pair-capacity formula for the unit cut capacity of a simple graph. -/
theorem unitCutCapacity_def [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    G.unitCutCapacity S =
      TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ 1) S :=
  (rfl)

/-- Exchanging the two sides of a cut does not change its unit capacity. -/
@[simp]
theorem unitCutCapacity_compl [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    G.unitCutCapacity Sᶜ = G.unitCutCapacity S := by
  rw [unitCutCapacity_def, unitCutCapacity_def, TauCeti.pairCutCapacity_compl]

/-- The native unit cut capacity agrees with unit edge capacity on the multigraph realization of
the simple graph. -/
theorem unitCutCapacity_eq_edgeCutCapacity [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    G.unitCutCapacity S =
      (Graph.ofSimpleGraph G).edgeCutCapacity (fun _ ↦ (1 : ℕ))
        (G.toOfSimpleGraphFinset S) := by
  classical
  have hsupp : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet →
      G.edgeSet.indicator (fun _ ↦ (1 : ℕ)) p = 0 := by
    intro p _ hp
    exact Set.indicator_of_notMem hp _
  rw [unitCutCapacity_def, ← G.edgeCutCapacity_eq_pairCutCapacity _ hsupp S]
  congr 1
  funext e
  rw [G.ofSimpleGraphCapacity_apply]
  exact Set.indicator_of_mem e.2 _

/-- Unit cut capacity is the number of actual simple-graph edges crossing the cut. -/
theorem unitCutCapacity_eq_ncard [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    G.unitCutCapacity S =
      (G.edgeSet ∩ {e | e.Crosses (S : Set V)}).ncard := by
  classical
  rw [unitCutCapacity_def, TauCeti.pairCutCapacity_def]
  let C := G.edgeSet ∩ {e | e.Crosses (S : Set V)}
  calc
    (∑ p : Sym2 V, if p.Crosses (S : Set V) then G.edgeSet.indicator (fun _ ↦ 1) p else 0) =
        #(Finset.univ.filter fun p : Sym2 V ↦ p ∈ C) := by
      rw [card_filter]
      apply sum_congr rfl
      intro p _
      by_cases hpG : p ∈ G.edgeSet <;> by_cases hpS : p.Crosses (S : Set V) <;>
        simp [C, hpG, hpS]
    _ = C.ncard := by
      rw [Set.ncard_eq_toFinset_card]
      congr 1
      ext p
      simp [C]

/-- For distinct vertices, simple-graph edge reachability is the minimum unit cut value, viewed
in `ℕ∞`. -/
theorem edgeReachability_eq_pairMinimumValue_unitCutCapacity [Fintype V] (G : SimpleGraph V)
    {s t : V}
    (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  let e : V ≃ V(Graph.ofSimpleGraph G) :=
    { toFun := fun x ↦ ⟨x, by simp⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext rfl }
  have he (S : Finset V) :
      (Graph.ofSimpleGraph G).edgeCutCapacity (fun _ ↦ (1 : ℕ))
          (S.map e.toEmbedding) = G.unitCutCapacity S := by
    rw [show S.map e.toEmbedding = G.toOfSimpleGraphFinset S by
      ext x
      have hx : x = G.toOfSimpleGraphVertex x.1 :=
        Subtype.ext (G.toOfSimpleGraphVertex_val x.1).symm
      rw [hx]
      simp [e]]
    exact (G.unitCutCapacity_eq_edgeCutCapacity S).symm
  have hst' : e s ≠ e t := e.injective.ne hst
  have hreach :=
    (Graph.ofSimpleGraph G).edgeReachability_eq_pairMinimumValue (s := e s) (t := e t) hst'
  have hmin := TauCeti.TerminalCut.pairMinimumValue_map G.unitCutCapacity e
    ((Graph.ofSimpleGraph G).edgeCutCapacity fun _ ↦ (1 : ℕ)) he s t
  simpa [e, Graph.edgeReachability_ofSimpleGraph] using hreach.trans (congrArg (↑· : ℕ → ℕ∞) hmin)

/-- Every nonempty finite simple graph has a cut tree for unit edge capacities. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree G.unitCutCapacity T w := by
  classical
  apply TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity
  intro x y _
  simp

end SimpleGraph

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit cut tree of a simple graph, some edge on every nontrivial tree path has weight equal
to the local edge reachability of its endpoints. -/
theorem exists_weight_eq_simpleGraph_edgeReachability
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w)
    {s t : V} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_⟩
  rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst, ← hwe]

/-- Deleting the cut-tree edges of weight below `k` leaves two vertices connected exactly when
they are equal or are locally `k`-edge-reachable in the original simple graph. -/
theorem reachable_deleteEdges_iff_simpleGraph_edgeReachability
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      s = t ∨ (k : ℕ∞) ≤ G.edgeReachability s t := by
  rw [hT.reachable_deleteEdges_iff]
  by_cases hst : s = t
  · simp [hst]
  · simp only [hst, false_or]
    rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]
    exact_mod_cast Iff.rfl

/-- The global edge connectivity of a finite simple graph with at least two vertices is the
minimum weight of an edge in any unit flow-equivalent tree. -/
theorem exists_edge_simpleGraph_edgeConnectivity_eq_weight [Nontrivial V]
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    ∃ u v, T.Adj u v ∧ G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hT
    exact SimpleGraph.not_preconnected_bot hT.isTree.connected.preconnected
  obtain ⟨u, v, huv, hmin⟩ := T.exists_minimum_weight_edge hTne w
  refine ⟨u, v, huv, le_antisymm ?_ ?_⟩
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
    · obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path x y
      obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hxy hp
      rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hxy]
      exact_mod_cast (hmin e (p.edges_subset_edgeSet he)).trans_eq hwe

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
