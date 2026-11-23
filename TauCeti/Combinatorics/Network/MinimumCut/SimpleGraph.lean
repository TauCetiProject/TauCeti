/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Graph
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Cut trees for simple graphs

This file gives the unit-capacity Gomory--Hu theory directly on a finite simple graph. The
capacity of an unordered pair is one exactly on the graph's edges and zero elsewhere. A cut tree
for this capacity records the graph's native local edge reachability: the minimum weight on the
tree path between two vertices is their local edge connectivity, and deleting a minimum-weight
path edge recovers a minimum cut in the original graph.

The results are stated on the original vertex type, rather than the vertex subtype of
`Graph.ofSimpleGraph G`. The comparison with the multigraph cut theory uses the canonical vertex
equivalence and preserves every cut side.

## Main results

* `SimpleGraph.exists_isUnitCutTree`: every nonempty finite simple graph has a unit cut tree.
* `SimpleGraph.edgeReachability_eq_pairMinimumValue_unitPairCapacity`: unit pair cuts compute
  native local edge reachability.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.reachable_deleteEdges_iff_simpleGraphEdgeReachability`:
  threshold components are the local edge-reachability classes.
* `TauCeti.TerminalCut.IsCutTree.simpleGraphEdgeReachability_eq_pairCutCapacity_edgeSide`: a
  minimum-weight path edge recovers a minimum cut in the simple graph.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.exists_edge_simpleGraphEdgeConnectivity_eq_weight`:
  global edge connectivity is the minimum tree-edge weight.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

open Classical in
/-- The unit pair capacity of a simple graph: one on each edge and zero on every non-edge,
including diagonal pairs. -/
noncomputable def unitPairCapacity (e : Sym2 V) : ℕ :=
  if e ∈ G.edgeSet then 1 else 0

@[simp]
theorem unitPairCapacity_eq_one_iff {e : Sym2 V} :
    G.unitPairCapacity e = 1 ↔ e ∈ G.edgeSet := by
  classical
  simp [unitPairCapacity]

@[simp]
theorem unitPairCapacity_eq_zero_iff {e : Sym2 V} :
    G.unitPairCapacity e = 0 ↔ e ∉ G.edgeSet := by
  classical
  simp [unitPairCapacity]

/-- Every nonempty finite simple graph has a cut tree for unit edge capacities. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w := by
  exact TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity G.unitPairCapacity
    fun _ _ _ ↦ Nat.zero_le _

private theorem edgeCutCapacity_unit_eq_pairCutCapacity [Fintype V] (S : Finset V) :
    (Graph.ofSimpleGraph G).edgeCutCapacity (fun _ ↦ (1 : ℕ))
        (G.toOfSimpleGraphFinset S) =
      TauCeti.pairCutCapacity G.unitPairCapacity S := by
  have hcap : G.ofSimpleGraphCapacity G.unitPairCapacity = fun _ ↦ (1 : ℕ) := by
    funext e
    have he : e.val ∈ G.edgeSet := by
      simpa [Graph.edgeSet_ofSimpleGraph] using e.property
    simp [unitPairCapacity, he]
  rw [← hcap]
  exact G.edgeCutCapacity_eq_pairCutCapacity G.unitPairCapacity (by
    intro p _ hnot
    simp [unitPairCapacity, hnot]) S

/-- For distinct vertices of a finite simple graph, native local edge reachability is the
minimum unit pair-cut value, viewed in `ℕ∞`. -/
theorem edgeReachability_eq_pairMinimumValue_unitPairCapacity [Fintype V] {s t : V}
    (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity G.unitPairCapacity) s t : ℕ) : ℕ∞) := by
  let e : V ≃ (Graph.ofSimpleGraph G).vertexSet :=
    Equiv.ofBijective G.toOfSimpleGraphVertex ⟨fun {x y} hxy ↦ by
      simpa using congrArg Subtype.val hxy, fun x ↦
        ⟨x.val, Subtype.ext (G.toOfSimpleGraphVertex_val x.val)⟩⟩
  have heval (x : V) : (e x).val = x := by
    change (G.toOfSimpleGraphVertex x).val = x
    exact G.toOfSimpleGraphVertex_val x
  have hemap (S : Finset V) :
      S.map e.toEmbedding = G.toOfSimpleGraphFinset S := by
    ext x
    have hx : G.toOfSimpleGraphVertex x.val = x :=
      Subtype.ext (G.toOfSimpleGraphVertex_val x.val)
    rw [← hx, Finset.mem_map_equiv]
    have he : e x.val = G.toOfSimpleGraphVertex x.val := rfl
    rw [← he, Equiv.symm_apply_apply]
    rw [he, G.mem_toOfSimpleGraphFinset]
  have hst' : e s ≠ e t := e.injective.ne hst
  have hmulti := (Graph.ofSimpleGraph G).edgeReachability_eq_pairMinimumValue hst'
  rw [Graph.edgeReachability_ofSimpleGraph, heval s, heval t] at hmulti
  have hmap := TauCeti.TerminalCut.pairMinimumValue_map
    (f := TauCeti.pairCutCapacity G.unitPairCapacity) e
    ((Graph.ofSimpleGraph G).edgeCutCapacity fun _ ↦ (1 : ℕ))
    (fun S ↦ by rw [hemap]; exact G.edgeCutCapacity_unit_eq_pairCutCapacity S) s t
  exact hmulti.trans (congrArg (Nat.cast : ℕ → ℕ∞) hmap)

end SimpleGraph

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit-capacity simple-graph flow-equivalent tree, some edge on every nontrivial tree path
has weight equal to the native local edge reachability of its endpoints. -/
theorem exists_weight_eq_simpleGraphEdgeReachability
    (hT : IsFlowEquivalentTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w)
    {s t : V} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_⟩
  rw [G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hst, ← hwe]

/-- Deleting the tree edges of weight below `k` leaves two vertices connected exactly when they
are equal or their native local edge reachability is at least `k`. -/
theorem reachable_deleteEdges_iff_simpleGraphEdgeReachability
    (hT : IsFlowEquivalentTree (TauCeti.pairCutCapacity G.unitPairCapacity) T w)
    (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      s = t ∨ (k : ℕ∞) ≤ G.edgeReachability s t := by
  rw [hT.reachable_deleteEdges_iff]
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
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hT
    exact SimpleGraph.not_preconnected_bot hT.isTree.connected.preconnected
  obtain ⟨u, v, huv, hmin⟩ := T.exists_minimum_weight_edge hTne w
  refine ⟨u, v, huv, hmin, le_antisymm ?_ ?_⟩
  · calc
      G.edgeConnectivity ≤ G.edgeReachability u v :=
        G.edgeConnectivity_le_edgeReachability u v
      _ = ((TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity G.unitPairCapacity) u v : ℕ) : ℕ∞) :=
        G.edgeReachability_eq_pairMinimumValue_unitPairCapacity huv.ne
      _ = (w s(u, v) : ℕ∞) := by rw [hT.weight_eq huv]
  · rw [G.edgeConnectivity_eq_iInf_edgeReachability]
    refine le_iInf fun x ↦ le_iInf fun y ↦ ?_
    by_cases hxy : x = y
    · subst y
      rw [G.edgeReachability_self]
      exact le_top
    · obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path x y
      obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hxy hp
      rw [G.edgeReachability_eq_pairMinimumValue_unitPairCapacity hxy]
      exact_mod_cast (hmin e (p.edges_subset_edgeSet he)).trans_eq hwe

end TauCeti.TerminalCut.IsFlowEquivalentTree
