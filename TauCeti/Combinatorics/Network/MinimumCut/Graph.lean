/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Menger.CutValue
public import TauCeti.Combinatorics.Network.MinimumCut.GomoryHu
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Cut trees for weighted multigraphs

This file specializes the Gomory--Hu theorem to pair capacities and weighted multigraphs.
For unit edge capacities, a cut tree records native multigraph edge reachability: the minimum
weight on the tree path between two actual vertices is their local edge connectivity, and a
minimum-weight tree edge recovers a minimum cut in the original vertex set.

Parallel edges contribute their multiplicities, loops contribute nothing, and zero capacities
are allowed. In particular, disconnected weighted graphs have zero-weight edges in every cut
tree joining vertices from different components.

## Main results

* `TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity`: pair capacities admit cut trees.
* `Graph.exists_isCutTree_edgeCutCapacity`: finite weighted multigraphs admit cut trees.
* `Graph.exists_isUnitCutTree`: finite multigraphs admit unit-capacity cut trees.
* `IsFlowEquivalentTree.reachable_deleteEdges_iff_edgeReachability`: threshold components of a
  unit flow-equivalent tree are the local edge-connectivity classes of the multigraph.
* `IsFlowEquivalentTree.exists_edge_edgeConnectivity_eq_weight`: the global edge connectivity is
  the minimum tree-edge weight.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
-/

public section

open Finset

namespace TauCeti.TerminalCut

variable {V K : Type*}

/-- Every nonnegative pair-capacity function on a nonempty finite vertex type has a cut tree. -/
theorem exists_isCutTree_pairCutCapacity [Fintype V] [Nonempty V]
    [AddCommMonoid K] [LinearOrder K] [IsOrderedCancelAddMonoid K]
    (c : Sym2 V → K) (hc : ∀ x y, x ≠ y → 0 ≤ c s(x, y)) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → K), IsCutTree (TauCeti.pairCutCapacity c) T w := by
  classical
  exact exists_isCutTree (TauCeti.isSymmSubmodular_pairCutCapacity c hc)

end TauCeti.TerminalCut

namespace Graph

variable {α β K : Type*} {G : Graph α β}

/-- Every finite weighted multigraph with nonnegative nonloop edge weights has a cut tree on its
actual vertices. Parallel edges retain their separate contributions, while loops are ignored by
the cut function. -/
theorem exists_isCutTree_edgeCutCapacity [Fintype V(G)] [Nonempty V(G)] [Fintype E(G)]
    [AddCommMonoid K] [LinearOrder K] [IsOrderedCancelAddMonoid K]
    (c : E(G) → K) (hc : ∀ e, ¬(G.edgeEnds e).IsDiag → 0 ≤ c e) :
    ∃ (T : SimpleGraph V(G)) (w : Sym2 V(G) → K),
      TauCeti.TerminalCut.IsCutTree (G.edgeCutCapacity c) T w := by
  classical
  exact TauCeti.TerminalCut.exists_isCutTree (G.isSymmSubmodular_edgeCutCapacity c hc)

/-- Every finite multigraph with a nonempty actual vertex set has a cut tree for unit edge
capacities. Thus parallel edges are counted with multiplicity. -/
theorem exists_isUnitCutTree [Fintype V(G)] [Nonempty V(G)] [Fintype E(G)] :
    ∃ (T : SimpleGraph V(G)) (w : Sym2 V(G) → ℕ),
      TauCeti.TerminalCut.IsCutTree (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w := by
  apply G.exists_isCutTree_edgeCutCapacity (fun _ ↦ (1 : ℕ))
  simp

end Graph

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open Graph SimpleGraph

variable {α β : Type*} {G : Graph α β} [Finite V(G)] [Fintype E(G)]
variable {T : SimpleGraph V(G)} {w : Sym2 V(G) → ℕ}

/-- On a unit-capacity multigraph flow-equivalent tree, some edge on every nontrivial tree path has
weight equal to the native local edge reachability of its endpoints. -/
theorem exists_weight_eq_edgeReachability
    (hT : IsFlowEquivalentTree (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w)
    {s t : V(G)} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_⟩
  rw [G.edgeReachability_eq_pairMinimumValue hst, ← hwe]

/-- Deleting the tree edges of weight below `k` leaves two actual vertices connected exactly when
they are equal or their native local edge reachability is at least `k`. -/
theorem reachable_deleteEdges_iff_edgeReachability
    (hT : IsFlowEquivalentTree (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w) (k : ℕ) {s t : V(G)} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      s = t ∨ (k : ℕ∞) ≤ G.edgeReachability s t := by
  rw [hT.reachable_deleteEdges_iff]
  by_cases hst : s = t
  · simp [hst]
  · simp only [hst, false_or]
    rw [G.edgeReachability_eq_pairMinimumValue hst]
    exact_mod_cast Iff.rfl

end TauCeti.TerminalCut.IsFlowEquivalentTree

namespace TauCeti.TerminalCut.IsCutTree

open Graph SimpleGraph

variable {α β : Type*} {G : Graph α β} [Fintype V(G)] [Fintype E(G)]
variable {T : SimpleGraph V(G)} {w : Sym2 V(G) → ℕ}

/-- A minimum-weight edge on a unit cut-tree path recovers a minimum multigraph cut, expressed as
a subset of the original actual vertices. Its unit cut capacity equals local edge reachability. -/
theorem edgeReachability_eq_edgeCutCapacity_edgeSide
    (hT : IsCutTree (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w)
    {s t u v : V(G)} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v) :
    G.edgeReachability s t =
      ((G.edgeCutCapacity (fun _ ↦ (1 : ℕ)) (T.edgeSide u v) : ℕ) : ℕ∞) := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  obtain ⟨hs', ht⟩ := TauCeti.TerminalCut.isAdmissible_singleton.mp hcut.admissible
  have hst : s ≠ t := fun h ↦ ht (h ▸ hs')
  rw [G.edgeReachability_eq_pairMinimumValue hst, hcut.pairMinimumValue_eq]

end TauCeti.TerminalCut.IsCutTree

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open Graph SimpleGraph

variable {α β : Type*} {G : Graph α β} [Finite V(G)] [Fintype E(G)]
variable {T : SimpleGraph V(G)} {w : Sym2 V(G) → ℕ}

/-- The global edge connectivity of a finite multigraph with at least two actual vertices is the
minimum weight of an edge in any unit-capacity flow-equivalent tree. -/
theorem exists_edge_edgeConnectivity_eq_weight [Nontrivial V(G)]
    (hT : IsFlowEquivalentTree (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w) :
    ∃ u v, T.Adj u v ∧ G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hT
    exact SimpleGraph.not_preconnected_bot hT.isTree.connected.preconnected
  obtain ⟨u, v, huv, hmin⟩ := T.exists_minimum_weight_edge hTne w
  refine ⟨u, v, huv, le_antisymm ?_ ?_⟩
  · calc
      G.edgeConnectivity ≤ G.edgeReachability u v :=
        G.edgeConnectivity_le_edgeReachability u.property v.property
      _ = ((TauCeti.TerminalCut.pairMinimumValue
          (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) u v : ℕ) : ℕ∞) :=
        G.edgeReachability_eq_pairMinimumValue huv.ne
      _ = (w s(u, v) : ℕ∞) := by rw [hT.weight_eq huv]
  · rw [G.edgeConnectivity_eq_iInf_edgeReachability]
    refine le_iInf fun x ↦ le_iInf fun hx ↦ le_iInf fun y ↦ le_iInf fun hy ↦ ?_
    let sx : V(G) := ⟨x, hx⟩
    let sy : V(G) := ⟨y, hy⟩
    by_cases hxy : sx = sy
    · have hxy' : x = y := congrArg Subtype.val hxy
      subst y
      rw [G.edgeReachability_self hx]
      exact le_top
    · obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path sx sy
      obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hxy hp
      rw [G.edgeReachability_eq_pairMinimumValue hxy]
      exact_mod_cast (hmin e (p.edges_subset_edgeSet he)).trans_eq hwe

end TauCeti.TerminalCut.IsFlowEquivalentTree

/-!
## A disconnected weighted graph

The graph below has one edge joining `0` and `1`, while `2` is isolated. Every unit-capacity cut
tree therefore has a zero-weight edge on the tree path from `2` to `0`.
-/

namespace TauCeti.TerminalCut

open Graph SimpleGraph

private abbrev disconnectedWeightedGraph : Graph (Fin 3) (Sym2 (Fin 3)) :=
  Graph.ofSimpleGraph (SimpleGraph.fromEdgeSet {s(0, 1)})

private noncomputable instance : Fintype V(disconnectedWeightedGraph) := Fintype.ofFinite _

private noncomputable instance : Fintype E(disconnectedWeightedGraph) := Fintype.ofFinite _

private def disconnectedWeightedGraphVertex (i : Fin 3) : V(disconnectedWeightedGraph) :=
  ⟨i, by simp [disconnectedWeightedGraph]⟩

private theorem disconnectedWeightedGraph_isolatedCut :
    disconnectedWeightedGraph.edgeCutCapacity (fun _ ↦ (1 : ℕ))
      {disconnectedWeightedGraphVertex 2} = 0 := by
  rw [Graph.edgeCutCapacity_one, Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨u, v, hlink, hu, -⟩ := Graph.mem_edgeCut_iff.mp he
  obtain ⟨u', hu', rfl⟩ := hu
  have huEq : u' = disconnectedWeightedGraphVertex 2 := by simpa using hu'
  subst u'
  rw [Graph.ofSimpleGraph_isLink, SimpleGraph.edgeSet_fromEdgeSet] at hlink
  have he01 : e = s(0, 1) := hlink.2.1
  have h := hlink.1.symm.trans he01
  fin_cases v <;> simp [disconnectedWeightedGraphVertex] at h

/-- A unit-capacity cut tree for a graph with one edge and one isolated vertex contains a
zero-weight edge. -/
example (T : SimpleGraph V(disconnectedWeightedGraph))
    (w : Sym2 V(disconnectedWeightedGraph) → ℕ)
    (hT : IsCutTree (disconnectedWeightedGraph.edgeCutCapacity fun _ ↦ (1 : ℕ)) T w) :
    ∃ e ∈ T.edgeSet, w e = 0 := by
  let v0 := disconnectedWeightedGraphVertex 0
  let v2 := disconnectedWeightedGraphVertex 2
  have hv20 : v2 ≠ v0 := by
    intro h
    have := congrArg Subtype.val h
    simp [v0, v2, disconnectedWeightedGraphVertex] at this
  have hpair : pairMinimumValue
      (disconnectedWeightedGraph.edgeCutCapacity fun _ ↦ (1 : ℕ)) v2 v0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      pairMinimumValue (disconnectedWeightedGraph.edgeCutCapacity fun _ ↦ (1 : ℕ)) v2 v0 ≤
          disconnectedWeightedGraph.edgeCutCapacity (fun _ ↦ (1 : ℕ)) {v2} :=
        pairMinimumValue_le _ (mem_singleton_self v2) (by simpa using hv20.symm)
      _ = 0 := disconnectedWeightedGraph_isolatedCut
  obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path v2 v0
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hv20 hp
  exact ⟨e, p.edges_subset_edgeSet he, hwe.trans hpair⟩

end TauCeti.TerminalCut
