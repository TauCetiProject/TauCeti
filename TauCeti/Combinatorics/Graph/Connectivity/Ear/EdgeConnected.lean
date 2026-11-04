/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity

import Mathlib.Data.Set.Card

/-!
# Ear decompositions and `2`-edge-connectivity of multigraphs

This file proves the ear-decomposition characterization of `2`-edge-connected multigraphs. Every
allowed initial graph of an ear decomposition (a single actual vertex or a cycle) is connected and
`2`-edge-connected, and adjoining either an open or a closed ear preserves connectedness and
`2`-edge-connectivity without any finiteness hypothesis. Conversely, if `G` is `2`-edge-connected
and `H < G` is a proper subgraph with at least one actual vertex, then `G` admits an open or closed
ear over `H` (`Graph.IsEdgeConnected.nonempty_ear`); when `E(G)` is finite, iterating ear addition
completes any partial ear decomposition `G.EarDecomposition H` to a full ear decomposition
`G.EarDecomposition G` (`Graph.EarDecomposition.extend`).

Loops and parallel edges are preserved throughout: an unused loop at a vertex of `H` is added as a
one-edge closed ear (`Graph.Ear.ofIsLoopAt`), and an unused parallel edge between distinct vertices
of `H` is added as a one-edge open ear (`Graph.Ear.ofIsLink`), while an initial cycle may itself be
a one-edge loop or a two-edge parallel cycle. Normalizing an initial cycle into a single-vertex
start followed by one closed ear (`Graph.EarDecomposition.toVertexStart`) makes general ear
decompositions equivalent to vertex-started ones. Specializing to `Graph.ofSimpleGraph` recovers the
corresponding `2`-edge-connectivity criterion for simple graphs.

The theorem goes back to H. E. Robbins (1939), *A theorem on graphs, with an application to a
problem of traffic control*, Amer. Math. Monthly 46, 281–283; the presentation follows R. Diestel,
*Graph Theory*, Chapter 3, adapted to edge-labelled multigraphs.

## Main declarations

* `Graph.Ear.connected_add`, `Graph.Ear.isEdgeConnected_two_add`: adjoining an ear preserves
  connectedness and `2`-edge-connectivity.
* `Graph.EarDecomposition.connected`, `Graph.EarDecomposition.isEdgeConnected_two`: any graph
  admitting an ear decomposition in `G` is connected and `2`-edge-connected.
* `Graph.IsEdgeConnected.nonempty_ear`: in a `2`-edge-connected multigraph, every proper subgraph
  with an actual vertex admits an ear.
* `Graph.EarDecomposition.extend`: with finitely many actual edges, any partial ear decomposition
  in a `2`-edge-connected multigraph extends to an ear decomposition of the whole multigraph.
* `Graph.isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle`,
  `Graph.isEdgeConnected_two_iff_nonempty_earDecomposition`: a multigraph with an actual vertex and
  finitely many actual edges is `2`-edge-connected if and only if it admits a (vertex-started) ear
  decomposition.
* `SimpleGraph.isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle`,
  `SimpleGraph.isEdgeConnected_two_iff_nonempty_earDecomposition`: the corresponding simple-graph
  characterizations via `Graph.ofSimpleGraph`.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-! ### Soundness of ear decompositions -/

namespace EarStart

/-- Every allowed initial graph of an ear decomposition is connected. -/
theorem connected : ∀ _start : G.EarStart H, H.Connected
  | .vertex v =>
      connected_iff_forall_reachable.mpr
        ⟨⟨v.1, by simp⟩, fun x y hx hy ↦ by
          simp only [vertexSet_noEdge, mem_singleton_iff] at hx hy
          subst hx hy
          exact Reachable.refl (by simp)⟩
  | .cycle walk _ => walk.connected_walkGraph

/-- Every allowed initial graph of an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two : ∀ _start : G.EarStart H, H.IsEdgeConnected 2
  | .vertex _ => IsEdgeConnected.of_subsingleton (by simp [Set.subsingleton_singleton])
  | .cycle _ isCycle => isCycle.isEdgeConnected_two_walkGraph

end EarStart

namespace Ear

/-- Adjoining an ear to a connected subgraph yields a connected subgraph. -/
theorem connected_add (ear : G.Ear H) (hH : H.Connected) : ear.add.Connected :=
  ear.compatible.connected_union hH ear.toWalk.2.2.connected_walkGraph
    ⟨ear.toWalk.1, ear.start_mem_base, by simp [Ear.vertexSet_toGraph]⟩

/-- Adjoining an ear to a `2`-edge-connected subgraph yields a `2`-edge-connected subgraph. -/
theorem isEdgeConnected_two_add (ear : G.Ear H) (hH : H.IsEdgeConnected 2) :
    ear.add.IsEdgeConnected 2 := by
  have hconnH : H.Connected := hH.connected two_ne_zero ear.base_nonempty
  have hconnAdd : ear.add.Connected := ear.connected_add hconnH
  refine (isEdgeConnected_two_iff_connected_and_forall_not_isBridge hconnAdd.nonempty).mpr
    ⟨hconnAdd, fun e he ↦ ?_⟩
  have hemem : e ∈ E(H) ∨ e ∈ E(ear.toGraph) := by
    simpa only [Ear.edgeSet_add, mem_union] using he.mem_edgeSet
  rcases hemem with heH | heEar
  · exact (isEdgeConnected_two_iff_forall_reachable_and_forall_not_isBridge.mp hH).2 e
      (he.anti_of_mem ear.base_le_add heH)
  · -- Join the ear's endpoints in `H` to form a closed trail in `ear.add` containing `e`.
    have heEdges : e ∈ ear.toWalk.2.2.edges := by simpa [Ear.edgeSet_toGraph] using heEar
    obtain ⟨q, hq⟩ := (hconnH.reachable ear.end_mem_base ear.start_mem_base).exists_isPath
    let w' := ear.toWalk.2.2.transfer ear.add_le fun _ hf ↦ ear.mem_edgeSet_add_of_mem_edges hf
    let q' := q.mapLe ear.base_le_add
    have htrail : (w'.append q').IsTrail := by
      rw [Walk.isTrail_def, Walk.edges_append, Walk.edges_transfer, Walk.edges_mapLe_eq_edges]
      exact List.nodup_append.mpr ⟨(Walk.isTrail_def _).mp ear.isTrail,
        (Walk.isTrail_def q).mp hq.isTrail,
        fun f hfw f' hfq hff' ↦ ear.edge_notMem_base hfw (hff' ▸ q.edges_subset_edgeSet hfq)⟩
    have heAppend : e ∈ (w'.append q').edges := by
      rw [Walk.edges_append, Walk.edges_transfer]
      exact List.mem_append_left _ heEdges
    exact he.notMem_edges_of_isTrail htrail heAppend

end Ear

namespace EarDecomposition

/-- Every stage graph of an ear decomposition is connected. -/
theorem connected_graphAfter (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.graphAfter i).Connected := by
  induction i using Fin.induction with
  | zero => exact d.start.connected
  | succ k ih =>
      rw [d.graphAfter_succ]
      exact (d.earAt k).2.connected_add ((d.earAt_fst k).symm ▸ ih)

/-- The final graph of any ear decomposition is connected. -/
theorem connected (d : G.EarDecomposition H) : H.Connected :=
  d.graphAfter_last ▸ d.connected_graphAfter (Fin.last d.length)

/-- Every stage graph of an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two_graphAfter (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.graphAfter i).IsEdgeConnected 2 := by
  induction i using Fin.induction with
  | zero => exact d.start.isEdgeConnected_two
  | succ k ih =>
      rw [d.graphAfter_succ]
      exact (d.earAt k).2.isEdgeConnected_two_add ((d.earAt_fst k).symm ▸ ih)

/-- The final graph of any ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two (d : G.EarDecomposition H) : H.IsEdgeConnected 2 :=
  d.graphAfter_last ▸ d.isEdgeConnected_two_graphAfter (Fin.last d.length)

end EarDecomposition

/-! ### Finding a next ear and completing partial decompositions -/

/-- In a `2`-edge-connected multigraph, every proper subgraph with at least one actual vertex admits
an open or closed ear. -/
theorem IsEdgeConnected.nonempty_ear (hG : G.IsEdgeConnected 2) {H : Graph α β} (hHG : H < G)
    (hH : V(H).Nonempty) : Nonempty (G.Ear H) := by
  have hconnG : G.Connected := hG.connected two_ne_zero (hH.mono hHG.le.vertexSet_mono)
  have hnobridge : ∀ e, ¬ G.IsBridge e :=
    (isEdgeConnected_two_iff_forall_reachable_and_forall_not_isBridge.mp hG).2
  by_cases hVeq : V(H) = V(G)
  · -- Case 1: `H` already spans `V(G)`, so `E(G) \ E(H)` has a link with both ends in `V(H)`.
    have hEne : E(H) ≠ E(G) := fun hEeq ↦
      hHG.ne ((Compatible.of_le_le hHG.le le_rfl).ext hVeq hEeq)
    obtain ⟨e₀, he₀G, he₀H⟩ :=
      exists_of_ssubset (ssubset_of_subset_of_ne hHG.le.edgeSet_mono hEne)
    obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he₀G
    exact Ear.nonempty_of_isLink hHG.le hl (hVeq.symm ▸ hl.left_mem) (hVeq.symm ▸ hl.right_mem) he₀H
  · -- Case 2: `V(H) ⊂ V(G)`; pick a cut edge `e₀` leaving `V(H)` and return in `G - {e₀}`
    -- using bridgelessness of `e₀`.
    obtain ⟨u, huH⟩ := hH
    obtain ⟨w, hwG, hwH⟩ :=
      exists_of_ssubset (ssubset_of_subset_of_ne hHG.le.vertexSet_mono hVeq)
    obtain ⟨e₀, he₀cut⟩ :=
      (hconnG.reachable (hHG.le.vertexSet_mono huH) hwG).edgeCut_nonempty huH hwH
    obtain ⟨x, y, hl, hxH, hyH⟩ := mem_edgeCut_iff.mp he₀cut
    have hxy : (G.deleteEdges {e₀}).Reachable x y := by
      simpa [hl.isBridge_iff_not_reachable_deleteEdges] using hnobridge e₀
    exact Ear.nonempty_of_isLink_reachable_deleteEdges hHG.le hl hxH hyH hxH hxy.symm

namespace EarDecomposition

private theorem ncard_sdiff_add_lt [Finite E(G)] {H : Graph α β} (ear : G.Ear H) :
    (E(G) \ E(ear.add)).ncard < (E(G) \ E(H)).ncard :=
  Set.ncard_lt_ncard ear.sdiff_edgeSet_add_ssubset (Set.toFinite E(G)).sdiff

open Classical in
/-- Complete any partial ear decomposition in a `2`-edge-connected multigraph with finitely many
actual edges to an ear decomposition of the whole multigraph. -/
noncomputable def extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : G.EarDecomposition G :=
  if h : H = G then
    d.copy h
  else
    let ear : G.Ear H :=
      Classical.choice (hG.nonempty_ear (lt_of_le_of_ne d.final_le h) d.nonempty)
    (d.snoc ear).extend hG
termination_by (E(G) \ E(H)).ncard
decreasing_by
  simpa only [← Ear.edgeSet_toGraph, ← Ear.edgeSet_add] using ncard_sdiff_add_lt _

/-- Completing a partial ear decomposition preserves its initial graph. -/
theorem initial_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : (d.extend hG).initial = d.initial := by
  rw [extend]
  split_ifs with h
  · exact d.initial_copy h
  · rw [initial_extend, d.initial_snoc]
termination_by (E(G) \ E(H)).ncard
decreasing_by
  simpa only [← Ear.edgeSet_toGraph, ← Ear.edgeSet_add] using ncard_sdiff_add_lt _

@[simp]
theorem start_isCycle_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : (d.extend hG).start.IsCycle ↔ d.start.IsCycle := by
  have hdef := extend.eq_1 hG d
  split_ifs at hdef with h
  · rw [hdef, d.start_isCycle_copy h]
  · rw [hdef, start_isCycle_extend, d.start_isCycle_snoc]
termination_by (E(G) \ E(H)).ncard
decreasing_by
  simpa only [← Ear.edgeSet_toGraph, ← Ear.edgeSet_add] using ncard_sdiff_add_lt _

end EarDecomposition

/-- Build an ear decomposition of a `2`-edge-connected multigraph with finitely many actual edges
starting from a prescribed actual vertex. -/
noncomputable def IsEdgeConnected.earDecompositionOfVertex [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (v : V(G)) : G.EarDecomposition G :=
  (EarDecomposition.vertex v).extend hG

/-- The ear decomposition built from a prescribed actual vertex has that vertex as initial graph. -/
theorem IsEdgeConnected.initial_earDecompositionOfVertex [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (v : V(G)) : (hG.earDecompositionOfVertex v).initial = Graph.noEdge {v.1} β := by
  rw [earDecompositionOfVertex, EarDecomposition.initial_extend, EarDecomposition.initial_vertex]

@[simp]
theorem IsEdgeConnected.not_start_isCycle_earDecompositionOfVertex [Finite E(G)]
    (hG : G.IsEdgeConnected 2) (v : V(G)) :
    ¬ (hG.earDecompositionOfVertex v).start.IsCycle := by
  rw [earDecompositionOfVertex, EarDecomposition.start_isCycle_extend]
  exact EarDecomposition.not_start_isCycle_vertex v

/-- Build an ear decomposition of a `2`-edge-connected multigraph with finitely many actual edges
starting from a prescribed cycle. -/
noncomputable def IsEdgeConnected.earDecompositionOfCycle [Finite E(G)] (hG : G.IsEdgeConnected 2)
    {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) : G.EarDecomposition G :=
  (EarDecomposition.cycle walk isCycle).extend hG

/-- The ear decomposition built from a prescribed cycle has its traced graph as initial graph. -/
theorem IsEdgeConnected.initial_earDecompositionOfCycle [Finite E(G)] (hG : G.IsEdgeConnected 2)
    {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (hG.earDecompositionOfCycle walk isCycle).initial = G.walkGraph walk := by
  rw [earDecompositionOfCycle, EarDecomposition.initial_extend, EarDecomposition.initial_cycle]

@[simp]
theorem IsEdgeConnected.start_isCycle_earDecompositionOfCycle [Finite E(G)]
    (hG : G.IsEdgeConnected 2) {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (hG.earDecompositionOfCycle walk isCycle).start.IsCycle := by
  rw [earDecompositionOfCycle, EarDecomposition.start_isCycle_extend]
  exact EarDecomposition.start_isCycle_cycle walk isCycle

/-! ### Ear characterizations of `2`-edge-connectivity -/

/-- **Ear characterization of `2`-edge-connected multigraphs** (vertex-started form). A multigraph
with at least one actual vertex and finitely many actual edges is `2`-edge-connected if and only if
it admits an ear decomposition starting from a single vertex. -/
theorem isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle [Finite E(G)]
    (hV : V(G).Nonempty) :
    G.IsEdgeConnected 2 ↔ ∃ d : G.EarDecomposition G, ¬ d.start.IsCycle :=
  ⟨fun hG ↦
    let ⟨x, hx⟩ := hV
    ⟨hG.earDecompositionOfVertex ⟨x, hx⟩, hG.not_start_isCycle_earDecompositionOfVertex _⟩,
   fun ⟨d, _⟩ ↦ d.isEdgeConnected_two⟩

/-- **Ear characterization of `2`-edge-connected multigraphs**. A multigraph with at least one
actual vertex and finitely many actual edges is `2`-edge-connected if and only if it admits an ear
decomposition. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition [Finite E(G)] (hV : V(G).Nonempty) :
    G.IsEdgeConnected 2 ↔ Nonempty (G.EarDecomposition G) := by
  rw [nonempty_earDecomposition_iff_exists_not_isCycle,
    isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle hV]

/-- A multigraph with finitely many actual edges is connected and bridgeless if and only if it
admits an ear decomposition. Unlike `isEdgeConnected_two_iff_nonempty_earDecomposition`, no separate
vertex-nonemptiness assumption is needed because both sides imply `V(G).Nonempty`. -/
theorem connected_and_forall_not_isBridge_iff_nonempty_earDecomposition [Finite E(G)] :
    (G.Connected ∧ ∀ e, ¬ G.IsBridge e) ↔ Nonempty (G.EarDecomposition G) := by
  constructor
  · rintro ⟨hconn, hnb⟩
    exact (isEdgeConnected_two_iff_nonempty_earDecomposition hconn.nonempty).mp
      ((isEdgeConnected_two_iff_connected_and_forall_not_isBridge hconn.nonempty).mpr ⟨hconn, hnb⟩)
  · rintro ⟨d⟩
    exact (isEdgeConnected_two_iff_connected_and_forall_not_isBridge d.nonempty).mp
      d.isEdgeConnected_two

end Graph

namespace SimpleGraph

variable {α : Type u}

/-- **Ear characterization of `2`-edge-connected simple graphs** (vertex-started form). A simple
graph on a nonempty vertex type with finitely many edges is `2`-edge-connected if and only if
`Graph.ofSimpleGraph H` admits an ear decomposition starting from a single vertex. -/
theorem isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle (H : SimpleGraph α)
    [Finite H.edgeSet] [Nonempty α] :
    H.IsEdgeConnected 2 ↔
      ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H),
        ¬ d.start.IsCycle := by
  have : Finite (Graph.ofSimpleGraph H).edgeSet := inferInstanceAs (Finite H.edgeSet)
  rw [← Nat.cast_ofNat, ← Graph.isEdgeConnected_ofSimpleGraph_iff,
    Graph.isEdgeConnected_two_iff_exists_earDecomposition_not_isCycle Set.univ_nonempty]

/-- **Ear characterization of `2`-edge-connected simple graphs**. A simple graph on a nonempty
vertex type with finitely many edges is `2`-edge-connected if and only if `Graph.ofSimpleGraph H`
admits an ear decomposition. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition (H : SimpleGraph α)
    [Finite H.edgeSet] [Nonempty α] :
    H.IsEdgeConnected 2 ↔
      Nonempty ((Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) := by
  have : Finite (Graph.ofSimpleGraph H).edgeSet := inferInstanceAs (Finite H.edgeSet)
  rw [← Nat.cast_ofNat, ← Graph.isEdgeConnected_ofSimpleGraph_iff,
    Graph.isEdgeConnected_two_iff_nonempty_earDecomposition Set.univ_nonempty]

end SimpleGraph
