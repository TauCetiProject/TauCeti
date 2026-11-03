/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.Graph.EdgeEnds

/-!
# Whitney's inequality for multigraphs

Whitney's inequality says that vertex connectivity is at most edge connectivity. This file
extends the simple-graph result to multigraphs while retaining edge identities: deleting fewer
than `k` actual edges can destroy at most that many adjacencies of the underlying simple graph.
An adjacency is destroyed only when every parallel edge above it is deleted; loops do not affect
the underlying simple graph.

The result needs no finiteness assumptions. Together with the incidence bound for edge
connectivity, it bounds multigraph vertex connectivity by the number of nonloop edges incident to
either of two distinct actual vertices.

The inequality is due to H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J.
Math. 54 (1932), 150--168. The reduction to the underlying simple graph follows the endpoint
selection argument in R. Diestel, *Graph Theory*, 5th ed., Proposition 1.4.2.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {k : ℕ}

/-- The simple edges whose every representing multigraph edge belongs to `F`. -/
private def blockedSimpleEdges (G : Graph α β) (F : Set β) : Set (Sym2 V(G)) :=
  {p | p ∈ G.toSimpleGraph.edgeSet ∧
    ∀ e : E(G), G.edgeEnds e = p → (e : β) ∈ F}

/-- Deleting `F` blocks at most `F.encard` edges of the underlying simple graph. -/
private theorem encard_blockedSimpleEdges_le (G : Graph α β) (F : Set β) :
    (blockedSimpleEdges G F).encard ≤ F.encard := by
  have hsubset : blockedSimpleEdges G F ⊆
      G.edgeEnds '' {e : E(G) | (e : β) ∈ F} := by
    intro p hp
    induction p using Sym2.ind with
    | _ x y =>
      have hadj : G.toSimpleGraph.Adj x y := G.toSimpleGraph.mem_edgeSet.mp hp.1
      obtain ⟨e, he⟩ := hadj.2
      let e' : E(G) := ⟨e, he.edge_mem⟩
      have hend : G.edgeEnds e' = s(x, y) := (G.edgeEnds_eq_iff_isLink e' x y).2 he
      exact ⟨e', hp.2 e' hend, hend⟩
  calc
    (blockedSimpleEdges G F).encard ≤
        (G.edgeEnds '' {e : E(G) | (e : β) ∈ F}).encard :=
      encard_le_encard hsubset
    _ ≤ {e : E(G) | (e : β) ∈ F}.encard := encard_image_le _ _
    _ ≤ F.encard := encard_preimage_val_le_encard_right E(G) F

/-- A simple adjacency that is not blocked by `F` has a representing edge outside `F`. -/
private theorem exists_isLink_notMem_of_notMem_blockedSimpleEdges
    (F : Set β) {x y : V(G)} (hxy : G.toSimpleGraph.Adj x y)
    (hnot : s(x, y) ∉ blockedSimpleEdges G F) :
    ∃ e : β, G.IsLink e x y ∧ e ∉ F := by
  by_contra! hall
  apply hnot
  refine ⟨G.toSimpleGraph.mem_edgeSet.mpr hxy, fun e he ↦ ?_⟩
  exact hall e ((G.edgeEnds_eq_iff_isLink e x y).1 he)

/-- A walk in the underlying simple graph after deleting the blocked adjacencies lifts to a
multigraph walk avoiding the original deleted edges. -/
private theorem exists_walk_avoiding_of_walk_deleteEdges
    (F : Set β) {x y : V(G)}
    (p : (G.toSimpleGraph.deleteEdges (blockedSimpleEdges G F)).Walk x y) :
    ∃ q : G.Walk x y, ∀ e ∈ q.edges, e ∉ F := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x y z h p ih =>
    obtain ⟨hxy, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h
    obtain ⟨e, he, heF⟩ := exists_isLink_notMem_of_notMem_blockedSimpleEdges F
      hxy hnot
    obtain ⟨q, hq⟩ := ih
    refine ⟨.cons e he q, ?_⟩
    intro a ha
    simp only [Walk.edges_cons, List.mem_cons] at ha
    exact ha.elim (fun hae ↦ hae ▸ heF) (hq a)

/-- **Whitney's inequality for multigraphs**, predicate form: a `k`-vertex-connected multigraph
is `k`-edge-connected. Parallel edges count separately toward edge connectivity, while loops
affect neither side. -/
theorem IsVertexConnected.isEdgeConnected (h : G.IsVertexConnected k) :
    G.IsEdgeConnected k := by
  rw [isEdgeConnected_def]
  intro x hx y hy
  rw [isEdgeReachable_def]
  intro F hF
  let x' : V(G) := ⟨x, hx⟩
  let y' : V(G) := ⟨y, hy⟩
  have hblocked : (blockedSimpleEdges G F).encard < k :=
    (encard_blockedSimpleEdges_le G F).trans_lt hF
  have hr : (G.toSimpleGraph.deleteEdges (blockedSimpleEdges G F)).Reachable x' y' :=
    (SimpleGraph.IsVertexConnected.isEdgeConnected h) x' y' hblocked
  obtain ⟨p⟩ := hr
  obtain ⟨q, hq⟩ := exists_walk_avoiding_of_walk_deleteEdges F p
  exact reachable_deleteEdges_iff_exists_walk.mpr ⟨hx, q, hq⟩

/-- **Whitney's inequality for multigraphs**: vertex connectivity is at most edge connectivity. -/
theorem vertexConnectivity_le_edgeConnectivity :
    G.vertexConnectivity ≤ G.edgeConnectivity := by
  cases isEmpty_or_nonempty V(G) with
  | inl _ =>
      rw [vertexConnectivity_of_subsingleton]
      exact bot_le
  | inr _ =>
      refine ENat.forall_natCast_le_iff_le.mp fun k hk ↦ ?_
      exact (isEdgeConnected_iff_le_edgeConnectivity k).1
        (IsVertexConnected.isEdgeConnected
          ((isVertexConnected_iff_le_vertexConnectivity k).2 hk))

/-- The vertex connectivity of a multigraph is at most the number of nonloop edges incident to
either of two distinct actual vertices. Parallel edges are counted separately. -/
theorem vertexConnectivity_le_nonloopIncidenceCount
    {x y : α} (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hxy : x ≠ y)
    (hfin : (G.incidenceSet x \ G.loopSet x).Finite) :
    G.vertexConnectivity ≤ G.nonloopIncidenceCount x :=
  vertexConnectivity_le_edgeConnectivity.trans
    (edgeConnectivity_le_nonloopIncidenceCount hx hy hxy hfin)

end Graph
