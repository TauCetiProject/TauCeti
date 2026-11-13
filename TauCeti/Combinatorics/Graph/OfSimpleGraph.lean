/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import TauCeti.Combinatorics.Graph.Union

/-!
# Subgraphs of graphs built from simple graphs

A subgraph `H : G.Subgraph` of a simple graph `G` determines a multigraph `H.toGraph` on the same
vertex type, whose edge joining adjacent vertices `x` and `y` of `H` is the unordered pair
`s(x, y)`, exactly as in `Graph.ofSimpleGraph`. This identifies `G.Subgraph` with the multigraph
subgraphs of `Graph.ofSimpleGraph G`, as an order isomorphism
`SimpleGraph.Subgraph.toGraphOrderIso`.

The correspondence sends the top subgraph to `Graph.ofSimpleGraph G`, singleton subgraphs to
edgeless one-vertex graphs, and suprema to unions. These are the identities needed to transport
constructions built from subgraphs, such as ear decompositions, between the two interfaces.
-/

public section

open scoped Graph Sym2

universe u

namespace SimpleGraph

variable {α : Type u} {G : SimpleGraph α}

namespace Subgraph

variable {H K : G.Subgraph} {e : Sym2 α} {x y : α}

/-- A subgraph of a simple graph `G`, regarded as a subgraph of `Graph.ofSimpleGraph G`: its
vertices are those of the subgraph, and its edges are the unordered pairs of adjacent vertices. -/
def toGraph (H : G.Subgraph) : Graph α (Sym2 α) where
  vertexSet := H.verts
  edgeSet := H.edgeSet
  IsLink e x y := e = s(x, y) ∧ H.Adj x y
  isLink_symm _ _ := ⟨fun _ _ h ↦ ⟨h.1.trans Sym2.eq_swap, h.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by
    induction e with | h u v => exact ⟨fun h ↦ ⟨u, v, rfl, h⟩, by rintro ⟨x, y, h, hxy⟩; simpa [h]⟩
  left_mem_of_isLink _ _ _ h := H.edge_vert h.2

@[simp]
theorem vertexSet_toGraph (H : G.Subgraph) : V(H.toGraph) = H.verts := (rfl)

@[simp]
theorem edgeSet_toGraph (H : G.Subgraph) : E(H.toGraph) = H.edgeSet := (rfl)

@[simp]
theorem toGraph_isLink : H.toGraph.IsLink e x y ↔ e = s(x, y) ∧ H.Adj x y := (Iff.rfl)

@[simp]
theorem toGraph_adj : H.toGraph.Adj x y ↔ H.Adj x y := by
  simp [Graph.Adj]

/-- The multigraph of a subgraph is a subgraph of the multigraph of the ambient simple graph. -/
theorem toGraph_le (H : G.Subgraph) : H.toGraph ≤ Graph.ofSimpleGraph G where
  vertexSet_mono := Set.subset_univ _
  isLink_mono _ _ _ h := by
    rw [toGraph_isLink] at h
    simpa [h.1] using h.2.adj_sub

@[simp]
theorem toGraph_le_toGraph_iff : H.toGraph ≤ K.toGraph ↔ H ≤ K := by
  refine ⟨fun h ↦ ⟨h.vertexSet_mono, fun x y hxy ↦ ?_⟩, fun h ↦ ⟨h.1, fun e x y hxy ↦ ?_⟩⟩
  · exact (toGraph_isLink.mp (h.isLink_mono (toGraph_isLink.mpr ⟨rfl, hxy⟩))).2
  · rw [toGraph_isLink] at hxy ⊢
    exact ⟨hxy.1, h.2 hxy.2⟩

theorem toGraph_injective : Function.Injective (toGraph (G := G)) := fun _ _ h ↦
  le_antisymm (toGraph_le_toGraph_iff.mp h.le) (toGraph_le_toGraph_iff.mp h.ge)

@[simp]
theorem toGraph_inj : H.toGraph = K.toGraph ↔ H = K :=
  toGraph_injective.eq_iff

@[simp]
theorem toGraph_top : (⊤ : G.Subgraph).toGraph = Graph.ofSimpleGraph G :=
  Graph.ext (by simp) fun e x y ↦ by
    simp only [toGraph_isLink, top_adj, Graph.ofSimpleGraph_isLink]
    constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

@[simp]
theorem toGraph_singletonSubgraph (v : α) :
    (G.singletonSubgraph v).toGraph = Graph.noEdge {v} (Sym2 α) :=
  Graph.ext (by simp) fun e x y ↦ by simp

/-- The multigraph of a supremum of subgraphs is the union of their multigraphs. -/
theorem toGraph_sup (H K : G.Subgraph) :
    (H ⊔ K).toGraph = (Graph.Compatible.of_le_le H.toGraph_le K.toGraph_le).union :=
  Graph.ext (by simp) fun e x y ↦ by simp [and_or_left]

/-- Every subgraph of `Graph.ofSimpleGraph G` comes from a unique subgraph of `G`, so the subgraphs
of a simple graph are order-isomorphic to the multigraph subgraphs of its multigraph. -/
def toGraphOrderIso {G : SimpleGraph α} : G.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph G) where
  toFun H := ⟨H.toGraph, H.toGraph_le⟩
  invFun K :=
    { verts := V(K.1)
      Adj x y := K.1.IsLink s(x, y) x y
      adj_sub h := by simpa using K.2.isLink_mono h
      edge_vert h := h.left_mem
      symm := ⟨fun _ _ h ↦ by simpa [Sym2.eq_swap] using h.symm⟩ }
  left_inv H := by
    ext <;> simp
  right_inv K := by
    refine Subtype.ext (Graph.ext (by simp) fun e x y ↦ ?_)
    simp only [toGraph_isLink]
    constructor
    · rintro ⟨rfl, h⟩
      exact h
    · intro h
      exact ⟨by simpa using (K.2.isLink_mono h).1, by simpa using (K.2.isLink_mono h).1 ▸ h⟩
  map_rel_iff' := Subtype.mk_le_mk.trans toGraph_le_toGraph_iff

@[simp]
theorem coe_toGraphOrderIso_apply (H : G.Subgraph) :
    (toGraphOrderIso H : Graph α (Sym2 α)) = H.toGraph := (rfl)

@[simp]
theorem toGraph_toGraphOrderIso_symm_apply (K : Set.Iic (Graph.ofSimpleGraph G)) :
    (toGraphOrderIso.symm K).toGraph = K := by
  rw [← coe_toGraphOrderIso_apply, OrderIso.apply_symm_apply]

@[simp]
theorem verts_toGraphOrderIso_symm_apply (K : Set.Iic (Graph.ofSimpleGraph G)) :
    (toGraphOrderIso.symm K).verts = V(K.1) := (rfl)

@[simp]
theorem toGraphOrderIso_symm_apply_adj (K : Set.Iic (Graph.ofSimpleGraph G)) :
    (toGraphOrderIso.symm K).Adj x y ↔ K.1.Adj x y := by
  rw [← toGraph_adj, toGraph_toGraphOrderIso_symm_apply]

end Subgraph

end SimpleGraph
