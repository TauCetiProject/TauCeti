/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Subgraphs of graphs associated to simple graphs

This file identifies a subgraph of a simple graph `G` with a subgraph of the edge-labelled graph
`Graph.ofSimpleGraph G`. The two conversions preserve vertex and edge sets, adjacency, inclusion,
unions, and singleton and full subgraphs.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Subgraph

/-- Regard a subgraph of a simple graph as a subgraph of its associated edge-labelled graph,
retaining the ambient vertex and edge types. -/
def toGraph (H : G.Subgraph) : Graph V (Sym2 V) :=
  (Graph.ofSimpleGraph H.spanningCoe).induce H.verts

@[simp]
theorem vertexSet_toGraph (H : G.Subgraph) : H.toGraph.vertexSet = H.verts :=
  Graph.vertexSet_induce _ _

@[simp]
theorem toGraph_isLink (H : G.Subgraph) (e : Sym2 V) (x y : V) :
    H.toGraph.IsLink e x y ↔ e = s(x, y) ∧ H.Adj x y := by
  simp only [toGraph, Graph.induce_isLink, Graph.ofSimpleGraph_isLink]
  constructor
  · rintro ⟨⟨rfl, he⟩, -, -⟩
    exact ⟨rfl, by simpa using he⟩
  · rintro ⟨rfl, hxy⟩
    exact ⟨⟨rfl, by simpa using hxy⟩, hxy.fst_mem, hxy.snd_mem⟩

@[simp]
theorem edgeSet_toGraph (H : G.Subgraph) : H.toGraph.edgeSet = H.edgeSet := by
  ext e
  induction e with
  | h x y =>
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      constructor
      · intro he
        obtain ⟨a, b, hab⟩ := (Graph.edge_mem_iff_exists_isLink _ _).1 he
        rw [H.toGraph_isLink] at hab
        exact (H.adj_congr_of_sym2 hab.1).mpr hab.2
      · intro hxy
        exact (Graph.edge_mem_iff_exists_isLink _ _).2
          ⟨x, y, (H.toGraph_isLink _ _ _).2 ⟨rfl, hxy⟩⟩

/-- The graph attached to a simple-graph subgraph is a subgraph of the graph attached to the
ambient simple graph. -/
theorem toGraph_le (H : G.Subgraph) : H.toGraph ≤ Graph.ofSimpleGraph G := by
  refine ⟨by simp, fun e x y he ↦ ?_⟩
  rw [H.toGraph_isLink] at he
  rw [Graph.ofSimpleGraph_isLink]
  exact ⟨he.1, he.1 ▸ G.mem_edgeSet.mpr (H.adj_sub he.2)⟩

@[simp]
theorem adj_toGraph (H : G.Subgraph) (x y : V) : H.toGraph.Adj x y ↔ H.Adj x y := by
  simp [Graph.Adj]

/-- Inclusion of simple-graph subgraphs is preserved by the edge-labelled representation. -/
theorem toGraph_mono {H K : G.Subgraph} (hHK : H ≤ K) : H.toGraph ≤ K.toGraph := by
  refine ⟨by simpa using hHK.1, fun e x y he ↦ ?_⟩
  rw [H.toGraph_isLink] at he
  exact (K.toGraph_isLink e x y).2 ⟨he.1, hHK.2 he.2⟩

@[simp]
theorem toGraph_top : (⊤ : G.Subgraph).toGraph = Graph.ofSimpleGraph G :=
  (Graph.Compatible.of_le_le (toGraph_le ⊤) le_rfl).ext (by simp) (by simp)

@[simp]
theorem toGraph_singletonSubgraph (v : V) :
    (G.singletonSubgraph v).toGraph = Graph.noEdge {v} (Sym2 V) :=
  (Graph.Compatible.of_le_le (toGraph_le _) (Graph.noEdge_le_iff.mpr (by simp))).ext
    (by simp) (by simp)

end Subgraph

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V}

/-- Regard a subgraph of `Graph.ofSimpleGraph G` as a subgraph of `G`. -/
def toSubgraphOfSimpleGraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G) :
    G.Subgraph where
  verts := V(K)
  Adj x y := K.Adj x y
  adj_sub := fun {x y} hxy ↦ (ofSimpleGraph_adj_iff x y).1 (hxy.mono hK)
  edge_vert := fun {_ _} hxy ↦ hxy.left_mem
  symm := ⟨fun _ _ hxy ↦ hxy.symm⟩

@[simp]
theorem verts_toSubgraphOfSimpleGraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) : (K.toSubgraphOfSimpleGraph hK).verts = V(K) :=
  (rfl)

@[simp]
theorem toSubgraphOfSimpleGraph_adj (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) (x y : V) :
    (K.toSubgraphOfSimpleGraph hK).Adj x y ↔ K.Adj x y :=
  Iff.rfl

@[simp]
theorem edgeSet_toSubgraphOfSimpleGraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSubgraphOfSimpleGraph hK).edgeSet = E(K) := by
  ext e
  induction e with
  | h x y =>
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      constructor
      · intro hxy
        obtain ⟨f, hf⟩ := hxy
        have hfeq : f = s(x, y) := (hK.2 hf).1
        subst f
        exact hf.edge_mem
      · intro he
        obtain ⟨a, b, hab⟩ := (edge_mem_iff_exists_isLink K _).1 he
        have heq : s(a, b) = s(x, y) := (hK.2 hab).1.symm
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨_, hab⟩
        · exact ⟨_, hab.symm⟩

@[simp]
theorem toGraph_toSubgraphOfSimpleGraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) : (K.toSubgraphOfSimpleGraph hK).toGraph = K :=
  (Compatible.of_le_le (K.toSubgraphOfSimpleGraph hK).toGraph_le hK).ext (by simp) (by simp)

/-- The conversion to a simple-graph subgraph is independent of replacing its graph argument and
inclusion proof by equal ones. -/
theorem toSubgraphOfSimpleGraph_congr {K L : Graph V (Sym2 V)}
    (h : K = L) (hK : K ≤ Graph.ofSimpleGraph G) (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSubgraphOfSimpleGraph hK = L.toSubgraphOfSimpleGraph hL := by
  subst L
  ext <;> simp

@[simp]
theorem toSubgraphOfSimpleGraph_ofSimpleGraph :
    (Graph.ofSimpleGraph G).toSubgraphOfSimpleGraph le_rfl = (⊤ : G.Subgraph) := by
  ext <;> simp

@[simp]
theorem toSubgraphOfSimpleGraph_noEdge_singleton (v : V)
    (h : Graph.noEdge {v} (Sym2 V) ≤ Graph.ofSimpleGraph G) :
    (Graph.noEdge {v} (Sym2 V)).toSubgraphOfSimpleGraph h = G.singletonSubgraph v := by
  ext x y
  · simp [toSubgraphOfSimpleGraph]
  · simp [Graph.Adj]

end Graph

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

@[simp]
theorem toSubgraphOfSimpleGraph_toGraph (H : G.Subgraph) :
    H.toGraph.toSubgraphOfSimpleGraph H.toGraph_le = H := by
  ext <;> simp

/-- The edge-labelled representation of simple-graph subgraphs is injective. -/
theorem toGraph_injective (G : SimpleGraph V) :
    Function.Injective (fun H : G.Subgraph ↦ H.toGraph) := by
  intro H K h
  ext x y
  · rw [show H.verts = K.verts from by simpa using congrArg Graph.vertexSet h]
  · have hlink := congrArg (fun L : Graph V (Sym2 V) ↦ L.IsLink s(x, y) x y) h
    simpa using hlink

end SimpleGraph.Subgraph
