/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import TauCeti.Combinatorics.Graph.Union

/-!
# Subgraphs of simple graphs viewed as multigraphs

Mathlib represents subgraphs of a simple graph `H : SimpleGraph V` as bundled structures
`S : H.Subgraph`, whereas subgraphs of a multigraph `G : Graph V E` are graphs `K : Graph V E`
satisfying `K ≤ G`. When `G` is `Graph.ofSimpleGraph H`, an edge identity is determined by its
unordered pair of endpoints, so no multiplicity or loop data separates the two viewpoints.

This file builds the order-preserving bijection between `H.Subgraph` and
`{K : Graph V (Sym2 V) // K ≤ Graph.ofSimpleGraph H}` and shows that it commutes with the standard
subgraph operations: `⊤`, `⊥`, singleton and single-edge subgraphs, binary suprema (compatible
unions) and infima, edge deletion, induced subgraphs, spanning and induced predicates, and the
underlying simple graph `S.coe`.

## Main definitions

* `SimpleGraph.Subgraph.toGraph`: view `S : H.Subgraph` as a multigraph `Graph V (Sym2 V)` inside
  `Graph.ofSimpleGraph H`.
* `Graph.IsSubgraph.toSimpleGraphSubgraph`: recover `S : H.Subgraph` from any multigraph subgraph
  `hK : K ≤ Graph.ofSimpleGraph H`.
* `SimpleGraph.subgraphOrderIsoOfSimpleGraph`: the order isomorphism
  `H.Subgraph ≃o {K : Graph V (Sym2 V) // K ≤ Graph.ofSimpleGraph H}`.
* `SimpleGraph.Subgraph.toSimpleGraphToGraphIso`: the canonical simple-graph isomorphism
  `S.toGraph.toSimpleGraph ≃g S.coe`.
-/

public section

open Set
open scoped Graph Sym2

universe u

namespace SimpleGraph.Subgraph

variable {V : Type u} {H : SimpleGraph V}

private theorem edgeSet_iff_exists_adj (S : H.Subgraph) (e : Sym2 V) :
    e ∈ S.edgeSet ↔ ∃ x y, e = s(x, y) ∧ S.Adj x y := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Subgraph.mem_edgeSet]
    exact ⟨fun h ↦ ⟨u, v, rfl, h⟩,
      fun ⟨x, y, he, h⟩ ↦ (Sym2.eq_iff.mp he).elim
        (fun ⟨rfl, rfl⟩ ↦ h) (fun ⟨rfl, rfl⟩ ↦ h.symm)⟩

/-- Regard a subgraph `S` of a simple graph `H` as a multigraph on `V` with edge type `Sym2 V`,
retaining the vertices and edges of `S`. -/
def toGraph (S : H.Subgraph) : Graph V (Sym2 V) where
  vertexSet := S.verts
  edgeSet := S.edgeSet
  IsLink e x y := e = s(x, y) ∧ S.Adj x y
  isLink_symm _ _ := ⟨fun _ _ ⟨he, hxy⟩ ↦ ⟨he.trans Sym2.eq_swap, hxy.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := by
    rcases Sym2.eq_iff.mp (h₁.1.symm.trans h₂.1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := S.edgeSet_iff_exists_adj
  left_mem_of_isLink _ _ _ h := S.edge_vert h.2

@[simp, grind =]
theorem vertexSet_toGraph (S : H.Subgraph) : V(S.toGraph) = S.verts := (rfl)

@[simp, grind =]
theorem edgeSet_toGraph (S : H.Subgraph) : E(S.toGraph) = S.edgeSet := (rfl)

@[simp, grind =]
theorem toGraph_isLink (S : H.Subgraph) (e : Sym2 V) (x y : V) :
    S.toGraph.IsLink e x y ↔ e = s(x, y) ∧ S.Adj x y := (Iff.rfl)

@[simp]
theorem toGraph_adj (S : H.Subgraph) (x y : V) :
    S.toGraph.Adj x y ↔ S.Adj x y := by
  simp [Graph.Adj]

@[simp]
theorem toGraph_inc (S : H.Subgraph) (e : Sym2 V) (x : V) :
    S.toGraph.Inc e x ↔ e ∈ S.edgeSet ∧ x ∈ e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Graph.Inc, toGraph_isLink, Sym2.eq_iff, Sym2.mem_iff]
    constructor
    · rintro ⟨y, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hxy⟩
      · exact ⟨hxy, Or.inl rfl⟩
      · exact ⟨hxy.symm, Or.inr rfl⟩
    · rintro ⟨huv, rfl | rfl⟩
      · exact ⟨v, Or.inl ⟨rfl, rfl⟩, huv⟩
      · exact ⟨u, Or.inr ⟨rfl, rfl⟩, huv.symm⟩

/-- The multigraph associated to any subgraph of a simple graph is simple (hence loopless). -/
instance (S : H.Subgraph) : S.toGraph.Simple where
  not_isLoopAt e x h := by
    rw [Graph.IsLoopAt, toGraph_isLink] at h
    exact S.loopless.irrefl x h.2
  eq_of_isLink _ _ _ _ h₁ h₂ := h₁.1.trans h₂.1.symm

/-- Every `S.toGraph` is a subgraph of `Graph.ofSimpleGraph H`. -/
@[simp]
theorem toGraph_le_ofSimpleGraph (S : H.Subgraph) : S.toGraph ≤ Graph.ofSimpleGraph H where
  vertexSet_mono := subset_univ _
  isLink_mono e x y h := by
    rw [toGraph_isLink] at h
    rw [Graph.ofSimpleGraph_isLink]
    exact ⟨h.1, h.1 ▸ H.mem_edgeSet.mpr (S.adj_sub h.2)⟩

/-- Multigraphs obtained from subgraphs of one ambient simple graph are pairwise compatible. -/
theorem toGraph_compatible (S₁ S₂ : H.Subgraph) : S₁.toGraph.Compatible S₂.toGraph :=
  .of_le_le S₁.toGraph_le_ofSimpleGraph S₂.toGraph_le_ofSimpleGraph

@[simp]
theorem toGraph_le_toGraph_iff {S₁ S₂ : H.Subgraph} :
    S₁.toGraph ≤ S₂.toGraph ↔ S₁ ≤ S₂ := by
  constructor
  · intro h
    refine ⟨by simpa using h.vertexSet_mono, fun x y hxy ↦ ?_⟩
    exact ((S₂.toGraph_isLink s(x, y) x y).mp
      (h.isLink_mono ((S₁.toGraph_isLink s(x, y) x y).mpr ⟨rfl, hxy⟩))).2
  · rintro ⟨hv, ha⟩
    exact ⟨hv, fun e x y h ↦ by
      rw [toGraph_isLink] at h ⊢
      exact ⟨h.1, ha h.2⟩⟩

theorem toGraph_mono : Monotone (toGraph (H := H)) :=
  fun _ _ ↦ toGraph_le_toGraph_iff.mpr

theorem toGraph_injective : Function.Injective (toGraph (H := H)) :=
  fun _ _ h ↦ le_antisymm
    (toGraph_le_toGraph_iff.mp h.le) (toGraph_le_toGraph_iff.mp h.ge)

@[simp]
theorem toGraph_inj {S₁ S₂ : H.Subgraph} : S₁.toGraph = S₂.toGraph ↔ S₁ = S₂ :=
  toGraph_injective.eq_iff

@[simp]
theorem toGraph_lt_toGraph_iff {S₁ S₂ : H.Subgraph} :
    S₁.toGraph < S₂.toGraph ↔ S₁ < S₂ :=
  lt_iff_lt_of_le_iff_le' toGraph_le_toGraph_iff toGraph_le_toGraph_iff

theorem toGraph_strictMono : StrictMono (toGraph (H := H)) :=
  fun _ _ ↦ toGraph_lt_toGraph_iff.mpr

end SimpleGraph.Subgraph

namespace Graph.IsSubgraph

variable {V : Type u} {H : SimpleGraph V} {K K₁ K₂ : Graph V (Sym2 V)}

/-- Recover a subgraph of `H` from a multigraph subgraph of `Graph.ofSimpleGraph H`. -/
def toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) : H.Subgraph where
  verts := V(K)
  Adj := K.Adj
  adj_sub hxy := (Graph.ofSimpleGraph_adj_iff _ _).mp (hxy.mono hK)
  edge_vert hxy := hxy.left_mem
  symm := ⟨fun _ _ hxy ↦ hxy.symm⟩

@[simp, grind =]
theorem verts_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.verts = V(K) := (rfl)

@[simp, grind =]
theorem toSimpleGraphSubgraph_adj (hK : K ≤ Graph.ofSimpleGraph H) (x y : V) :
    hK.toSimpleGraphSubgraph.Adj x y ↔ K.Adj x y := (Iff.rfl)

@[simp, grind =]
theorem edgeSet_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.edgeSet = E(K) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.Subgraph.mem_edgeSet, toSimpleGraphSubgraph_adj]
    constructor
    · rintro ⟨f, hf⟩
      have hfH := (Graph.ofSimpleGraph_isLink ..).mp (hf.mono hK)
      exact hfH.1 ▸ hf.edge_mem
    · intro he
      obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
      have huvH := (Graph.ofSimpleGraph_isLink ..).mp (huv.mono hK)
      rcases Sym2.eq_iff.mp huvH.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv.adj
      · exact huv.symm.adj

@[simp]
theorem toGraph_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.toGraph = K :=
  (Compatible.of_le_le hK.toSimpleGraphSubgraph.toGraph_le_ofSimpleGraph hK).ext
    (by simp) (by simp)

@[simp]
theorem toSimpleGraphSubgraph_le_iff (hK₁ : K₁ ≤ Graph.ofSimpleGraph H)
    (hK₂ : K₂ ≤ Graph.ofSimpleGraph H) :
    hK₁.toSimpleGraphSubgraph ≤ hK₂.toSimpleGraphSubgraph ↔ K₁ ≤ K₂ := by
  rw [← SimpleGraph.Subgraph.toGraph_le_toGraph_iff,
    hK₁.toGraph_toSimpleGraphSubgraph, hK₂.toGraph_toSimpleGraphSubgraph]

@[simp]
theorem toSimpleGraphSubgraph_inj (hK₁ : K₁ ≤ Graph.ofSimpleGraph H)
    (hK₂ : K₂ ≤ Graph.ofSimpleGraph H) :
    hK₁.toSimpleGraphSubgraph = hK₂.toSimpleGraphSubgraph ↔ K₁ = K₂ := by
  rw [← SimpleGraph.Subgraph.toGraph_inj,
    hK₁.toGraph_toSimpleGraphSubgraph, hK₂.toGraph_toSimpleGraphSubgraph]

end Graph.IsSubgraph

namespace SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

namespace Subgraph

@[simp]
theorem toSimpleGraphSubgraph_toGraph (S : H.Subgraph)
    (hS : S.toGraph ≤ Graph.ofSimpleGraph H) :
    hS.toSimpleGraphSubgraph = S := by
  ext x y <;> simp

end Subgraph

/-- Subgraphs of a simple graph `H` are order-isomorphic to multigraph subgraphs of
`Graph.ofSimpleGraph H`. -/
def subgraphOrderIsoOfSimpleGraph (H : SimpleGraph V) :
    H.Subgraph ≃o {K : Graph V (Sym2 V) // K ≤ Graph.ofSimpleGraph H} where
  toFun S := ⟨S.toGraph, S.toGraph_le_ofSimpleGraph⟩
  invFun K := K.2.toSimpleGraphSubgraph
  left_inv S := S.toSimpleGraphSubgraph_toGraph S.toGraph_le_ofSimpleGraph
  right_inv K := Subtype.ext K.2.toGraph_toSimpleGraphSubgraph
  map_rel_iff' := Subgraph.toGraph_le_toGraph_iff

@[simp]
theorem coe_subgraphOrderIsoOfSimpleGraph_apply (H : SimpleGraph V) (S : H.Subgraph) :
    (H.subgraphOrderIsoOfSimpleGraph S : Graph V (Sym2 V)) = S.toGraph := (rfl)

@[simp]
theorem subgraphOrderIsoOfSimpleGraph_symm_apply (H : SimpleGraph V)
    (K : {K : Graph V (Sym2 V) // K ≤ Graph.ofSimpleGraph H}) :
    H.subgraphOrderIsoOfSimpleGraph.symm K = K.2.toSimpleGraphSubgraph := (rfl)

namespace Subgraph

/-! ### Compatibility with lattice and graph operations -/

@[simp]
theorem top_toGraph : (⊤ : H.Subgraph).toGraph = Graph.ofSimpleGraph H :=
  Graph.ext (by simp) fun e x y ↦ by
    simp only [toGraph_isLink, top_adj, Graph.ofSimpleGraph_isLink]
    exact ⟨fun ⟨he, hxy⟩ ↦ ⟨he, he ▸ H.mem_edgeSet.mpr hxy⟩,
      fun ⟨he, hmem⟩ ↦ ⟨he, H.mem_edgeSet.mp (he ▸ hmem)⟩⟩

@[simp]
theorem bot_toGraph : (⊥ : H.Subgraph).toGraph = ⊥ :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp

@[simp]
theorem singletonSubgraph_toGraph (v : V) :
    (H.singletonSubgraph v).toGraph = Graph.noEdge {v} (Sym2 V) :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp

@[simp]
theorem subgraphOfAdj_toGraph {u v : V} (h : H.Adj u v) :
    (H.subgraphOfAdj h).toGraph = ((Graph.ofSimpleGraph H).induce {u, v}).restrict {s(u, v)} := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [toGraph_isLink, subgraphOfAdj_adj, Graph.restrict_isLink, mem_singleton_iff,
    Graph.induce_isLink, Graph.ofSimpleGraph_isLink, mem_insert_iff]
  constructor
  · rintro ⟨rfl, hxy⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, ⟨rfl, H.mem_edgeSet.mpr h⟩, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Sym2.eq_swap, ⟨rfl, H.mem_edgeSet.mpr h.symm⟩, Or.inr rfl, Or.inl rfl⟩
  · rintro ⟨he, ⟨rfl, -⟩, -, -⟩
    exact ⟨rfl, he.symm⟩

@[simp]
theorem toSubgraph_toGraph {H' : SimpleGraph V} (h : H' ≤ H) :
    (SimpleGraph.toSubgraph H' h).toGraph = Graph.ofSimpleGraph H' :=
  Graph.ext (by simp) fun e x y ↦ by
    simp only [toGraph_isLink, SimpleGraph.toSubgraph_adj, Graph.ofSimpleGraph_isLink]
    exact ⟨fun ⟨he, hxy⟩ ↦ ⟨he, he ▸ H'.mem_edgeSet.mpr hxy⟩,
      fun ⟨he, hmem⟩ ↦ ⟨he, H'.mem_edgeSet.mp (he ▸ hmem)⟩⟩

@[simp]
theorem sup_toGraph (S₁ S₂ : H.Subgraph) :
    (S₁ ⊔ S₂).toGraph = (S₁.toGraph_compatible S₂).union :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_or_left]

@[simp]
theorem deleteEdges_toGraph (S : H.Subgraph) (F : Set (Sym2 V)) :
    (S.deleteEdges F).toGraph = S.toGraph.deleteEdges F :=
  Graph.ext (by simp) fun e x y ↦ by
    simp only [toGraph_isLink, deleteEdges_adj, Graph.deleteEdges_isLink]
    constructor
    · rintro ⟨rfl, hxy, hnF⟩
      exact ⟨⟨rfl, hxy⟩, hnF⟩
    · rintro ⟨⟨rfl, hxy⟩, hnF⟩
      exact ⟨rfl, hxy, hnF⟩

@[simp]
theorem induce_toGraph (S : H.Subgraph) (s : Set V) :
    (S.induce s).toGraph = S.toGraph.induce s :=
  Graph.ext (by simp) fun _ _ _ ↦ by
    simp only [toGraph_isLink, induce_adj, Graph.induce_isLink]
    tauto

@[simp]
theorem inf_toGraph (S₁ S₂ : H.Subgraph) :
    (S₁ ⊓ S₂).toGraph = (S₁.toGraph.induce (S₁.verts ∩ S₂.verts)).restrict S₂.edgeSet :=
  Graph.ext (by simp) fun e x y ↦ by
    simp only [toGraph_isLink, inf_adj, Graph.restrict_isLink, Graph.induce_isLink, mem_inter_iff]
    constructor
    · rintro ⟨rfl, h₁, h₂⟩
      exact ⟨Subgraph.mem_edgeSet.mpr h₂, ⟨rfl, h₁⟩,
        ⟨S₁.edge_vert h₁, S₂.edge_vert h₂⟩, ⟨S₁.edge_vert h₁.symm, S₂.edge_vert h₂.symm⟩⟩
    · rintro ⟨he₂, ⟨rfl, h₁⟩, -, -⟩
      exact ⟨rfl, h₁, Subgraph.mem_edgeSet.mp he₂⟩

@[simp]
theorem isSpanning_toGraph_iff {S : H.Subgraph} :
    S.toGraph ≤s Graph.ofSimpleGraph H ↔ S.IsSpanning := by
  rw [Graph.isSpanningSubgraph_iff, Subgraph.isSpanning_iff]
  simp [S.toGraph_le_ofSimpleGraph]

@[simp]
theorem isInducedSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph ≤i Graph.ofSimpleGraph H ↔ S.IsInduced := by
  rw [Graph.isInducedSubgraph_iff]
  simp only [Graph.ofSimpleGraph_isLink, vertexSet_toGraph, toGraph_isLink]
  constructor
  · rintro ⟨-, h⟩ x hx y hy hxy
    exact (h ⟨rfl, H.mem_edgeSet.mpr hxy⟩ hx hy).2
  · intro h
    exact ⟨S.toGraph_le_ofSimpleGraph,
      fun _ _ _ ⟨heq, he⟩ hx hy ↦ ⟨heq, h hx hy (H.mem_edgeSet.mp (heq ▸ he))⟩⟩

/-- The underlying simple graph of `S.toGraph` is canonically isomorphic to `S.coe`. -/
def toSimpleGraphToGraphIso (S : H.Subgraph) : S.toGraph.toSimpleGraph ≃g S.coe where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_toGraph]
  map_rel_iff' {u v} := by
    rw [S.toGraph.toSimpleGraph_adj_iff, toGraph_adj]
    rfl

@[simp]
theorem coe_toSimpleGraphToGraphIso_apply (S : H.Subgraph) (v : V(S.toGraph)) :
    (S.toSimpleGraphToGraphIso v : V) = v := (rfl)

@[simp]
theorem coe_toSimpleGraphToGraphIso_symm_apply (S : H.Subgraph) (v : S.verts) :
    (S.toSimpleGraphToGraphIso.symm v : V) = v := (rfl)

end Subgraph

end SimpleGraph

namespace Graph.IsSubgraph

variable {V : Type u} {H : SimpleGraph V}

@[simp]
theorem ofSimpleGraph_toSimpleGraphSubgraph
    (h : Graph.ofSimpleGraph H ≤ Graph.ofSimpleGraph H) :
    h.toSimpleGraphSubgraph = ⊤ := by
  rw [← SimpleGraph.Subgraph.toGraph_inj, h.toGraph_toSimpleGraphSubgraph,
    SimpleGraph.Subgraph.top_toGraph]

@[simp]
theorem bot_toSimpleGraphSubgraph (h : (⊥ : Graph V (Sym2 V)) ≤ Graph.ofSimpleGraph H) :
    h.toSimpleGraphSubgraph = ⊥ := by
  rw [← SimpleGraph.Subgraph.toGraph_inj, h.toGraph_toSimpleGraphSubgraph,
    SimpleGraph.Subgraph.bot_toGraph]

@[simp]
theorem noEdge_singleton_toSimpleGraphSubgraph {v : V}
    (h : Graph.noEdge {v} (Sym2 V) ≤ Graph.ofSimpleGraph H) :
    h.toSimpleGraphSubgraph = H.singletonSubgraph v := by
  rw [← SimpleGraph.Subgraph.toGraph_inj, h.toGraph_toSimpleGraphSubgraph,
    SimpleGraph.Subgraph.singletonSubgraph_toGraph]

end Graph.IsSubgraph

namespace Graph

instance instFiniteEdgeSetOfSimpleGraph {V : Type u} (H : SimpleGraph V) [Finite H.edgeSet] :
    Finite E(Graph.ofSimpleGraph H) := by
  rwa [Graph.edgeSet_ofSimpleGraph]

end Graph
