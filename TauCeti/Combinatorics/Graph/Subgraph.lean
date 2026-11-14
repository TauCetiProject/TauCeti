/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Union

/-!
# Subgraphs of simple graphs viewed as multigraphs

Mathlib represents subgraphs in two ways: a subgraph of `H : SimpleGraph α` is a bundled record
`S : H.Subgraph` storing a vertex subset and a subrelation of `H.Adj`, whereas a subgraph of a
multigraph `G : Graph α β` is another `Graph α β` ordered by `K ≤ G`.

When `G = Graph.ofSimpleGraph H`, every actual edge identity `e : Sym2 α` is determined by its
unordered pair of ends, so no parallel-edge or loop information distinguishes subgraphs of
`Graph.ofSimpleGraph H` from terms of `H.Subgraph`. This file constructs the two-way translation and
packages it as an order isomorphism `H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H)`, preserving
vertex and edge sets, top, bottom, intersections, compatible unions, singleton subgraphs, spanning
and induced predicates, and canonical isomorphisms `S.toGraph.toSimpleGraph ≃g S.coe` and
`Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.

## Main definitions

* `SimpleGraph.Subgraph.toGraph`: view a simple-graph subgraph `S : H.Subgraph` as a multigraph
  `Graph α (Sym2 α)` below `Graph.ofSimpleGraph H`.
* `SimpleGraph.Subgraph.toGraphToSimpleGraphIso`: canonical simple-graph isomorphism
  `S.toGraph.toSimpleGraph ≃g S.coe`.
* `SimpleGraph.Subgraph.ofSimpleGraphCoeIso`: canonical multigraph isomorphism
  `Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.
* `Graph.IsSubgraph.toSimpleGraphSubgraph`: recover `S : H.Subgraph` from
  `hK : K ≤ Graph.ofSimpleGraph H`.
* `SimpleGraph.subgraphOfSimpleGraphOrderIso`: the order isomorphism
  `H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H)`.
-/

public section

open Set
open scoped Graph Sym2

universe u

namespace SimpleGraph.Subgraph

variable {α : Type u} {H : SimpleGraph α}

/-- Regard a subgraph `S : H.Subgraph` of a simple graph as a multigraph `Graph α (Sym2 α)` whose
actual vertices are `S.verts` and whose links are the unordered pairs of `S`-adjacent vertices. -/
def toGraph (S : H.Subgraph) : Graph α (Sym2 α) where
  vertexSet := S.verts
  edgeSet := S.edgeSet
  IsLink e x y := e = s(x, y) ∧ S.Adj x y
  isLink_symm _ _ := ⟨fun _ _ ⟨he, hxy⟩ ↦ ⟨he.trans Sym2.eq_swap, hxy.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨rfl, _⟩ ⟨heq, _⟩; exact (Sym2.eq_iff.mp heq).imp And.left And.left
  edge_mem_iff_exists_isLink := Sym2.ind fun x y ↦ by
    rw [S.mem_edgeSet]
    refine ⟨fun h ↦ ⟨x, y, rfl, h⟩, fun ⟨_, _, heq, huv⟩ ↦ ?_⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [huv, huv.symm]
  left_mem_of_isLink _ _ _ h := S.edge_vert h.2

@[simp, grind =] theorem vertexSet_toGraph (S : H.Subgraph) : V(S.toGraph) = S.verts := (rfl)

@[simp, grind =] theorem edgeSet_toGraph (S : H.Subgraph) : E(S.toGraph) = S.edgeSet := (rfl)

@[simp, grind =]
theorem toGraph_isLink (S : H.Subgraph) (e : Sym2 α) (x y : α) :
    S.toGraph.IsLink e x y ↔ e = s(x, y) ∧ S.Adj x y := (Iff.rfl)

@[simp] theorem toGraph_adj_iff (S : H.Subgraph) (x y : α) : S.toGraph.Adj x y ↔ S.Adj x y := by
  simp [Graph.Adj]

/-- The multigraph associated to any simple-graph subgraph is simple (loopless with no parallel
edges). -/
instance instSimpleToGraph (S : H.Subgraph) : S.toGraph.Simple where
  not_isLoopAt e x h := by rw [Graph.IsLoopAt, toGraph_isLink] at h; exact S.loopless.irrefl x h.2
  eq_of_isLink _ _ _ _ h₁ h₂ := h₁.1.trans h₂.1.symm

/-- Every `S : H.Subgraph` embeds as a multigraph subgraph of `Graph.ofSimpleGraph H`. -/
theorem toGraph_le_ofSimpleGraph (S : H.Subgraph) : S.toGraph ≤ Graph.ofSimpleGraph H where
  vertexSet_mono := subset_univ _
  isLink_mono := by
    rintro _ x y ⟨rfl, hxy⟩
    rw [Graph.ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet]
    exact ⟨rfl, S.adj_sub hxy⟩

@[gcongr]
theorem toGraph_mono {S T : H.Subgraph} (h : S ≤ T) : S.toGraph ≤ T.toGraph where
  vertexSet_mono := h.1
  isLink_mono _ _ _ hxy := ⟨hxy.1, h.2 hxy.2⟩

@[simp]
theorem toGraph_le_toGraph_iff {S T : H.Subgraph} : S.toGraph ≤ T.toGraph ↔ S ≤ T :=
  ⟨fun h ↦ ⟨h.vertexSet_mono, fun x y hxy ↦
    ((T.toGraph_isLink s(x, y) x y).mp (h.isLink_mono ⟨rfl, hxy⟩)).2⟩, toGraph_mono⟩

theorem toGraph_injective : Function.Injective (toGraph (H := H)) :=
  fun _ _ h ↦ le_antisymm (toGraph_le_toGraph_iff.mp h.le) (toGraph_le_toGraph_iff.mp h.ge)

@[simp] theorem toGraph_inj {S T : H.Subgraph} : S.toGraph = T.toGraph ↔ S = T :=
  toGraph_injective.eq_iff

@[simp] theorem toGraph_lt_toGraph_iff {S T : H.Subgraph} : S.toGraph < T.toGraph ↔ S < T :=
  lt_iff_lt_of_le_iff_le' toGraph_le_toGraph_iff toGraph_le_toGraph_iff

@[simp]
theorem toGraph_top : (⊤ : H.Subgraph).toGraph = Graph.ofSimpleGraph H := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [toGraph_isLink, top_adj, Graph.ofSimpleGraph_isLink]
  exact ⟨fun ⟨he, hxy⟩ ↦ ⟨he, he ▸ H.mem_edgeSet.mpr hxy⟩,
    fun ⟨he, hmem⟩ ↦ ⟨he, H.mem_edgeSet.mp (he ▸ hmem)⟩⟩

@[simp] theorem toGraph_bot : (⊥ : H.Subgraph).toGraph = ⊥ :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp

@[simp] theorem toGraph_inf (S T : H.Subgraph) : (S ⊓ T).toGraph = S.toGraph ⊓ T.toGraph :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_left_comm, and_assoc]

/-- Any two subgraphs of the same simple graph convert to compatible multigraphs. -/
theorem toGraph_compatible (S T : H.Subgraph) : S.toGraph.Compatible T.toGraph :=
  .of_le_le S.toGraph_le_ofSimpleGraph T.toGraph_le_ofSimpleGraph

/-- The supremum of two simple-graph subgraphs corresponds to the compatible multigraph union. -/
theorem toGraph_sup (S T : H.Subgraph) : (S ⊔ T).toGraph = (S.toGraph_compatible T).union :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_or_left]

/-- A singleton subgraph of `H` converts to the edgeless single-vertex multigraph. -/
@[simp]
theorem _root_.SimpleGraph.toGraph_singletonSubgraph (H : SimpleGraph α) (v : α) :
    (H.singletonSubgraph v).toGraph = Graph.noEdge {v} (Sym2 α) :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp

/-- When `S.edgeSet` is finite, `S.toGraph` has finitely many actual edges. -/
instance instFiniteEdgeSetToGraph (S : H.Subgraph) [Finite S.edgeSet] : Finite E(S.toGraph) := by
  rw [S.edgeSet_toGraph]; infer_instance

@[simp]
theorem isSpanningSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph ≤s Graph.ofSimpleGraph H ↔ S.IsSpanning := by
  rw [Graph.isSpanningSubgraph_iff, Subgraph.isSpanning_iff]; simp [S.toGraph_le_ofSimpleGraph]

@[simp]
theorem isInducedSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph.IsInducedSubgraph (Graph.ofSimpleGraph H) ↔ S.IsInduced := by
  rw [Graph.isInducedSubgraph_iff]
  refine ⟨fun ⟨_, h⟩ x hx y hy hxy ↦ ?_, fun h ↦ ⟨S.toGraph_le_ofSimpleGraph, ?_⟩⟩
  · exact ((S.toGraph_isLink s(x, y) x y).mp
      (h (by simpa [Graph.ofSimpleGraph_isLink] using hxy) hx hy)).2
  · rintro e x y he hx hy
    rw [Graph.ofSimpleGraph_isLink] at he; rcases he with ⟨rfl, he⟩
    exact ⟨rfl, h hx hy (H.mem_edgeSet.mp he)⟩

/-- The underlying simple graph of `S.toGraph` is canonically isomorphic to `S.coe`. -/
def toGraphToSimpleGraphIso (S : H.Subgraph) : S.toGraph.toSimpleGraph ≃g S.coe where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]
  map_rel_iff' {x y} := by rw [S.toGraph.toSimpleGraph_adj_iff, S.toGraph_adj_iff, S.coe_adj]; rfl

@[simp] theorem coe_toGraphToSimpleGraphIso_apply (S : H.Subgraph) (x : V(S.toGraph)) :
    (S.toGraphToSimpleGraphIso x : α) = x := (rfl)

@[simp] theorem coe_toGraphToSimpleGraphIso_symm_apply (S : H.Subgraph) (x : S.verts) :
    (S.toGraphToSimpleGraphIso.symm x : α) = x := (rfl)

/-- The multigraph built from the coerced simple graph `S.coe` is canonically isomorphic to
`S.toGraph`. -/
noncomputable def ofSimpleGraphCoeIso (S : H.Subgraph) :
    Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph where
  vertexEquiv := (Equiv.Set.univ S.verts).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]).symm
  edgeEquiv := Equiv.ofBijective
    (fun e ↦ ⟨e.1.map Subtype.val, by
      have hm : e.1 ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using e.2
      rw [S.edgeSet_toGraph]; rwa [S.edgeSet_coe] at hm⟩)
    ⟨fun _ _ h ↦ Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h)),
     fun ⟨f, hf⟩ ↦ by
      rw [S.edgeSet_toGraph, ← S.image_coe_edgeSet_coe] at hf
      obtain ⟨e, he, rfl⟩ := hf
      exact ⟨⟨e, by simpa only [Graph.edgeSet_ofSimpleGraph] using he⟩, rfl⟩⟩
  map_isLink_iff e x y := by
    simp only [toGraph_isLink, Graph.ofSimpleGraph_isLink]
    have hm : e.1 ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using e.2
    refine ⟨fun ⟨he, _⟩ ↦ ⟨Sym2.map.injective Subtype.val_injective he, hm⟩,
      fun ⟨he, _⟩ ↦ ⟨congrArg (Sym2.map Subtype.val) he, ?_⟩⟩
    rwa [he, SimpleGraph.mem_edgeSet, S.coe_adj] at hm

@[simp] theorem coe_ofSimpleGraphCoeIso_vertexEquiv_apply (S : H.Subgraph)
    (x : V(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.vertexEquiv x : α) = (x.1 : α) := (rfl)

@[simp] theorem coe_ofSimpleGraphCoeIso_edgeEquiv_apply (S : H.Subgraph)
    (e : E(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.edgeEquiv e : Sym2 α) = e.1.map Subtype.val := (rfl)

end SimpleGraph.Subgraph

namespace Graph.IsSubgraph

variable {α : Type u} {H : SimpleGraph α} {K L : Graph α (Sym2 α)}

/-- Recover a bundled simple-graph subgraph `H.Subgraph` from a multigraph subgraph
`K ≤ Graph.ofSimpleGraph H`. -/
def toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) : H.Subgraph where
  verts := V(K)
  Adj := K.Adj
  adj_sub hxy := (Graph.ofSimpleGraph_adj_iff _ _).mp (hxy.mono hK)
  edge_vert hxy := hxy.left_mem
  symm := ⟨fun _ _ hxy ↦ hxy.symm⟩

@[simp, grind =] theorem verts_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.verts = V(K) := (rfl)

@[simp, grind =] theorem toSimpleGraphSubgraph_adj (hK : K ≤ Graph.ofSimpleGraph H) (x y : α) :
    hK.toSimpleGraphSubgraph.Adj x y ↔ K.Adj x y := (Iff.rfl)

@[simp, grind =]
theorem edgeSet_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.edgeSet = E(K) := by
  ext e; induction e using Sym2.ind with | _ x y =>
  rw [SimpleGraph.Subgraph.mem_edgeSet, toSimpleGraphSubgraph_adj]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun he ↦ ?_⟩
  · have hf' := hf.mono hK; rw [Graph.ofSimpleGraph_isLink] at hf'; exact hf'.1 ▸ hf.edge_mem
  · obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
    have huv' := huv.mono hK; rw [Graph.ofSimpleGraph_isLink] at huv'
    rcases Sym2.eq_iff.mp huv'.1.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [huv.adj, huv.symm.adj]

@[simp]
theorem toGraph_toSimpleGraphSubgraph (hK : K ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph.toGraph = K := by
  refine Graph.ext rfl fun e x y ↦ ?_
  rw [SimpleGraph.Subgraph.toGraph_isLink, toSimpleGraphSubgraph_adj]
  refine ⟨fun ⟨he, _, hf⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hf' := hf.mono hK; rw [Graph.ofSimpleGraph_isLink] at hf'; exact he ▸ hf'.1 ▸ hf
  · have h' := h.mono hK; rw [Graph.ofSimpleGraph_isLink] at h'; exact ⟨h'.1, h.adj⟩

@[simp] theorem _root_.SimpleGraph.Subgraph.toSimpleGraphSubgraph_toGraph (S : H.Subgraph)
    (h : S.toGraph ≤ Graph.ofSimpleGraph H) : h.toSimpleGraphSubgraph = S :=
  SimpleGraph.Subgraph.toGraph_injective (toGraph_toSimpleGraphSubgraph h)

@[simp] theorem toSimpleGraphSubgraph_le_iff (hK : K ≤ Graph.ofSimpleGraph H)
    (hL : L ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph ≤ hL.toSimpleGraphSubgraph ↔ K ≤ L := by
  rw [← SimpleGraph.Subgraph.toGraph_le_toGraph_iff, toGraph_toSimpleGraphSubgraph,
    toGraph_toSimpleGraphSubgraph]

@[simp] theorem toSimpleGraphSubgraph_eq_iff (hK : K ≤ Graph.ofSimpleGraph H)
    (hL : L ≤ Graph.ofSimpleGraph H) :
    hK.toSimpleGraphSubgraph = hL.toSimpleGraphSubgraph ↔ K = L := by
  rw [← SimpleGraph.Subgraph.toGraph_inj, toGraph_toSimpleGraphSubgraph,
    toGraph_toSimpleGraphSubgraph]

@[simp] theorem toSimpleGraphSubgraph_ofSimpleGraph
    (h : Graph.ofSimpleGraph H ≤ Graph.ofSimpleGraph H) : h.toSimpleGraphSubgraph = ⊤ :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

@[simp] theorem toSimpleGraphSubgraph_noEdge_singleton {v : α}
    (hv : Graph.noEdge {v} (Sym2 α) ≤ Graph.ofSimpleGraph H) :
    hv.toSimpleGraphSubgraph = H.singletonSubgraph v :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

@[simp] theorem toSimpleGraphSubgraph_inf (hK : K ≤ Graph.ofSimpleGraph H)
    (hL : L ≤ Graph.ofSimpleGraph H) :
    (inf_le_left.trans hK : K ⊓ L ≤ Graph.ofSimpleGraph H).toSimpleGraphSubgraph =
      hK.toSimpleGraphSubgraph ⊓ hL.toSimpleGraphSubgraph :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

@[simp] theorem toSimpleGraphSubgraph_union (hK : K ≤ Graph.ofSimpleGraph H)
    (hL : L ≤ Graph.ofSimpleGraph H) :
    (Graph.IsSubgraph.union_le hK hL).toSimpleGraphSubgraph =
      hK.toSimpleGraphSubgraph ⊔ hL.toSimpleGraphSubgraph := by
  apply SimpleGraph.Subgraph.toGraph_injective
  rw [toGraph_toSimpleGraphSubgraph, SimpleGraph.Subgraph.toGraph_sup]
  exact Graph.ext (by simp) fun _ _ _ ↦ by simp

end Graph.IsSubgraph

namespace SimpleGraph

variable {α : Type u}

/-- Subgraphs `S : H.Subgraph` of a simple graph `H` are order-isomorphic to multigraph subgraphs
`K ≤ Graph.ofSimpleGraph H`. -/
def subgraphOfSimpleGraphOrderIso (H : SimpleGraph α) :
    H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H) where
  toFun S := ⟨S.toGraph, S.toGraph_le_ofSimpleGraph⟩
  invFun K := K.2.toSimpleGraphSubgraph
  left_inv S := S.toSimpleGraphSubgraph_toGraph _
  right_inv K := Subtype.ext K.2.toGraph_toSimpleGraphSubgraph
  map_rel_iff' := Subgraph.toGraph_le_toGraph_iff

@[simp] theorem coe_subgraphOfSimpleGraphOrderIso_apply (H : SimpleGraph α) (S : H.Subgraph) :
    (H.subgraphOfSimpleGraphOrderIso S : Graph α (Sym2 α)) = S.toGraph := (rfl)

@[simp] theorem subgraphOfSimpleGraphOrderIso_symm_apply (H : SimpleGraph α)
    (K : Set.Iic (Graph.ofSimpleGraph H)) :
    H.subgraphOfSimpleGraphOrderIso.symm K = K.2.toSimpleGraphSubgraph := (rfl)

end SimpleGraph

namespace Graph

/-- When `H.edgeSet` is finite, `Graph.ofSimpleGraph H` has finitely many actual edges. -/
instance instFiniteEdgeSetOfSimpleGraph {α : Type u} (H : SimpleGraph α) [Finite H.edgeSet] :
    Finite E(Graph.ofSimpleGraph H) := by
  rw [Graph.edgeSet_ofSimpleGraph]; infer_instance

end Graph
