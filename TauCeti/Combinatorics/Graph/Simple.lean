/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Lattice
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import TauCeti.Combinatorics.Graph.EdgeEnds
public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.Union

/-!
# Simple multigraphs and their underlying simple graphs

A simple multigraph has no loops and at most one edge between any two vertices. Consequently,
its actual edges are canonically equivalent to the edges of its underlying `SimpleGraph`, by
sending an edge to its unordered pair of ends.

This edge equivalence combines with the identity equivalence on actual vertices to identify a
simple multigraph `G` with `Graph.ofSimpleGraph G.toSimpleGraph`. It supplies the reverse of
Mathlib's `Graph.toSimpleGraphOfSimpleGraphIso`, so the two graph representations can be used
interchangeably when edge identities carry no additional information.

For a simple graph `G`, this file also identifies `G.Subgraph` with the graphs below
`Graph.ofSimpleGraph G`: `SimpleGraph.Subgraph.toGraph` equips a simple subgraph with unordered
pairs as edge identities, while `Graph.toSimpleGraphSubgraph` forgets those redundant identities.
Together they assemble into an order isomorphism
`SimpleGraph.subgraphOfSimpleGraphOrderIso : G.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph G)`
compatible with intersections, compatible multigraph unions, spanning and induced subgraph
predicates, simplicity, and edge-set finiteness, along with canonical isomorphisms
`S.toGraph.toSimpleGraph ≃g S.coe` and `Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.

## Main declarations

* `Graph.edgeEndsEquiv`: actual edges of a simple multigraph are the edges of its underlying
  simple graph.
* `Graph.ofSimpleGraphEdgeSetEquiv`: actual edges of the multigraph built from a simple graph
  are the edges of that simple graph.
* `Graph.ofSimpleGraphToSimpleGraphIso`: the canonical multigraph isomorphism from the graph
  reconstructed from the underlying simple graph to the original simple multigraph.
* `Graph.Iso.toSimpleGraphIso`: an arbitrary multigraph isomorphism induces an isomorphism of
  underlying simple graphs.
* `SimpleGraph.Subgraph.toGraph` and `Graph.toSimpleGraphSubgraph`: the correspondence between
  subgraphs of `G` and graphs below `Graph.ofSimpleGraph G`.
* `SimpleGraph.Subgraph.toSimpleGraphToGraphIso`: canonical simple-graph isomorphism
  `S.toGraph.toSimpleGraph ≃g S.coe`.
* `SimpleGraph.Subgraph.ofSimpleGraphCoeIso`: canonical multigraph isomorphism
  `Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.
* `SimpleGraph.subgraphOfSimpleGraphOrderIso`: the order isomorphism
  `G.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph G)`.
-/

public section

open Set
open scoped Graph Sym2

universe u v

namespace Graph

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- A nonloop link gives adjacency in the underlying simple graph. -/
theorem IsLink.toSimpleGraph_adj {x y : V} {e : E} (h : G.IsLink e x y)
    (hxy : x ≠ y) : G.toSimpleGraph.Adj ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
  ⟨fun heq ↦ hxy (Subtype.mk.inj heq), h.adj⟩

private theorem edgeEnds_mem_toSimpleGraph_edgeSet [G.Simple] (e : G.edgeSet) :
    G.edgeEnds e ∈ G.toSimpleGraph.edgeSet := by
  rw [← Sym2.mk_fst_out_snd_out (G.edgeEnds e), SimpleGraph.mem_edgeSet,
    G.toSimpleGraph_adj_iff]
  exact ((G.edgeEnds_eq_iff_isLink e _ _).1
    (Sym2.mk_fst_out_snd_out (G.edgeEnds e)).symm).adj

private theorem edgeEnds_injective [G.Simple] : Function.Injective G.edgeEnds := by
  intro e f hef
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  let x' : G.vertexSet := ⟨x, hxy.left_mem⟩
  let y' : G.vertexSet := ⟨y, hxy.right_mem⟩
  have he : G.edgeEnds e = s(x', y') := (G.edgeEnds_eq_iff_isLink e x' y').2 hxy
  have hf : G.edgeEnds f = s(x', y') := hef.symm.trans he
  exact Subtype.ext (hxy.eq ((G.edgeEnds_eq_iff_isLink f x' y').1 hf))

private theorem edgeEnds_surjective [G.Simple] :
    Function.Surjective fun e : G.edgeSet ↦
      (⟨G.edgeEnds e, edgeEnds_mem_toSimpleGraph_edgeSet e⟩ : G.toSimpleGraph.edgeSet) := by
  intro p
  let x := p.val.out.1
  let y := p.val.out.2
  have hadj : G.toSimpleGraph.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk_fst_out_snd_out]
    exact p.property
  obtain ⟨e, he⟩ := (G.toSimpleGraph_adj_iff x y).1 hadj
  let e' : G.edgeSet := ⟨e, he.edge_mem⟩
  refine ⟨e', Subtype.ext ?_⟩
  exact ((G.edgeEnds_eq_iff_isLink e' x y).2 he).trans
    (Sym2.mk_fst_out_snd_out p.val)

/-- The actual edges of a simple multigraph are canonically equivalent to the edges of its
underlying simple graph. The equivalence sends each edge identity to its unordered pair of ends.
-/
noncomputable def edgeEndsEquiv (G : Graph V E) [G.Simple] :
    G.edgeSet ≃ G.toSimpleGraph.edgeSet :=
  Equiv.ofBijective
    (fun e ↦ ⟨G.edgeEnds e, edgeEnds_mem_toSimpleGraph_edgeSet e⟩)
    ⟨fun _ _ h ↦ edgeEnds_injective (Subtype.ext_iff.mp h), edgeEnds_surjective⟩

/-- The edge equivalence from a simple multigraph to its underlying simple graph is given by
`Graph.edgeEnds`. -/
@[simp]
theorem coe_edgeEndsEquiv_apply (G : Graph V E) [G.Simple] (e : G.edgeSet) :
    (G.edgeEndsEquiv e : Sym2 G.vertexSet) = G.edgeEnds e :=
  (rfl)

/-- The edge selected by the inverse endpoint equivalence has the prescribed unordered ends. -/
@[simp]
theorem edgeEnds_edgeEndsEquiv_symm_apply (G : Graph V E) [G.Simple]
    (p : G.toSimpleGraph.edgeSet) :
    G.edgeEnds (G.edgeEndsEquiv.symm p) = p := by
  exact congrArg Subtype.val (G.edgeEndsEquiv.apply_symm_apply p)

/-- The actual edges of the multigraph built from a simple graph are exactly the edges of that
simple graph. -/
def ofSimpleGraphEdgeSetEquiv {α : Type*} (H : SimpleGraph α) :
    (ofSimpleGraph H).edgeSet ≃ H.edgeSet :=
  Equiv.subtypeEquivRight fun _ ↦ by rw [edgeSet_ofSimpleGraph]

/-- The edge equivalence `Graph.ofSimpleGraphEdgeSetEquiv` does not change the underlying
unordered pair. -/
@[simp]
theorem coe_ofSimpleGraphEdgeSetEquiv_apply {α : Type*} (H : SimpleGraph α)
    (e : (ofSimpleGraph H).edgeSet) :
    (ofSimpleGraphEdgeSetEquiv H e : Sym2 α) = e :=
  (rfl)

/-- The inverse of `Graph.ofSimpleGraphEdgeSetEquiv` does not change the underlying unordered
pair. -/
@[simp]
theorem coe_ofSimpleGraphEdgeSetEquiv_symm_apply {α : Type*} (H : SimpleGraph α)
    (e : H.edgeSet) :
    ((ofSimpleGraphEdgeSetEquiv H).symm e : Sym2 α) = e :=
  (rfl)

/-- Reconstructing a simple multigraph from its underlying simple graph gives an isomorphic
multigraph. The isomorphism fixes actual vertices and identifies an unordered pair of adjacent
vertices with the unique original edge having those ends. -/
noncomputable def ofSimpleGraphToSimpleGraphIso (G : Graph V E) [G.Simple] :
    Iso (ofSimpleGraph G.toSimpleGraph) G where
  vertexEquiv := Equiv.Set.univ G.vertexSet
  edgeEquiv := (ofSimpleGraphEdgeSetEquiv G.toSimpleGraph).trans G.edgeEndsEquiv.symm
  map_isLink_iff e x y := by
    simp only [Equiv.trans_apply]
    rw [← G.edgeEnds_eq_iff_isLink, G.edgeEnds_edgeEndsEquiv_symm_apply]
    simp only [ofSimpleGraph_isLink, coe_ofSimpleGraphEdgeSetEquiv_apply]
    constructor
    · intro h
      exact ⟨h, by simpa only [edgeSet_ofSimpleGraph] using e.property⟩
    · exact fun h ↦ h.1

/-- The reverse simple-graph round-trip isomorphism fixes each actual vertex. -/
@[simp]
theorem ofSimpleGraphToSimpleGraphIso_vertexEquiv_apply (G : Graph V E) [G.Simple]
    (x : (ofSimpleGraph G.toSimpleGraph).vertexSet) :
    (G.ofSimpleGraphToSimpleGraphIso.vertexEquiv x : V) = (x.val : G.vertexSet) :=
  (rfl)

/-- The original edge corresponding to an edge of the reconstructed graph has exactly the
displayed unordered pair of ends. This is not a simp lemma: `Graph.Iso.edgeEnds_edgeEquiv`
rewrites its left-hand side, and
`Graph.map_vertexEquiv_edgeEnds_ofSimpleGraphToSimpleGraphIso` is the simp-normal form. -/
theorem edgeEnds_ofSimpleGraphToSimpleGraphIso_edgeEquiv_apply
    (G : Graph V E) [G.Simple] (e : (ofSimpleGraph G.toSimpleGraph).edgeSet) :
    G.edgeEnds (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv e) = e :=
  G.edgeEnds_edgeEndsEquiv_symm_apply (ofSimpleGraphEdgeSetEquiv G.toSimpleGraph e)

/-- The reverse simple-graph round-trip isomorphism carries the ends of an edge of the
reconstructed graph to the displayed unordered pair itself. -/
@[simp]
theorem map_vertexEquiv_edgeEnds_ofSimpleGraphToSimpleGraphIso
    (G : Graph V E) [G.Simple] (e : (ofSimpleGraph G.toSimpleGraph).edgeSet) :
    ((ofSimpleGraph G.toSimpleGraph).edgeEnds e).map G.ofSimpleGraphToSimpleGraphIso.vertexEquiv =
      e := by
  rw [← Iso.edgeEnds_edgeEquiv, edgeEnds_ofSimpleGraphToSimpleGraphIso_edgeEquiv_apply]

/-- In the inverse round-trip isomorphism, an original edge is sent to its unordered pair of
ends. -/
@[simp]
theorem coe_ofSimpleGraphToSimpleGraphIso_symm_edgeEquiv_apply
    (G : Graph V E) [G.Simple] (e : G.edgeSet) :
    (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv.symm e : Sym2 G.vertexSet) = G.edgeEnds e := by
  have h := G.edgeEnds_ofSimpleGraphToSimpleGraphIso_edgeEquiv_apply
    (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

namespace Iso

variable {V' E' : Type*} {H : Graph V' E'}

/-- A multigraph isomorphism induces an isomorphism of the underlying simple graphs,
forgetting loops and parallel-edge identities. -/
def toSimpleGraphIso (f : Iso G H) : G.toSimpleGraph ≃g H.toSimpleGraph where
  toEquiv := f.vertexEquiv
  map_rel_iff' := by
    intro x y
    simp only [toSimpleGraph_adj, f.vertexEquiv.injective.ne_iff]
    exact and_congr_right fun _ ↦ f.map_adj_iff x y

/-- The induced simple-graph isomorphism uses the original vertex equivalence. -/
@[simp]
theorem toSimpleGraphIso_apply (f : Iso G H) (x : V(G)) :
    f.toSimpleGraphIso x = f.vertexEquiv x := (rfl)

/-- The inverse induced isomorphism uses the inverse vertex equivalence. -/
@[simp]
theorem toSimpleGraphIso_symm_apply (f : Iso G H) (x : V(H)) :
    f.toSimpleGraphIso.symm x = f.vertexEquiv.symm x := by
  apply f.toSimpleGraphIso.injective
  simp

/-- Simplification sends the identity multigraph isomorphism to the identity. -/
@[simp]
theorem toSimpleGraphIso_refl : (refl G).toSimpleGraphIso = SimpleGraph.Iso.refl := by
  ext x
  simp

/-- Simplification commutes with inversion of isomorphisms. -/
@[simp]
theorem toSimpleGraphIso_symm (f : Iso G H) :
    f.symm.toSimpleGraphIso = f.toSimpleGraphIso.symm := by
  ext x
  simp

/-- Simplification commutes with composition of isomorphisms. -/
@[simp]
theorem toSimpleGraphIso_trans {V'' E'' : Type*} {K : Graph V'' E''}
    (f : Iso G H) (g : Iso H K) :
    (f.trans g).toSimpleGraphIso = f.toSimpleGraphIso.trans g.toSimpleGraphIso := by
  ext x
  simp

end Iso

end Graph

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-- Regard a subgraph of a simple graph as an edge-labelled graph on the ambient vertex type.
Its edge identities are the unordered pairs in the subgraph's edge set. -/
def toGraph (H : G.Subgraph) : Graph V (Sym2 V) where
  vertexSet := H.verts
  edgeSet := H.edgeSet
  IsLink e x y := e = s(x, y) ∧ H.Adj x y
  isLink_symm _ _ := ⟨fun _ _ h ↦ ⟨h.1.trans Sym2.eq_swap, H.adj_symm h.2⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := by
    exact (Sym2.eq_iff.mp (h₁.1.symm.trans h₂.1)).imp And.left And.left
  edge_mem_iff_exists_isLink e := by
    induction e using Sym2.ind with
    | _ x y =>
        rw [SimpleGraph.Subgraph.mem_edgeSet]
        constructor
        · exact fun h ↦ ⟨x, y, rfl, h⟩
        · rintro ⟨a, b, hab, hAdj⟩
          rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hAdj
          · exact H.adj_symm hAdj
  left_mem_of_isLink := fun _ _ _ h ↦ H.edge_vert h.2

@[grind =, simp]
theorem vertexSet_toGraph (H : G.Subgraph) : H.toGraph.vertexSet = H.verts := (rfl)

@[grind =, simp]
theorem edgeSet_toGraph (H : G.Subgraph) : H.toGraph.edgeSet = H.edgeSet := (rfl)

@[grind =, simp]
theorem toGraph_isLink (H : G.Subgraph) (e : Sym2 V) (x y : V) :
    H.toGraph.IsLink e x y ↔ e = s(x, y) ∧ H.Adj x y := (Iff.rfl)

@[grind =, simp]
theorem toGraph_adj (H : G.Subgraph) (x y : V) : H.toGraph.Adj x y ↔ H.Adj x y := by
  constructor
  · rintro ⟨e, rfl, hxy⟩
    exact hxy
  · exact fun hxy ↦ ⟨s(x, y), rfl, hxy⟩

/-- The graph associated to a simple subgraph is a subgraph of the graph associated to the
ambient simple graph. -/
@[grind .]
theorem toGraph_le_ofSimpleGraph (H : G.Subgraph) : H.toGraph ≤ Graph.ofSimpleGraph G := by
  refine ⟨by simp, fun e x y h ↦ ?_⟩
  rw [Graph.ofSimpleGraph_isLink]
  exact ⟨h.1, by simpa [h.1] using H.adj_sub h.2⟩

end SimpleGraph.Subgraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V}

/-- A subgraph of `Graph.ofSimpleGraph G`, expressed as a subgraph of `G` with the same vertices
and adjacencies. -/
def toSimpleGraphSubgraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G) : G.Subgraph where
  verts := K.vertexSet
  Adj := K.Adj
  adj_sub h := (ofSimpleGraph_adj_iff _ _).mp (h.mono hK)
  edge_vert h := h.left_mem
  symm := ⟨fun _ _ ↦ Adj.symm⟩

@[grind =, simp]
theorem verts_toSimpleGraphSubgraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSimpleGraphSubgraph hK).verts = K.vertexSet := (rfl)

@[grind =, simp]
theorem adj_toSimpleGraphSubgraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G)
    (x y : V) : (K.toSimpleGraphSubgraph hK).Adj x y ↔ K.Adj x y := (Iff.rfl)

/-- Passing from a simple subgraph to an edge-labelled graph and back recovers the subgraph. -/
@[simp]
theorem _root_.SimpleGraph.Subgraph.toSimpleGraphSubgraph_toGraph (H : G.Subgraph)
    (h : H.toGraph ≤ Graph.ofSimpleGraph G) : H.toGraph.toSimpleGraphSubgraph h = H := by
  ext x y
  · rfl
  · simp

/-- A subgraph of `Graph.ofSimpleGraph G` is recovered from its associated simple subgraph. -/
@[simp]
theorem toGraph_toSimpleGraphSubgraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) : (K.toSimpleGraphSubgraph hK).toGraph = K := by
  refine @Graph.ext V (Sym2 V) _ _ rfl ?_
  intro e x y
  constructor
  · rintro ⟨rfl, hxy⟩
    obtain ⟨f, hf⟩ := hxy
    have hfg := hK.isLink_mono hf
    rw [Graph.ofSimpleGraph_isLink] at hfg
    simpa [hfg.1] using hf
  · intro h
    have hg := hK.isLink_mono h
    rw [Graph.ofSimpleGraph_isLink] at hg
    exact ⟨hg.1, ⟨e, h⟩⟩

@[grind =, simp]
theorem edgeSet_toSimpleGraphSubgraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) : (K.toSimpleGraphSubgraph hK).edgeSet = K.edgeSet := by
  rw [← SimpleGraph.Subgraph.edgeSet_toGraph, K.toGraph_toSimpleGraphSubgraph]

/-- The associated simple subgraph respects equality of the multigraphs and is independent of
the subgraph proofs. -/
theorem toSimpleGraphSubgraph_congr {K L : Graph V (Sym2 V)}
    (h : K = L) (hK : K ≤ Graph.ofSimpleGraph G) (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSimpleGraphSubgraph hK = L.toSimpleGraphSubgraph hL := by
  subst L
  congr

/-- The graph associated to the ambient simple graph becomes the top subgraph. -/
@[simp]
theorem toSimpleGraphSubgraph_ofSimpleGraph
    (h : Graph.ofSimpleGraph G ≤ Graph.ofSimpleGraph G) :
    (Graph.ofSimpleGraph G).toSimpleGraphSubgraph h = ⊤ := by
  ext x y <;> simp

/-- A one-vertex graph becomes the corresponding singleton subgraph of the ambient simple graph. -/
@[simp]
theorem toSimpleGraphSubgraph_noEdge_singleton (v : V)
    (h : Graph.noEdge {v} (Sym2 V) ≤ Graph.ofSimpleGraph G) :
    (Graph.noEdge {v} (Sym2 V)).toSimpleGraphSubgraph h = G.singletonSubgraph v := by
  ext x y
  · simp [toSimpleGraphSubgraph]
  · simp [toSimpleGraphSubgraph, Graph.Adj]

end Graph

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-- The top simple subgraph corresponds to its whole edge-labelled graph. -/
@[simp]
theorem toGraph_top : (⊤ : G.Subgraph).toGraph = Graph.ofSimpleGraph G := by
  simpa using Graph.toGraph_toSimpleGraphSubgraph (Graph.ofSimpleGraph G) le_rfl

/-- The bottom simple subgraph corresponds to the graph with no vertices or edges. -/
@[simp]
theorem toGraph_bot : (⊥ : G.Subgraph).toGraph = ⊥ := by
  apply Graph.ext <;> simp

/-- A singleton simple subgraph corresponds to the one-vertex graph with no edges. -/
@[simp]
theorem toGraph_singletonSubgraph (v : V) :
    (G.singletonSubgraph v).toGraph = Graph.noEdge {v} (Sym2 V) := by
  apply Graph.ext <;> simp

/-- Converting simple subgraphs to edge-labelled graphs reflects and preserves inclusion. -/
@[simp]
theorem toGraph_le_toGraph (H L : G.Subgraph) : H.toGraph ≤ L.toGraph ↔ H ≤ L := by
  constructor
  · intro h
    refine ⟨by simpa using h.vertexSet_mono, ?_⟩
    intro x y hadj
    exact (L.toGraph_isLink s(x, y) x y).mp
      (h.isLink_mono ((H.toGraph_isLink s(x, y) x y).mpr ⟨rfl, hadj⟩)) |>.2
  · intro h
    refine ⟨by simpa using h.1, fun e x y he ↦ ?_⟩
    exact (L.toGraph_isLink e x y).mpr ⟨he.1, h.2 he.2⟩

/-- Converting simple subgraphs to edge-labelled graphs is injective. -/
@[simp]
theorem toGraph_inj {H L : G.Subgraph} : H.toGraph = L.toGraph ↔ H = L := by
  constructor
  · intro h
    exact le_antisymm ((toGraph_le_toGraph H L).mp h.le)
      ((toGraph_le_toGraph L H).mp h.ge)
  · exact congrArg toGraph

/-- The multigraph associated to any simple-graph subgraph is simple (loopless with no parallel
edges). -/
instance instSimpleToGraph (S : G.Subgraph) : S.toGraph.Simple where
  not_isLoopAt e x h := by rw [Graph.IsLoopAt, toGraph_isLink] at h; exact S.loopless.irrefl x h.2
  eq_of_isLink _ _ _ _ h₁ h₂ := by rw [toGraph_isLink] at h₁ h₂; exact h₁.1.trans h₂.1.symm

@[gcongr]
theorem toGraph_mono {S T : G.Subgraph} (h : S ≤ T) : S.toGraph ≤ T.toGraph :=
  (toGraph_le_toGraph S T).mpr h

theorem toGraph_injective : Function.Injective (toGraph (G := G)) :=
  fun _ _ ↦ toGraph_inj.mp

@[simp]
theorem toGraph_lt_toGraph (S T : G.Subgraph) : S.toGraph < T.toGraph ↔ S < T :=
  lt_iff_lt_of_le_iff_le' (toGraph_le_toGraph T S) (toGraph_le_toGraph S T)

@[simp]
theorem toGraph_inf (S T : G.Subgraph) : (S ⊓ T).toGraph = S.toGraph ⊓ T.toGraph :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_left_comm, and_assoc]

/-- Any two subgraphs of the same simple graph convert to compatible multigraphs. -/
theorem toGraph_compatible (S T : G.Subgraph) : S.toGraph.Compatible T.toGraph :=
  .of_le_le S.toGraph_le_ofSimpleGraph T.toGraph_le_ofSimpleGraph

/-- The supremum of two simple-graph subgraphs corresponds to the compatible multigraph union. -/
theorem toGraph_sup (S T : G.Subgraph) : (S ⊔ T).toGraph = (S.toGraph_compatible T).union :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_or_left]

/-- When `S.edgeSet` is finite, `S.toGraph` has finitely many actual edges. -/
instance instFiniteEdgeSetToGraph (S : G.Subgraph) [Finite S.edgeSet] : Finite E(S.toGraph) := by
  rw [S.edgeSet_toGraph]; infer_instance

@[simp]
theorem isSpanningSubgraph_toGraph_iff {S : G.Subgraph} :
    S.toGraph ≤s Graph.ofSimpleGraph G ↔ S.IsSpanning := by
  rw [Graph.isSpanningSubgraph_iff, Subgraph.isSpanning_iff]; simp [S.toGraph_le_ofSimpleGraph]

@[simp]
theorem isInducedSubgraph_toGraph_iff {S : G.Subgraph} :
    S.toGraph.IsInducedSubgraph (Graph.ofSimpleGraph G) ↔ S.IsInduced := by
  rw [Graph.isInducedSubgraph_iff]
  refine ⟨fun ⟨_, h⟩ x hx y hy hxy ↦ ?_, fun h ↦ ⟨S.toGraph_le_ofSimpleGraph, ?_⟩⟩
  · exact ((S.toGraph_isLink s(x, y) x y).mp
      (h (by simpa [Graph.ofSimpleGraph_isLink] using hxy)
        (S.vertexSet_toGraph.symm ▸ hx) (S.vertexSet_toGraph.symm ▸ hy))).2
  · rintro e x y he hx hy
    rw [Graph.ofSimpleGraph_isLink] at he; rcases he with ⟨rfl, he⟩
    exact (S.toGraph_isLink _ _ _).mpr
      ⟨rfl, h (S.vertexSet_toGraph ▸ hx) (S.vertexSet_toGraph ▸ hy) (G.mem_edgeSet.mp he)⟩

/-- The underlying simple graph of `S.toGraph` is canonically isomorphic to `S.coe`. -/
def toSimpleGraphToGraphIso (S : G.Subgraph) : S.toGraph.toSimpleGraph ≃g S.coe where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]
  map_rel_iff' {x y} := by rw [S.toGraph.toSimpleGraph_adj_iff, S.toGraph_adj, S.coe_adj]; rfl

@[simp] theorem coe_toSimpleGraphToGraphIso_apply (S : G.Subgraph) (x : V(S.toGraph)) :
    (S.toSimpleGraphToGraphIso x : V) = x := (rfl)

@[simp] theorem coe_toSimpleGraphToGraphIso_symm_apply (S : G.Subgraph) (x : S.verts) :
    (S.toSimpleGraphToGraphIso.symm x : V) = x := (rfl)

/-- The multigraph built from the coerced simple graph `S.coe` is canonically isomorphic to
`S.toGraph`. -/
noncomputable def ofSimpleGraphCoeIso (S : G.Subgraph) :
    Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph where
  vertexEquiv := (Equiv.Set.univ S.verts).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]).symm
  edgeEquiv := Equiv.ofBijective
    (fun e ↦ ⟨e.val.map Subtype.val, by
      have hm : e.val ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using
          e.property
      rw [S.edgeSet_toGraph]; rwa [S.edgeSet_coe] at hm⟩)
    ⟨fun _ _ h ↦ Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h)),
     fun ⟨f, hf⟩ ↦ by
      rw [S.edgeSet_toGraph, ← S.image_coe_edgeSet_coe] at hf
      obtain ⟨e, he, rfl⟩ := hf
      exact ⟨⟨e, by simpa only [Graph.edgeSet_ofSimpleGraph] using he⟩, rfl⟩⟩
  map_isLink_iff e x y := by
    simp only [toGraph_isLink, Graph.ofSimpleGraph_isLink]
    have hm : e.val ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using e.property
    refine ⟨fun ⟨he, _⟩ ↦ ⟨Sym2.map.injective Subtype.val_injective he, hm⟩,
      fun ⟨he, _⟩ ↦ ⟨congrArg (Sym2.map Subtype.val) he, ?_⟩⟩
    rwa [he, SimpleGraph.mem_edgeSet, S.coe_adj] at hm

@[simp] theorem coe_ofSimpleGraphCoeIso_vertexEquiv_apply (S : G.Subgraph)
    (x : V(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.vertexEquiv x : V) = (x.val : V) := (rfl)

@[simp] theorem coe_ofSimpleGraphCoeIso_vertexEquiv_symm_apply (S : G.Subgraph)
    (x : V(S.toGraph)) :
    ((S.ofSimpleGraphCoeIso.vertexEquiv.symm x).val : V) = (x : V) := (rfl)

@[simp] theorem coe_ofSimpleGraphCoeIso_edgeEquiv_apply (S : G.Subgraph)
    (e : E(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.edgeEquiv e : Sym2 V) = e.val.map Subtype.val := (rfl)

@[simp] theorem map_coe_ofSimpleGraphCoeIso_edgeEquiv_symm_apply (S : G.Subgraph)
    (e : E(S.toGraph)) :
    (S.ofSimpleGraphCoeIso.edgeEquiv.symm e : Sym2 S.verts).map Subtype.val = (e : Sym2 V) := by
  simpa only [coe_ofSimpleGraphCoeIso_edgeEquiv_apply] using
    congrArg Subtype.val (S.ofSimpleGraphCoeIso.edgeEquiv.apply_symm_apply e)

end SimpleGraph.Subgraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V}

/-- The graph with no vertices or edges becomes the bottom simple subgraph. -/
@[simp]
theorem toSimpleGraphSubgraph_bot
    (h : (⊥ : Graph V (Sym2 V)) ≤ Graph.ofSimpleGraph G) :
    (⊥ : Graph V (Sym2 V)).toSimpleGraphSubgraph h = ⊥ := by
  ext x y <;> simp [toSimpleGraphSubgraph, Graph.Adj]

/-- Forgetting edge identities reflects and preserves inclusion between subgraphs of
`Graph.ofSimpleGraph G`. -/
@[simp]
theorem toSimpleGraphSubgraph_le_toSimpleGraphSubgraph
    (K L : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G)
    (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSimpleGraphSubgraph hK ≤ L.toSimpleGraphSubgraph hL ↔ K ≤ L := by
  rw [← SimpleGraph.Subgraph.toGraph_le_toGraph]
  simp

/-- Forgetting edge identities reflects and preserves strict inclusion between subgraphs of
`Graph.ofSimpleGraph G`. -/
@[simp]
theorem toSimpleGraphSubgraph_lt_toSimpleGraphSubgraph
    (K L : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G)
    (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSimpleGraphSubgraph hK < L.toSimpleGraphSubgraph hL ↔ K < L :=
  lt_iff_lt_of_le_iff_le' (toSimpleGraphSubgraph_le_toSimpleGraphSubgraph L K hL hK)
    (toSimpleGraphSubgraph_le_toSimpleGraphSubgraph K L hK hL)

/-- Forgetting edge identities is injective on subgraphs of `Graph.ofSimpleGraph G`. -/
@[simp]
theorem toSimpleGraphSubgraph_inj
    {K L : Graph V (Sym2 V)} (hK : K ≤ Graph.ofSimpleGraph G)
    (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSimpleGraphSubgraph hK = L.toSimpleGraphSubgraph hL ↔ K = L := by
  constructor
  · intro h
    simpa only [toGraph_toSimpleGraphSubgraph] using congrArg SimpleGraph.Subgraph.toGraph h
  · rintro rfl
    rfl

@[simp]
theorem isSpanning_toSimpleGraphSubgraph_iff {K : Graph V (Sym2 V)}
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSimpleGraphSubgraph hK).IsSpanning ↔ K ≤s Graph.ofSimpleGraph G := by
  rw [← SimpleGraph.Subgraph.isSpanningSubgraph_toGraph_iff, toGraph_toSimpleGraphSubgraph]

@[simp]
theorem isInduced_toSimpleGraphSubgraph_iff {K : Graph V (Sym2 V)}
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSimpleGraphSubgraph hK).IsInduced ↔ K.IsInducedSubgraph (Graph.ofSimpleGraph G) := by
  rw [← SimpleGraph.Subgraph.isInducedSubgraph_toGraph_iff, toGraph_toSimpleGraphSubgraph]

/-- Converting the intersection of two subgraphs of `Graph.ofSimpleGraph G` to a simple subgraph
commutes with `⊓`. -/
theorem toSimpleGraphSubgraph_inf {K L : Graph V (Sym2 V)}
    (hK : K ≤ Graph.ofSimpleGraph G) (hL : L ≤ Graph.ofSimpleGraph G)
    (hKL : K ⊓ L ≤ Graph.ofSimpleGraph G) :
    (K ⊓ L).toSimpleGraphSubgraph hKL =
      K.toSimpleGraphSubgraph hK ⊓ L.toSimpleGraphSubgraph hL :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

/-- Converting the compatible union of two subgraphs of `Graph.ofSimpleGraph G` to a simple
subgraph commutes with `⊔`. -/
@[simp]
theorem toSimpleGraphSubgraph_union {K L : Graph V (Sym2 V)} (h : K.Compatible L)
    (hKL : h.union ≤ Graph.ofSimpleGraph G) :
    h.union.toSimpleGraphSubgraph hKL =
      K.toSimpleGraphSubgraph (h.left_le_union.trans hKL) ⊔
        L.toSimpleGraphSubgraph (h.right_le_union.trans hKL) := by
  apply SimpleGraph.Subgraph.toGraph_injective
  rw [toGraph_toSimpleGraphSubgraph, SimpleGraph.Subgraph.toGraph_sup]
  exact Graph.ext (by simp) fun _ _ _ ↦ by simp

/-- When `G.edgeSet` is finite, `Graph.ofSimpleGraph G` has finitely many actual edges. -/
instance instFiniteEdgeSetOfSimpleGraph (G : SimpleGraph V) [Finite G.edgeSet] :
    Finite E(Graph.ofSimpleGraph G) := by
  rw [Graph.edgeSet_ofSimpleGraph]; infer_instance

end Graph

namespace SimpleGraph

variable {V : Type u}

/-- Subgraphs `S : G.Subgraph` of a simple graph `G` are order-isomorphic to multigraph subgraphs
`K ≤ Graph.ofSimpleGraph G`. -/
def subgraphOfSimpleGraphOrderIso (G : SimpleGraph V) :
    G.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph G) where
  toFun S := ⟨S.toGraph, S.toGraph_le_ofSimpleGraph⟩
  invFun K := K.val.toSimpleGraphSubgraph K.property
  left_inv S := S.toSimpleGraphSubgraph_toGraph _
  right_inv K := Subtype.ext (K.val.toGraph_toSimpleGraphSubgraph K.property)
  map_rel_iff' := Subgraph.toGraph_le_toGraph _ _

@[simp] theorem coe_subgraphOfSimpleGraphOrderIso_apply (G : SimpleGraph V) (S : G.Subgraph) :
    (G.subgraphOfSimpleGraphOrderIso S : Graph V (Sym2 V)) = S.toGraph := (rfl)

@[simp] theorem subgraphOfSimpleGraphOrderIso_symm_apply (G : SimpleGraph V)
    (K : Set.Iic (Graph.ofSimpleGraph G)) :
    G.subgraphOfSimpleGraphOrderIso.symm K = K.val.toSimpleGraphSubgraph K.property := (rfl)

end SimpleGraph
