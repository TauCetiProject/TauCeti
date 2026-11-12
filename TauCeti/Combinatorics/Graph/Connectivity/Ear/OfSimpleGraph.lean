/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Ear decompositions of graphs associated to simple graphs

This file transports ear decompositions of `Graph.ofSimpleGraph G` to the subgraph-based ear
decompositions of a simple graph `G`.  A subgraph of `Graph.ofSimpleGraph G` has the same canonical
unordered-pair edge identities as `G`, so it determines a `G.Subgraph`; the construction is inverse
to regarding that simple subgraph as an edge-labelled graph.

The transport preserves the initial vertex or cycle and the underlying walk and kind of every ear.
It therefore lets multigraph ear constructions supply simple-graph decompositions without
discarding their initial subgraph.
-/

public section

open Set
open scoped Sym2

universe u

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

@[simp]
theorem vertexSet_toGraph (H : G.Subgraph) : H.toGraph.vertexSet = H.verts := (rfl)

@[simp]
theorem edgeSet_toGraph (H : G.Subgraph) : H.toGraph.edgeSet = H.edgeSet := (rfl)

@[simp]
theorem toGraph_isLink (H : G.Subgraph) (e : Sym2 V) (x y : V) :
    H.toGraph.IsLink e x y ↔ e = s(x, y) ∧ H.Adj x y := Iff.rfl

/-- The graph associated to a simple subgraph is a subgraph of the graph associated to the
ambient simple graph. -/
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

@[simp]
theorem verts_toSimpleGraphSubgraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSimpleGraphSubgraph hK).verts = K.vertexSet := (rfl)

@[simp]
theorem adj_toSimpleGraphSubgraph (K : Graph V (Sym2 V)) (hK : K ≤ Graph.ofSimpleGraph G)
    (x y : V) : (K.toSimpleGraphSubgraph hK).Adj x y ↔ K.Adj x y := Iff.rfl

/-- Passing from a simple subgraph to an edge-labelled graph and back recovers the subgraph. -/
@[simp]
theorem toGraph_toSimpleGraphSubgraph (H : G.Subgraph) :
    H.toGraph.toSimpleGraphSubgraph H.toGraph_le_ofSimpleGraph = H := by
  ext x y
  · rfl
  · simp [toSimpleGraphSubgraph, Graph.Adj]

/-- A subgraph of `Graph.ofSimpleGraph G` is recovered from its associated simple subgraph. -/
@[simp]
theorem toSimpleGraphSubgraph_toGraph (K : Graph V (Sym2 V))
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

@[simp]
theorem edgeSet_toSimpleGraphSubgraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) : (K.toSimpleGraphSubgraph hK).edgeSet = K.edgeSet := by
  have h := congrArg Graph.edgeSet (K.toSimpleGraphSubgraph_toGraph hK)
  change (K.toSimpleGraphSubgraph hK).edgeSet = K.edgeSet at h
  exact h

/-- The associated simple subgraph is independent of the proof that the multigraph is a
subgraph, and respects equality of the multigraphs. -/
theorem toSimpleGraphSubgraph_congr {K L : Graph V (Sym2 V)}
    (h : K = L) (hK : K ≤ Graph.ofSimpleGraph G) (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSimpleGraphSubgraph hK = L.toSimpleGraphSubgraph hL := by
  subst L
  congr

/-- A one-vertex graph becomes the corresponding singleton subgraph of the ambient simple
graph. -/
@[simp]
theorem noEdge_toSimpleGraphSubgraph (v : V)
    (h : Graph.noEdge {v} (Sym2 V) ≤ Graph.ofSimpleGraph G) :
    (Graph.noEdge {v} (Sym2 V)).toSimpleGraphSubgraph h = G.singletonSubgraph v := by
  ext x y
  · simp [toSimpleGraphSubgraph]
  · simp [toSimpleGraphSubgraph, Graph.Adj]

end Graph

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport an ear of `Graph.ofSimpleGraph G` to an ear over the corresponding simple
subgraph. -/
def toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) (hK : K ≤ Graph.ofSimpleGraph G) :
    G.Ear (K.toSimpleGraphSubgraph hK) :=
  match e with
  | .open _ p hp hs ht hst hinter hedge =>
      .«open» p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using ht) hst
        (by simpa using hinter) (by simpa using hedge)
  | .closed _ p hp hs hinter _ =>
      .closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using hinter)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).kind = match e.kind with
      | .open => .«open»
      | .closed => .closed := by
  cases e with
  | «open» => unfold toSimpleGraph; rw [SimpleGraph.Ear.kind_open, Graph.Ear.kind_open]
  | «closed» => unfold toSimpleGraph; rw [SimpleGraph.Ear.kind_closed, Graph.Ear.kind_closed]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).toWalk =
      ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | «closed» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

/-- Transport commutes with adjoining an ear to its base graph. -/
theorem add_toSimpleGraphSubgraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.add.toSimpleGraphSubgraph e.add_le = (e.toSimpleGraph e.base_le).adjoin := by
  ext x y
  · rw [Graph.verts_toSimpleGraphSubgraph,
      SimpleGraph.Ear.verts_adjoin, Graph.Ear.vertexSet_add,
      Graph.Ear.vertexSet_toGraph, SimpleGraph.Ear.toSubgraph_eq_toWalk,
      SimpleGraph.Walk.verts_toSubgraph, toWalk_toSimpleGraph]
    simp
  · rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet]
    rw [Graph.edgeSet_toSimpleGraphSubgraph,
      SimpleGraph.Ear.edgeSet_adjoin, Graph.Ear.edgeSet_add,
      Graph.Ear.edgeSet_toGraph, SimpleGraph.Ear.toSubgraph_eq_toWalk,
      SimpleGraph.Walk.edgeSet_toSubgraph, toWalk_toSimpleGraph]
    simp

end Graph.Ear

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport the initial vertex or cycle of a multigraph ear decomposition to the corresponding
simple subgraph. -/
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K)
    (hK : K ≤ Graph.ofSimpleGraph G) : G.EarStart (K.toSimpleGraphSubgraph hK) := by
  cases s with
  | vertex v =>
      have h := Graph.noEdge_toSimpleGraphSubgraph v.1 hK
      exact h.symm ▸ .vertex v.1
  | @cycle x p hp =>
      have h : ((Graph.ofSimpleGraph G).walkGraph p).toSimpleGraphSubgraph
          hK = p.toSimpleGraph.toSubgraph := by
        ext a b
        · simp [Graph.toSimpleGraphSubgraph]
        · rw [Graph.adj_toSimpleGraphSubgraph,
            SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
          simp only [Graph.Adj, Graph.Walk.edges_toSimpleGraph]
          constructor
          · rintro ⟨e, he⟩
            rw [Graph.Walk.walkGraph_isLink, Graph.ofSimpleGraph_isLink] at he
            simpa [he.1.1] using he.2
          · intro hab
            refine ⟨s(a, b), (Graph.Walk.walkGraph_isLink p _ _ _).mpr ⟨?_, hab⟩⟩
            rw [Graph.ofSimpleGraph_isLink]
            exact ⟨rfl, p.edges_subset_edgeSet hab⟩
      exact h.symm ▸ .cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

end Graph.EarStart

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

private def ofSimpleGraphStart {H : G.Subgraph} (s : G.EarStart H) :
    G.EarDecomposition H :=
  match s with
  | .vertex v => SimpleGraph.EarDecomposition.vertex G v
  | .cycle c hc => SimpleGraph.EarDecomposition.cycle c hc

@[simp]
private theorem length_ofSimpleGraphStart {H : G.Subgraph} (s : G.EarStart H) :
    (ofSimpleGraphStart s).length = 0 := by cases s <;> simp [ofSimpleGraphStart]

@[simp]
private theorem initial_ofSimpleGraphStart {H : G.Subgraph} (s : G.EarStart H) :
    (ofSimpleGraphStart s).initial = H := by cases s <;> simp [ofSimpleGraphStart]

/-- Transport a decomposition of a subgraph of `Graph.ofSimpleGraph G` to a decomposition of the
corresponding simple subgraph.  The transport preserves the number of ears and the initial
subgraph. -/
theorem exists_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    ∃ d' : G.EarDecomposition (K.toSimpleGraphSubgraph d.final_le),
      d'.length = d.length ∧
        d'.initial =
          (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) := by
  have hprefix : ∀ i : Fin (d.length + 1),
      ∃ d' : G.EarDecomposition
          ((d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i)),
        d'.length = i.1 ∧
          d'.initial =
            (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        let d' := ofSimpleGraphStart (d.start.toSimpleGraph (d.graphAfter_le 0))
        exact ⟨d', by simp [d'], by simp [d']⟩
    | succ i ih =>
        obtain ⟨d', hlength, hinitial⟩ := ih
        let e := (d.earAt i).2
        let hbase := Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i)
          e.base_le (d.graphAfter_le i.castSucc)
        let e' := (e.toSimpleGraph e.base_le).copy hbase
        have hadjoin : e'.adjoin =
            (d.graphAfter i.succ).toSimpleGraphSubgraph (d.graphAfter_le i.succ) := by
          calc
            e'.adjoin = (e.toSimpleGraph e.base_le).adjoin := by
              rw [show e' = (e.toSimpleGraph e.base_le).copy hbase from rfl,
                SimpleGraph.Ear.adjoin_copy]
              calc
                (d.graphAfter i.castSucc).toSimpleGraphSubgraph
                    (d.graphAfter_le i.castSucc) ⊔ (e.toSimpleGraph e.base_le).toSubgraph =
                    (d.earAt i).1.toSimpleGraphSubgraph e.base_le ⊔
                      (e.toSimpleGraph e.base_le).toSubgraph :=
                  congrArg (· ⊔ (e.toSimpleGraph e.base_le).toSubgraph) hbase.symm
                _ = (e.toSimpleGraph e.base_le).adjoin :=
                  (SimpleGraph.Ear.adjoin_def _).symm
            _ = e.add.toSimpleGraphSubgraph e.add_le := e.add_toSimpleGraphSubgraph.symm
            _ = (d.graphAfter i.succ).toSimpleGraphSubgraph (d.graphAfter_le i.succ) :=
              Graph.toSimpleGraphSubgraph_congr (d.graphAfter_succ i).symm
                e.add_le (d.graphAfter_le i.succ)
        let d'' := (d'.snoc e').copy hadjoin
        refine ⟨d'', ?_, ?_⟩
        · rw [show d'' = (d'.snoc e').copy hadjoin from rfl,
            SimpleGraph.EarDecomposition.length_copy,
            SimpleGraph.EarDecomposition.length_snoc, hlength]
          rfl
        · rw [show d'' = (d'.snoc e').copy hadjoin from rfl,
            SimpleGraph.EarDecomposition.initial_copy,
            SimpleGraph.EarDecomposition.initial_snoc]
          exact hinitial
  obtain ⟨d', hlength, hinitial⟩ := hprefix (Fin.last d.length)
  let hfinal := Graph.toSimpleGraphSubgraph_congr d.graphAfter_last
    (d.graphAfter_le (Fin.last d.length)) d.final_le
  exact ⟨d'.copy hfinal, by simpa using hlength, by simpa using hinitial⟩

end Graph.EarDecomposition
