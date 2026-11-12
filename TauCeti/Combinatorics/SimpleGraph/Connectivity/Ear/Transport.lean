/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Transporting ear decompositions of simple graphs

This file identifies the two ear-decomposition interfaces attached to a simple graph `G`:
edge-labelled decompositions of the multigraph `Graph.ofSimpleGraph G`, and decompositions by
`SimpleGraph.Subgraph`s of `G`. The transport preserves every prefix, the initial vertex or cycle,
and the underlying walk and kind of every ear.

As an application, a finite nonempty simple graph is `2`-edge-connected exactly when it has an
ear decomposition beginning at one vertex and using open and closed ears.

The representation bridge is useful when a construction needs multigraph edge identities while
its statement belongs in the usual simple-graph API.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Subgraph

/-- Regard a subgraph of a simple graph as a subgraph of its associated edge-labelled graph,
retaining the ambient vertex and edge types. -/
def toMultigraph (H : G.Subgraph) : Graph V (Sym2 V) :=
  (Graph.ofSimpleGraph H.spanningCoe).induce H.verts

@[simp]
theorem vertexSet_toMultigraph (H : G.Subgraph) : H.toMultigraph.vertexSet = H.verts :=
  Graph.vertexSet_induce _ _

@[simp]
theorem isLink_toMultigraph (H : G.Subgraph) (e : Sym2 V) (x y : V) :
    H.toMultigraph.IsLink e x y ↔ e = s(x, y) ∧ H.Adj x y := by
  simp only [toMultigraph, Graph.induce_isLink, Graph.ofSimpleGraph_isLink]
  constructor
  · rintro ⟨⟨rfl, he⟩, -, -⟩
    exact ⟨rfl, by simpa using he⟩
  · rintro ⟨rfl, hxy⟩
    exact ⟨⟨rfl, by simpa using hxy⟩, hxy.fst_mem, hxy.snd_mem⟩

@[simp]
theorem edgeSet_toMultigraph (H : G.Subgraph) : H.toMultigraph.edgeSet = H.edgeSet := by
  ext e
  induction e with
  | h x y =>
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      constructor
      · intro he
        obtain ⟨a, b, hab⟩ := (Graph.edge_mem_iff_exists_isLink _ _).1 he
        rw [H.isLink_toMultigraph] at hab
        exact (H.adj_congr_of_sym2 hab.1).mpr hab.2
      · intro hxy
        exact (Graph.edge_mem_iff_exists_isLink _ _).2
          ⟨x, y, (H.isLink_toMultigraph _ _ _).2 ⟨rfl, hxy⟩⟩

/-- The graph attached to a simple-graph subgraph is a subgraph of the graph attached to the
ambient simple graph. -/
theorem toMultigraph_le (H : G.Subgraph) : H.toMultigraph ≤ Graph.ofSimpleGraph G := by
  refine ⟨by simp, fun e x y he ↦ ?_⟩
  rw [H.isLink_toMultigraph] at he
  rw [Graph.ofSimpleGraph_isLink]
  exact ⟨he.1, he.1 ▸ G.mem_edgeSet.mpr (H.adj_sub he.2)⟩

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
theorem adj_toSubgraphOfSimpleGraph (K : Graph V (Sym2 V))
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
        have heq : s(a, b) = s(x, y) := by
          exact (hK.2 hab).1.symm
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨_, hab⟩
        · exact ⟨_, hab.symm⟩

@[simp]
theorem toSubgraphOfSimpleGraph_toMultigraph (H : G.Subgraph) :
    H.toMultigraph.toSubgraphOfSimpleGraph H.toMultigraph_le = H := by
  ext x y
  · simp
  · simp [Adj, SimpleGraph.Subgraph.isLink_toMultigraph]

/-- The edge-labelled representation of simple-graph subgraphs is injective. -/
theorem _root_.SimpleGraph.Subgraph.toMultigraph_injective (G : SimpleGraph V) :
    Function.Injective (fun H : G.Subgraph ↦ H.toMultigraph) := by
  intro H K h
  ext x y
  · rw [show H.verts = K.verts from by simpa using congrArg Graph.vertexSet h]
  · have hlink := congrArg (fun L : Graph V (Sym2 V) ↦ L.IsLink s(x, y) x y) h
    simpa using hlink

theorem toMultigraph_toSubgraphOfSimpleGraph (K : Graph V (Sym2 V))
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (K.toSubgraphOfSimpleGraph hK).toMultigraph = K := by
  apply Graph.ext
  · simp
  · intro e x y
    rw [SimpleGraph.Subgraph.isLink_toMultigraph]
    constructor
    · rintro ⟨rfl, hxy⟩
      obtain ⟨f, hf⟩ := hxy
      have hfo := hK.2 hf
      exact hfo.1.symm ▸ hf
    · intro he
      exact ⟨(hK.2 he).1, ⟨e, he⟩⟩

/-- The conversion to a simple-graph subgraph is independent of replacing its graph argument and
inclusion proof by equal ones. -/
theorem toSubgraphOfSimpleGraph_congr {K L : Graph V (Sym2 V)}
    (h : K = L) (hK : K ≤ Graph.ofSimpleGraph G) (hL : L ≤ Graph.ofSimpleGraph G) :
    K.toSubgraphOfSimpleGraph hK = L.toSubgraphOfSimpleGraph hL := by
  subst L
  ext <;> simp

@[simp]
theorem toSubgraphOfSimpleGraph_top :
    (Graph.ofSimpleGraph G).toSubgraphOfSimpleGraph le_rfl = (⊤ : G.Subgraph) := by
  ext <;> simp

@[simp]
theorem toSubgraphOfSimpleGraph_noEdge_singleton (v : V(Graph.ofSimpleGraph G))
    (h : Graph.noEdge {v.1} (Sym2 V) ≤ Graph.ofSimpleGraph G) :
    (Graph.noEdge {v.1} (Sym2 V)).toSubgraphOfSimpleGraph h =
      G.singletonSubgraph v.1 := by
  ext x y
  · simp [toSubgraphOfSimpleGraph]
  · simp [Graph.Adj]

end Graph

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

namespace Subgraph

/-- Inclusion of simple-graph subgraphs is preserved by the edge-labelled representation. -/
theorem toMultigraph_mono {H K : G.Subgraph} (hHK : H ≤ K) :
    H.toMultigraph ≤ K.toMultigraph := by
  refine ⟨by simpa using hHK.1, fun e x y he ↦ ?_⟩
  rw [H.isLink_toMultigraph] at he
  exact (K.isLink_toMultigraph e x y).2 ⟨he.1, hHK.2 he.2⟩

/-- To bound the graph attached to a union of simple-graph subgraphs, it suffices to bound the
graphs attached to the two operands. -/
theorem toMultigraph_sup_le {H K : G.Subgraph} {L : Graph V (Sym2 V)}
    (hH : H.toMultigraph ≤ L) (hK : K.toMultigraph ≤ L) :
    (H ⊔ K).toMultigraph ≤ L := by
  refine ⟨?_, fun e x y he ↦ ?_⟩
  · simpa using Set.union_subset_union hH.1 hK.1
  · rw [isLink_toMultigraph, SimpleGraph.Subgraph.sup_adj] at he
    exact he.2.elim
      (fun hxy ↦ hH.2 ((H.isLink_toMultigraph e x y).2 ⟨he.1, hxy⟩))
      (fun hxy ↦ hK.2 ((K.isLink_toMultigraph e x y).2 ⟨he.1, hxy⟩))

end Subgraph

namespace Walk

/-- The subgraph traced by a simple-graph walk becomes the edge-labelled graph traced by the
corresponding walk in `Graph.ofSimpleGraph G`. -/
theorem toMultigraph_toSubgraph {x y : V} (p : G.Walk x y) :
    p.toSubgraph.toMultigraph = (Graph.ofSimpleGraph G).walkGraph p.toGraph := by
  apply Graph.ext
  · ext z
    simp
  · intro e a b
    rw [Subgraph.isLink_toMultigraph, Graph.Walk.walkGraph_isLink,
      Graph.ofSimpleGraph_isLink]
    constructor
    · rintro ⟨rfl, hab⟩
      exact ⟨⟨rfl, p.edges_subset_edgeSet (p.adj_toSubgraph_iff_mem_edges.mp hab)⟩,
        by simpa using p.adj_toSubgraph_iff_mem_edges.mp hab⟩
    · rintro ⟨⟨rfl, -⟩, he⟩
      exact ⟨rfl, p.adj_toSubgraph_iff_mem_edges.mpr (by simpa using he)⟩

end Walk

namespace EarKind

/-- Identify simple-graph ear kinds with multigraph ear kinds. -/
def toGraph : SimpleGraph.EarKind → Graph.EarKind
  | .open => .open
  | .closed => .closed

@[simp]
theorem toGraph_eq_open (kind : SimpleGraph.EarKind) :
    kind.toGraph = .open ↔ kind = .open := by
  cases kind <;> simp [toGraph]

end EarKind

namespace Ear

/-- Transport a simple-graph ear to the edge-labelled multigraph interface. -/
def toMultigraph (e : G.Ear H) :
    (Graph.ofSimpleGraph G).Ear H.toMultigraph := by
  cases e with
  | «open» p hp hu hv huv hint hedge =>
      exact .open H.toMultigraph_le p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa) (by simpa) huv
        (by simpa only [SimpleGraph.Walk.support_toGraph, Subgraph.vertexSet_toMultigraph]
            using hint)
        (by simpa only [SimpleGraph.Walk.edges_toGraph, Subgraph.edgeSet_toMultigraph]
            using hedge)
  | closed c hc hu hint =>
      exact .closed H.toMultigraph_le c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa)
        (by simpa only [SimpleGraph.Walk.support_toGraph, Subgraph.vertexSet_toMultigraph]
            using hint)
        (by simpa only [SimpleGraph.Walk.edges_toGraph, Subgraph.edgeSet_toMultigraph]
            using fun f hf ↦ closed_edges_notMem_edgeSet hint hf)

@[simp]
theorem kind_toMultigraph (e : G.Ear H) :
    e.toMultigraph.kind = e.kind.toGraph := by
  cases e <;> simp [toMultigraph, EarKind.toGraph]

@[simp]
theorem toWalk_toMultigraph (e : G.Ear H) :
    e.toMultigraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» =>
      dsimp only [toMultigraph]
      rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | closed =>
      dsimp only [toMultigraph]
      rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

@[simp]
theorem toGraph_toMultigraph (e : G.Ear H) :
    e.toMultigraph.toGraph = e.toSubgraph.toMultigraph := by
  cases e <;> simp only [toMultigraph, SimpleGraph.Ear.toSubgraph_open,
    SimpleGraph.Ear.toSubgraph_closed, Graph.Ear.toGraph_open, Graph.Ear.toGraph_closed,
    SimpleGraph.Walk.toMultigraph_toSubgraph]

/-- Transport commutes with adjoining a simple-graph ear. -/
theorem toMultigraph_adjoin (e : G.Ear H) :
    e.adjoin.toMultigraph = e.toMultigraph.add := by
  rw [SimpleGraph.Ear.adjoin_def]
  apply le_antisymm
  · apply Subgraph.toMultigraph_sup_le
    · exact e.toMultigraph.base_le_add
    · rw [← toGraph_toMultigraph]
      exact e.toMultigraph.toGraph_le_add
  · rw [Graph.Ear.add_le_iff]
    exact ⟨Subgraph.toMultigraph_mono le_sup_left,
      toGraph_toMultigraph e ▸ Subgraph.toMultigraph_mono le_sup_right⟩

end Ear

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

namespace EarKind

/-- Identify multigraph ear kinds with simple-graph ear kinds. -/
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .open
  | .closed => .closed

@[simp]
theorem toSimpleGraph_eq_open (kind : Graph.EarKind) :
    kind.toSimpleGraph = .open ↔ kind = .open := by
  cases kind <;> simp [toSimpleGraph]

end EarKind

namespace Ear

/-- Transport an ear in a subgraph of `Graph.ofSimpleGraph G` to the simple-graph interface. -/
def toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) (hK : K ≤ Graph.ofSimpleGraph G) :
    G.Ear (K.toSubgraphOfSimpleGraph hK) := by
  cases e with
  | «open» _ p hp hu hv huv hint hedge =>
      exact .open p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp)
        (by simpa) (by simpa) huv
        (by simpa only [Graph.Walk.support_toSimpleGraph, verts_toSubgraphOfSimpleGraph]
            using hint)
        (by simpa only [Graph.Walk.edges_toSimpleGraph, edgeSet_toSubgraphOfSimpleGraph]
            using hedge)
  | closed _ c hc hu hint _ =>
      exact .closed c.toSimpleGraph (c.isCycle_toSimpleGraph_iff.mpr hc)
        (by simpa)
        (by simpa only [Graph.Walk.support_toSimpleGraph, verts_toSubgraphOfSimpleGraph]
            using hint)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph, EarKind.toSimpleGraph]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).toWalk =
      ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» =>
      dsimp only [toSimpleGraph]
      rw [Graph.Ear.toWalk_open, SimpleGraph.Ear.toWalk_open]
  | closed =>
      dsimp only [toSimpleGraph]
      rw [Graph.Ear.toWalk_closed, SimpleGraph.Ear.toWalk_closed]

/-- Converting an ear to the simple-graph interface and back preserves its traced graph. -/
theorem toGraph_toMultigraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).toMultigraph.toGraph = e.toGraph := by
  cases e with
  | «open» =>
      dsimp only [toSimpleGraph]
      rw [SimpleGraph.Ear.toGraph_toMultigraph, SimpleGraph.Ear.toSubgraph_open,
        SimpleGraph.Walk.toMultigraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph,
        Graph.Ear.toGraph_open]
  | closed =>
      dsimp only [toSimpleGraph]
      rw [SimpleGraph.Ear.toGraph_toMultigraph, SimpleGraph.Ear.toSubgraph_closed,
        SimpleGraph.Walk.toMultigraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph,
        Graph.Ear.toGraph_closed]

/-- Converting an ear to the simple-graph interface and back preserves the graph obtained by
adjoining it. -/
theorem add_toMultigraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (e.toSimpleGraph hK).toMultigraph.add = e.add := by
  have hbase : (K.toSubgraphOfSimpleGraph hK).toMultigraph = K :=
    toMultigraph_toSubgraphOfSimpleGraph (G := G) K hK
  have htrace : (e.toSimpleGraph hK).toMultigraph.toGraph = e.toGraph :=
    e.toGraph_toMultigraph_toSimpleGraph hK
  apply le_antisymm
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.le.trans e.base_le_add, htrace.le.trans e.toGraph_le_add⟩
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.ge.trans (e.toSimpleGraph hK).toMultigraph.base_le_add,
      htrace.ge.trans (e.toSimpleGraph hK).toMultigraph.toGraph_le_add⟩

/-- Transport to the simple-graph interface commutes with adjoining an ear. -/
theorem toSimpleGraph_add (e : (Graph.ofSimpleGraph G).Ear K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    e.add.toSubgraphOfSimpleGraph e.add_le = (e.toSimpleGraph hK).adjoin := by
  apply SimpleGraph.Subgraph.toMultigraph_injective G
  -- Expose the representatives compared by the injectivity argument.
  change (e.add.toSubgraphOfSimpleGraph e.add_le).toMultigraph =
    ((e.toSimpleGraph hK).adjoin).toMultigraph
  rw [SimpleGraph.Ear.toMultigraph_adjoin, e.add_toMultigraph_toSimpleGraph hK,
    toMultigraph_toSubgraphOfSimpleGraph (G := G)]

end Ear

end Graph

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

namespace Subgraph

@[simp]
theorem toMultigraph_singletonSubgraph (v : V) :
    (G.singletonSubgraph v).toMultigraph = Graph.noEdge {v} (Sym2 V) := by
  apply Graph.ext
  · simp
  · intro e x y
    simp

end Subgraph

namespace EarStart

private theorem graphEarStart_isCycle_transport {K L : Graph V (Sym2 V)} (h : K = L)
    (s : (Graph.ofSimpleGraph G).EarStart K) : (h ▸ s).IsCycle ↔ s.IsCycle := by
  subst h
  rfl

/-- Transport initial ear-decomposition data to the edge-labelled multigraph interface. -/
def toMultigraph (s : G.EarStart H) :
    (Graph.ofSimpleGraph G).EarStart H.toMultigraph := by
  cases s with
  | vertex v =>
      exact (Subgraph.toMultigraph_singletonSubgraph (G := G) v).symm ▸
        Graph.EarStart.vertex ⟨v, by simp⟩
  | cycle c hc =>
      exact (SimpleGraph.Walk.toMultigraph_toSubgraph c).symm ▸
        Graph.EarStart.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)

@[simp]
theorem isCycle_toMultigraph (s : G.EarStart H) :
    s.toMultigraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      dsimp only [toMultigraph]
      rw [graphEarStart_isCycle_transport]
      simp only [Graph.EarStart.isCycle_vertex, SimpleGraph.EarStart.isCycle_vertex]
  | cycle c hc =>
      dsimp only [toMultigraph]
      rw [graphEarStart_isCycle_transport]
      simp only [Graph.EarStart.isCycle_cycle, SimpleGraph.EarStart.isCycle_cycle]

end EarStart

namespace EarDecomposition

/-- Transport a simple-graph ear decomposition to `Graph.ofSimpleGraph G`, preserving all prefix
data. -/
def toMultigraph (d : G.EarDecomposition H) :
    (Graph.ofSimpleGraph G).EarDecomposition H.toMultigraph where
  length := d.length
  graphAfter i := (d.subgraphAfter i).toMultigraph
  start := d.start.toMultigraph
  earAt i := ⟨(d.subgraphAfter i.castSucc).toMultigraph, (d.earAt i).toMultigraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by
    rw [d.subgraphAfter_succ, SimpleGraph.Ear.toMultigraph_adjoin]
  graphAfter_last := congrArg Subgraph.toMultigraph d.subgraphAfter_last

@[simp]
theorem length_toMultigraph (d : G.EarDecomposition H) : d.toMultigraph.length = d.length :=
  (rfl)

@[simp]
theorem graphAfter_toMultigraph (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toMultigraph.graphAfter
      (Fin.cast (congrArg (· + 1) (length_toMultigraph d).symm) i) =
        (d.subgraphAfter i).toMultigraph := by
  -- The only discrepancy is transport across the definitional length equality.
  change (d.subgraphAfter (Fin.cast rfl i)).toMultigraph = _
  rw [Fin.cast_eq_self]

theorem earAt_toMultigraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toMultigraph.earAt (Fin.cast (length_toMultigraph d).symm i) =
      (⟨(d.subgraphAfter i.castSucc).toMultigraph, (d.earAt i).toMultigraph⟩ :
        Σ K : Graph V (Sym2 V), (Graph.ofSimpleGraph G).Ear K) := by
  -- Expose the dependent pair after transporting its finite index.
  change (⟨(d.subgraphAfter (Fin.cast rfl i).castSucc).toMultigraph,
    (d.earAt (Fin.cast rfl i)).toMultigraph⟩ :
      Σ K : Graph V (Sym2 V), (Graph.ofSimpleGraph G).Ear K) = _
  rw [Fin.cast_eq_self]

@[simp]
theorem kindAt_toMultigraph (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.toMultigraph.earAt (Fin.cast (length_toMultigraph d).symm i)).2.kind =
      (d.kindAt i).toGraph := by
  rw [earAt_toMultigraph, SimpleGraph.EarDecomposition.kindAt_def]
  exact SimpleGraph.Ear.kind_toMultigraph (d.earAt i)

@[simp]
theorem walkAt_toMultigraph (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.toMultigraph.earAt (Fin.cast (length_toMultigraph d).symm i)).2.toWalk =
      ⟨d.walkAt i |>.1, (d.walkAt i).2.1, (d.walkAt i).2.2.toGraph⟩ := by
  rw [earAt_toMultigraph, SimpleGraph.EarDecomposition.walkAt_def]
  exact SimpleGraph.Ear.toWalk_toMultigraph (d.earAt i)

@[simp]
theorem isOpen_toMultigraph (d : G.EarDecomposition H) :
    d.toMultigraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, SimpleGraph.EarDecomposition.isOpen_iff]
  constructor
  · rintro ⟨hstart, hkinds⟩
    refine ⟨?_, fun i ↦ ?_⟩
    · -- Expose the converted initial witness before comparing its variant.
      change d.start.toMultigraph.IsCycle at hstart
      exact EarStart.isCycle_toMultigraph d.start |>.mp hstart
    · have hkind := hkinds (Fin.cast (length_toMultigraph d).symm i)
      rw [Graph.EarDecomposition.kindAt_eq, kindAt_toMultigraph] at hkind
      exact (EarKind.toGraph_eq_open _).mp hkind
  · rintro ⟨hstart, hkinds⟩
    refine ⟨?_, fun i ↦ ?_⟩
    · -- Expose the converted initial witness before comparing its variant.
      change d.start.toMultigraph.IsCycle
      exact EarStart.isCycle_toMultigraph d.start |>.mpr hstart
    · have hkind := hkinds (Fin.cast (length_toMultigraph d) i)
      have htransport := kindAt_toMultigraph d (Fin.cast (length_toMultigraph d) i)
      rw [Fin.cast_cast] at htransport
      rw [← Graph.EarDecomposition.kindAt_eq] at htransport
      exact htransport.trans ((EarKind.toGraph_eq_open _).mpr hkind)

end EarDecomposition

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

namespace EarStart

private theorem simpleGraphEarStart_isCycle_transport {H L : G.Subgraph} (h : H = L)
    (s : G.EarStart H) : (h ▸ s).IsCycle ↔ s.IsCycle := by
  subst h
  rfl

/-- Transport initial ear-decomposition data from `Graph.ofSimpleGraph G` to the simple-graph
interface. -/
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K)
    (hK : K ≤ Graph.ofSimpleGraph G) : G.EarStart (K.toSubgraphOfSimpleGraph hK) := by
  cases s with
  | vertex v =>
      exact (toSubgraphOfSimpleGraph_noEdge_singleton v hK).symm ▸
        SimpleGraph.EarStart.vertex v.1
  | cycle p hp =>
      have hsub :
          ((Graph.ofSimpleGraph G).walkGraph p).toSubgraphOfSimpleGraph hK =
            p.toSimpleGraph.toSubgraph := by
        apply SimpleGraph.Subgraph.toMultigraph_injective G
        -- Compare the two subgraphs through their inverse multigraph representations.
        change (((Graph.ofSimpleGraph G).walkGraph p).toSubgraphOfSimpleGraph hK).toMultigraph =
          p.toSimpleGraph.toSubgraph.toMultigraph
        rw [toMultigraph_toSubgraphOfSimpleGraph (G := G),
          SimpleGraph.Walk.toMultigraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph]
      exact hsub.symm ▸
        SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

@[simp]
theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K)
    (hK : K ≤ Graph.ofSimpleGraph G) :
    (s.toSimpleGraph hK).IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      dsimp only [toSimpleGraph]
      rw [simpleGraphEarStart_isCycle_transport]
      simp only [SimpleGraph.EarStart.isCycle_vertex, Graph.EarStart.isCycle_vertex]
  | cycle p hp =>
      dsimp only [toSimpleGraph]
      rw [simpleGraphEarStart_isCycle_transport]
      simp only [SimpleGraph.EarStart.isCycle_cycle, Graph.EarStart.isCycle_cycle]

end EarStart

namespace EarDecomposition

/-- Transport an ear decomposition of a subgraph of `Graph.ofSimpleGraph G` to the simple-graph
interface, preserving all prefix data. -/
def toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    G.EarDecomposition (K.toSubgraphOfSimpleGraph d.final_le) where
  length := d.length
  subgraphAfter i := (d.graphAfter i).toSubgraphOfSimpleGraph (d.graphAfter_le i)
  start := d.start.toSimpleGraph (d.graphAfter_le 0)
  earAt i :=
    ((d.earAt i).2.toSimpleGraph (d.earAt i).2.base_le).copy <|
      toSubgraphOfSimpleGraph_congr (d.earAt_fst i)
        (d.earAt i).2.base_le (d.graphAfter_le i.castSucc)
  subgraphAfter_succ i := by
    let e := (d.earAt i).2
    let hbase := toSubgraphOfSimpleGraph_congr (d.earAt_fst i)
      (d.earAt i).2.base_le (d.graphAfter_le i.castSucc)
    have hgraph := toSubgraphOfSimpleGraph_congr (d.graphAfter_succ i)
      (d.graphAfter_le i.succ) (d.earAt i).2.add_le
    rw [hgraph, (d.earAt i).2.toSimpleGraph_add (d.earAt i).2.base_le,
      SimpleGraph.Ear.adjoin_def, SimpleGraph.Ear.adjoin_copy]
    exact congrArg (· ⊔ (e.toSimpleGraph e.base_le).toSubgraph) hbase
  subgraphAfter_last :=
    toSubgraphOfSimpleGraph_congr d.graphAfter_last
      (d.graphAfter_le (Fin.last d.length)) d.final_le

@[simp]
theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.length = d.length :=
  (rfl)

@[simp]
theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.length + 1)) :
    d.toSimpleGraph.subgraphAfter
      (Fin.cast (congrArg (· + 1) (length_toSimpleGraph d).symm) i) =
        (d.graphAfter i).toSubgraphOfSimpleGraph (d.graphAfter_le i) := by
  -- The only discrepancy is transport across the definitional length equality.
  change (d.graphAfter (Fin.cast rfl i)).toSubgraphOfSimpleGraph
    (d.graphAfter_le (Fin.cast rfl i)) = _
  rw [Fin.cast_eq_self]

theorem earAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    HEq (d.toSimpleGraph.earAt (Fin.cast (length_toSimpleGraph d).symm i))
      (((d.earAt i).2.toSimpleGraph (d.earAt i).2.base_le).copy
        (toSubgraphOfSimpleGraph_congr (d.earAt_fst i)
          (d.earAt i).2.base_le (d.graphAfter_le i.castSucc))) := by
  rfl

private theorem simpleEar_kind_eq_of_heq {H L : G.Subgraph} {e : G.Ear H} {f : G.Ear L}
    (hHL : H = L) (hef : HEq e f) : e.kind = f.kind := by
  cases hHL
  cases hef
  rfl

private theorem simpleEar_toWalk_eq_of_heq {H L : G.Subgraph} {e : G.Ear H} {f : G.Ear L}
    (hHL : H = L) (hef : HEq e f) : e.toWalk = f.toWalk := by
  cases hHL
  cases hef
  rfl

@[simp]
theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.kindAt (Fin.cast (length_toSimpleGraph d).symm i) =
      (d.kindAt i).toSimpleGraph := by
  rw [SimpleGraph.EarDecomposition.kindAt_def, Graph.EarDecomposition.kindAt_eq]
  have hbase :
      d.toSimpleGraph.subgraphAfter
          (Fin.cast (length_toSimpleGraph d).symm i).castSucc =
        (d.graphAfter i.castSucc).toSubgraphOfSimpleGraph
          (d.graphAfter_le i.castSucc) := by
    simpa using d.subgraphAfter_toSimpleGraph i.castSucc
  have hear := d.earAt_toSimpleGraph i
  exact (simpleEar_kind_eq_of_heq hbase hear).trans <|
    (SimpleGraph.Ear.kind_copy _ _).trans <|
      Graph.Ear.kind_toSimpleGraph (d.earAt i).2 (d.earAt i).2.base_le

@[simp]
theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.walkAt (Fin.cast (length_toSimpleGraph d).symm i) =
      ⟨d.walkAt i |>.1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ := by
  rw [SimpleGraph.EarDecomposition.walkAt_def, Graph.EarDecomposition.walkAt_eq]
  have hbase :
      d.toSimpleGraph.subgraphAfter
          (Fin.cast (length_toSimpleGraph d).symm i).castSucc =
        (d.graphAfter i.castSucc).toSubgraphOfSimpleGraph
          (d.graphAfter_le i.castSucc) := by
    simpa using d.subgraphAfter_toSimpleGraph i.castSucc
  have hear := d.earAt_toSimpleGraph i
  exact (simpleEar_toWalk_eq_of_heq hbase hear).trans <|
    (SimpleGraph.Ear.toWalk_copy _ _).trans <|
      Graph.Ear.toWalk_toSimpleGraph (d.earAt i).2 (d.earAt i).2.base_le

@[simp]
theorem isOpen_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff]
  constructor
  · rintro ⟨hstart, hkinds⟩
    refine ⟨?_, fun i ↦ ?_⟩
    · -- Expose the converted initial witness before comparing its variant.
      change (d.start.toSimpleGraph (d.graphAfter_le 0)).IsCycle at hstart
      exact (EarStart.isCycle_toSimpleGraph d.start _).mp hstart
    · have hkind := hkinds (Fin.cast (length_toSimpleGraph d).symm i)
      rw [kindAt_toSimpleGraph] at hkind
      exact (EarKind.toSimpleGraph_eq_open _).mp hkind
  · rintro ⟨hstart, hkinds⟩
    refine ⟨?_, fun i ↦ ?_⟩
    · -- Expose the converted initial witness before comparing its variant.
      change (d.start.toSimpleGraph (d.graphAfter_le 0)).IsCycle
      exact (EarStart.isCycle_toSimpleGraph d.start _).mpr hstart
    · have hkind := hkinds (Fin.cast (length_toSimpleGraph d) i)
      have htransport := kindAt_toSimpleGraph d (Fin.cast (length_toSimpleGraph d) i)
      rw [Fin.cast_cast] at htransport
      exact htransport.trans ((EarKind.toSimpleGraph_eq_open _).mpr hkind)

/-- A full edge-labelled decomposition transports to a decomposition of the top simple-graph
subgraph. -/
def toSimpleGraphTop (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    G.EarDecomposition (⊤ : G.Subgraph) :=
  d.toSimpleGraph.copy toSubgraphOfSimpleGraph_top

@[simp]
theorem initial_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.initial =
      (d.graphAfter 0).toSubgraphOfSimpleGraph (d.graphAfter_le 0) := by
  rw [toSimpleGraphTop, SimpleGraph.EarDecomposition.initial_copy]
  rw [← d.toSimpleGraph.subgraphAfter_zero]
  simpa using d.subgraphAfter_toSimpleGraph 0

end EarDecomposition

end Graph
