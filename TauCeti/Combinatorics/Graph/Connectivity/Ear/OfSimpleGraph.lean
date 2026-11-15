/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Ear decompositions of graphs associated to simple graphs

A simple graph `G` has two ear-decomposition interfaces: `SimpleGraph.EarDecomposition`, whose
stages are subgraphs `H : G.Subgraph`, and `Graph.EarDecomposition` for the multigraph
`Graph.ofSimpleGraph G`, whose stages are graphs below `Graph.ofSimpleGraph G`. This file
identifies them.

`Graph.EarDecomposition.toSimpleGraph` drops the redundant `Sym2 V` edge identities, so
decompositions of graphs below `Graph.ofSimpleGraph G` can be used through the
`SimpleGraph.EarDecomposition` API. Conversely, `SimpleGraph.EarDecomposition.toGraph` regards a
decomposition of `H` as one of `H.toGraph`. Both transports act on ears, initial vertices or
cycles, and decompositions, and preserve the number of ears, the stage after every prefix, the
initial vertex or cycle, the walk and kind of every ear, prefix decompositions, and openness. They
are mutually inverse up to reindexing the target subgraph, and
`SimpleGraph.Subgraph.earDecompositionEquivOfSimpleGraph` packages them as an equivalence.

For a decomposition of all of `Graph.ofSimpleGraph G`, the target subgraph simplifies to `⊤` by
`Graph.toSimpleGraphSubgraph_ofSimpleGraph`; `SimpleGraph.EarDecomposition.copy` can then reindex
the transported decomposition to that canonical target.

## Implementation notes

`SimpleGraph.EarDecomposition.toGraph` is reducible and exposed, so that the length of a
transported decomposition unfolds to the original length even at reducible transparency.
Statements can then use `Fin` indices over either length interchangeably, and `rw` and `simp` can
use them.
-/

public section

open Set
open scoped Sym2

universe u

namespace Graph.EarKind

/-- Convert a multigraph ear kind (`open` or `closed`) to the corresponding
`SimpleGraph.EarKind`. -/
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .open
  | .closed => .closed

@[simp] theorem toSimpleGraph_open : toSimpleGraph .open = .open := (rfl)
@[simp] theorem toSimpleGraph_closed : toSimpleGraph .closed = .closed := (rfl)

@[simp]
theorem toSimpleGraph_eq_open_iff {k : Graph.EarKind} : k.toSimpleGraph = .open ↔ k = .open := by
  cases k <;> simp

@[simp]
theorem toSimpleGraph_eq_closed_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .closed ↔ k = .closed := by
  cases k <;> simp

theorem toSimpleGraph_injective : Function.Injective toSimpleGraph := by
  intro k l h
  cases k <;> cases l <;> simp_all

@[simp]
theorem toSimpleGraph_inj {k l : Graph.EarKind} :
    k.toSimpleGraph = l.toSimpleGraph ↔ k = l :=
  toSimpleGraph_injective.eq_iff

end Graph.EarKind

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport an ear of `Graph.ofSimpleGraph G` to an ear over the corresponding simple
subgraph. -/
def toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    G.Ear (K.toSimpleGraphSubgraph e.base_le) :=
  match e with
  | .open _ p hp hs ht hst hinter hedge =>
      .«open» p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using ht) hst
        (by simpa using hinter) (by simpa using hedge)
  | .closed _ p hp hs hinter _ =>
      .closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using hinter)

@[simp]
theorem toSimpleGraph_open {x y : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x y) (hp : p.IsPath) (hx : x ∈ K.vertexSet)
    (hy : y ∈ K.vertexSet) (hxy : x ≠ y)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ≠ y → z ∉ K.vertexSet)
    (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.open hKG p hp hx hy hxy hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.open p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hy) hxy
        (by simpa using hinter) (by simpa using hedge) := (rfl)

@[simp]
theorem toSimpleGraph_closed {x : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) (hx : x ∈ K.vertexSet)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ∉ K.vertexSet)
    (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.closed hKG p hp hx hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hinter) := (rfl)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph, Graph.EarKind.toSimpleGraph]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toWalk =
      ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | «closed» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

/-- Transport identifies the graph traced by an ear with the simple subgraph traced by the
transported ear. -/
@[simp]
theorem toSimpleGraphSubgraph_toGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (h : e.toGraph ≤ Graph.ofSimpleGraph G) :
    e.toGraph.toSimpleGraphSubgraph h = e.toSimpleGraph.toSubgraph := by
  cases e with
  | «open» hKG p hp hs ht hst hinter hedge =>
      simp
  | closed hKG p hp hs hinter hedge =>
      simp

/-- Transport commutes with adjoining an ear to its base graph. -/
@[simp]
theorem toSimpleGraphSubgraph_add (e : (Graph.ofSimpleGraph G).Ear K)
    (hAdd : e.add ≤ Graph.ofSimpleGraph G) :
    e.add.toSimpleGraphSubgraph hAdd = e.toSimpleGraph.adjoin := by
  ext x y
  · simp only [Graph.verts_toSimpleGraphSubgraph, Graph.Ear.vertexSet_add,
      SimpleGraph.Ear.verts_adjoin, Set.mem_union]
    rw [← Graph.verts_toSimpleGraphSubgraph e.toGraph e.toGraph_le,
      e.toSimpleGraphSubgraph_toGraph]
  · rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet]
    simp only [Graph.edgeSet_toSimpleGraphSubgraph, Graph.Ear.edgeSet_add,
      SimpleGraph.Ear.edgeSet_adjoin, Set.mem_union]
    rw [← Graph.edgeSet_toSimpleGraphSubgraph e.toGraph e.toGraph_le,
      e.toSimpleGraphSubgraph_toGraph]

end Graph.Ear

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport the initial vertex or cycle of a multigraph ear decomposition to the corresponding
simple subgraph. -/
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    G.EarStart (K.toSimpleGraphSubgraph s.le) := by
  cases s with
  | vertex v =>
      exact (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1
        (Graph.EarStart.vertex v).le).symm ▸ .vertex v.1
  | cycle p hp =>
      exact (Graph.Walk.toSimpleGraphSubgraph_walkGraph p
        (Graph.EarStart.cycle p hp).le).symm ▸
          .cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

/-- Transporting a vertex initial stage selects the corresponding simple-graph vertex stage. -/
theorem heq_toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    HEq (Graph.EarStart.vertex v).toSimpleGraph
      (SimpleGraph.EarStart.vertex (G := G) v.1) := by
  unfold toSimpleGraph
  exact eqRec_heq _ _

/-- Transporting a cycle initial stage selects the corresponding simple-graph cycle stage. -/
theorem heq_toSimpleGraph_cycle {x : V} (p : (Graph.ofSimpleGraph G).Walk x x)
    (hp : p.IsCycle) :
    HEq (Graph.EarStart.cycle p hp).toSimpleGraph
      (SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)) := by
  unfold toSimpleGraph
  exact eqRec_heq _ _

@[simp]
theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans
        ((SimpleGraph.EarStart.isCycle_vertex v.1).trans
          (Graph.EarStart.isCycle_vertex v).symm)
  | cycle p hp =>
      exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans
        ((SimpleGraph.EarStart.isCycle_cycle p.toSimpleGraph _).trans
          (Graph.EarStart.isCycle_cycle p hp).symm)

/-- Transport to the simple graph respects heterogeneous equality of initial stages. -/
theorem heq_toSimpleGraph_of_heq {K₁ K₂ : Graph V (Sym2 V)}
    {s₁ : (Graph.ofSimpleGraph G).EarStart K₁} {s₂ : (Graph.ofSimpleGraph G).EarStart K₂}
    (hK : K₁ = K₂) (hs : HEq s₁ s₂) : HEq s₁.toSimpleGraph s₂.toSimpleGraph := by
  subst hK
  cases eq_of_heq hs
  rfl

end Graph.EarStart

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport a decomposition of a subgraph of `Graph.ofSimpleGraph G` to a decomposition of the
corresponding simple subgraph, retaining every prefix and displayed ear. -/
@[expose]
def toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    G.EarDecomposition (K.toSimpleGraphSubgraph d.final_le) where
  length := d.length
  subgraphAfter i := (d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i)
  start := d.start.toSimpleGraph
  earAt i :=
    (d.earAt i).2.toSimpleGraph.copy
      (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) (d.earAt i).2.base_le
        (d.graphAfter_le i.castSucc))
  subgraphAfter_succ i := by
    let e := (d.earAt i).2
    let hbase := Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) e.base_le
      (d.graphAfter_le i.castSucc)
    calc
      (d.graphAfter i.succ).toSimpleGraphSubgraph (d.graphAfter_le i.succ) =
          e.add.toSimpleGraphSubgraph e.add_le :=
        Graph.toSimpleGraphSubgraph_congr (d.graphAfter_succ i) _ _
      _ = e.toSimpleGraph.adjoin := e.toSimpleGraphSubgraph_add e.add_le
      _ = (d.graphAfter i.castSucc).toSimpleGraphSubgraph
            (d.graphAfter_le i.castSucc) ⊔ e.toSimpleGraph.toSubgraph := by
        rw [SimpleGraph.Ear.adjoin_def]
        exact congrArg (fun H : G.Subgraph ↦ H ⊔ e.toSimpleGraph.toSubgraph) hbase
      _ = (e.toSimpleGraph.copy hbase).adjoin :=
        (SimpleGraph.Ear.adjoin_copy _ _).symm
  subgraphAfter_last :=
    Graph.toSimpleGraphSubgraph_congr d.graphAfter_last
      (d.graphAfter_le (Fin.last d.length)) d.final_le

@[simp]
theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.length = d.length := rfl

@[simp]
theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.length + 1)) :
    d.toSimpleGraph.subgraphAfter i =
      (d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i) := rfl

@[simp]
theorem initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial =
      (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) :=
  (SimpleGraph.EarDecomposition.subgraphAfter_zero d.toSimpleGraph).symm

/-- The transported decomposition retains the transported initial-stage witness. -/
@[simp]
theorem start_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.start = d.start.toSimpleGraph := (rfl)

/-- The transported decomposition displays the transported ear at each step, copied only across
the equality identifying its stored base with the corresponding prefix. -/
@[simp]
theorem earAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.earAt i =
      (d.earAt i).2.toSimpleGraph.copy
        (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) (d.earAt i).2.base_le
          (d.graphAfter_le i.castSucc)) := (rfl)

@[simp]
theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) : d.toSimpleGraph.kindAt i = (d.kindAt i).toSimpleGraph := by
  simp [SimpleGraph.EarDecomposition.kindAt_def, Graph.EarDecomposition.kindAt_eq,
    toSimpleGraph]

@[simp]
theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ := by
  rw [Graph.EarDecomposition.walkAt_eq]
  simp [SimpleGraph.EarDecomposition.walkAt_def, toSimpleGraph]

/-- Transport preserves the open-ear-decomposition predicate. -/
@[simp]
theorem isOpen_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff,
    start_toSimpleGraph]
  refine and_congr d.start.isCycle_toSimpleGraph ?_
  simpa only [length_toSimpleGraph] using
    (forall_congr' fun i : Fin d.length ↦ by simp)

end Graph.EarDecomposition

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Ear

variable {H : G.Subgraph}

/-- An ear over `H` in a simple graph `G`, as an ear over `H.toGraph` in `Graph.ofSimpleGraph G`
with the corresponding edge-labelled walk. -/
def toGraph : G.Ear H → (Graph.ofSimpleGraph G).Ear H.toGraph
  | .«open» p hp hu hv huv hint hedge =>
      .open H.toGraph_le_ofSimpleGraph p.toGraph (p.isPath_toGraph_iff.mpr hp) (by simpa using hu)
        (by simpa using hv) huv (by simpa using hint) (by simpa using hedge)
  | .closed c hc hu hint =>
      .closed H.toGraph_le_ofSimpleGraph c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa using hu) (by simpa using hint) fun _ he ↦ by
          simpa using closed_edges_notMem_edgeSet hint (by simpa using he)

@[simp]
theorem toWalk_toGraph (e : G.Ear H) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, (e.toWalk.2.2 : G.Walk _ _).toGraph⟩ := by
  cases e with
  | «open» => rw [toGraph, Graph.Ear.toWalk_open, toWalk_open]
  | closed => rw [toGraph, Graph.Ear.toWalk_closed, toWalk_closed]

@[simp]
theorem kind_toGraph_eq_open_iff (e : G.Ear H) :
    e.toGraph.kind = .open ↔ e.kind = .«open» := by
  cases e <;> simp [toGraph]

@[simp]
theorem kind_toGraph_eq_closed_iff (e : G.Ear H) :
    e.toGraph.kind = .closed ↔ e.kind = .closed := by
  cases e <;> simp [toGraph]

/-- The graph traced by a transported ear is the graph of the subgraph traced by the ear. -/
@[simp]
theorem toGraph_toGraph (e : G.Ear H) : e.toGraph.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph]

/-- Adjoining a transported ear gives the graph of the subgraph obtained by adjoining the ear. -/
@[simp]
theorem add_toGraph (e : G.Ear H) : e.toGraph.add = e.adjoin.toGraph := by
  refine Graph.ext ?_ fun f x y ↦ ?_
  · rw [Graph.Ear.vertexSet_add, toGraph_toGraph]
    simp [adjoin_def]
  · rw [Graph.Ear.add_isLink, toGraph_toGraph]
    simp [adjoin_def, and_or_left]

/-- Transporting an ear commutes with reindexing its base. -/
theorem heq_toGraph_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    HEq (e.copy h).toGraph e.toGraph := by
  subst h
  rw [copy_rfl]

/-- Transporting an ear to `Graph.ofSimpleGraph G` and back recovers it, reindexed along
`SimpleGraph.Subgraph.toSimpleGraphSubgraph_toGraph`. -/
@[simp]
theorem toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph = e.copy (H.toSimpleGraphSubgraph_toGraph _).symm :=
  Ear.ext <| by cases e <;> simp [toGraph]

end Ear

namespace EarStart

variable {H : G.Subgraph}

/-- An initial vertex or cycle of a simple graph, as an initial vertex or cycle of
`Graph.ofSimpleGraph G`. -/
def toGraph : {H : G.Subgraph} → G.EarStart H → (Graph.ofSimpleGraph G).EarStart H.toGraph
  | _, .vertex v =>
      cast (congrArg _ (Subgraph.toGraph_singletonSubgraph v).symm) (.vertex ⟨v, Set.mem_univ v⟩)
  | _, .cycle c hc =>
      cast (congrArg _ c.toGraph_toSubgraph.symm) (.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc))

/-- Transporting a vertex initial stage gives the corresponding multigraph vertex stage. -/
theorem heq_toGraph_vertex (v : V) :
    HEq (SimpleGraph.EarStart.vertex v : G.EarStart (G.singletonSubgraph v)).toGraph
      (Graph.EarStart.vertex ⟨v, Set.mem_univ v⟩ :
        (Graph.ofSimpleGraph G).EarStart (Graph.noEdge {v} (Sym2 V))) :=
  cast_heq _ _

/-- Transporting a cycle initial stage gives the stage of the transported cycle. -/
theorem heq_toGraph_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    HEq (SimpleGraph.EarStart.cycle c hc).toGraph
      (Graph.EarStart.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)) :=
  cast_heq _ _

@[simp]
theorem isCycle_toGraph (s : G.EarStart H) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.isCycle_iff_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (heq_toGraph_vertex v)).trans
        ((Graph.EarStart.isCycle_vertex _).trans (SimpleGraph.EarStart.isCycle_vertex _).symm)
  | cycle c hc =>
      exact (Graph.EarStart.isCycle_iff_of_heq c.toGraph_toSubgraph
        (heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.isCycle_cycle _ _).trans (SimpleGraph.EarStart.isCycle_cycle _ _).symm)

/-- Transport to `Graph.ofSimpleGraph G` respects heterogeneous equality of initial stages. -/
theorem heq_toGraph_of_heq {H₁ H₂ : G.Subgraph} {s₁ : G.EarStart H₁} {s₂ : G.EarStart H₂}
    (hH : H₁ = H₂) (hs : HEq s₁ s₂) : HEq s₁.toGraph s₂.toGraph := by
  subst hH
  cases eq_of_heq hs
  rfl

/-- Transporting an initial stage to `Graph.ofSimpleGraph G` and back recovers it. -/
theorem heq_toSimpleGraph_toGraph (s : G.EarStart H) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.heq_toSimpleGraph_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (heq_toGraph_vertex v)).trans (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | @cycle u c hc =>
      refine (Graph.EarStart.heq_toSimpleGraph_of_heq c.toGraph_toSubgraph
        (heq_toGraph_cycle c hc)).trans ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans ?_)
      suffices ∀ c' : G.Walk u u, c' = c → ∀ hc', HEq (SimpleGraph.EarStart.cycle c' hc')
          (SimpleGraph.EarStart.cycle c hc) from this _ c.toSimpleGraph_toGraph _
      rintro _ rfl _
      rfl

end EarStart

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transporting an ear to the simple graph and back recovers it. -/
theorem Ear.heq_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    HEq e.toSimpleGraph.toGraph e := by
  suffices ∀ {L : Graph V (Sym2 V)} (f : (Graph.ofSimpleGraph G).Ear L), L = K →
      f.toWalk = e.toWalk → HEq f e from
    this _ (K.toGraph_toSimpleGraphSubgraph e.base_le)
      (by cases e <;> simp [SimpleGraph.Ear.toGraph])
  rintro _ f rfl hf
  exact heq_of_eq (Ear.ext _ _ hf)

namespace EarStart

/-- Transporting an initial stage to the simple graph and back recovers it. -/
theorem heq_toGraph_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      refine (SimpleGraph.EarStart.heq_toGraph_of_heq
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 _) (heq_toSimpleGraph_vertex v)).trans
        ((SimpleGraph.EarStart.heq_toGraph_vertex _).trans ?_)
      rfl
  | @cycle u c hc =>
      refine (SimpleGraph.EarStart.heq_toGraph_of_heq
        (Graph.Walk.toSimpleGraphSubgraph_walkGraph c _) (heq_toSimpleGraph_cycle c hc)).trans
        ((SimpleGraph.EarStart.heq_toGraph_cycle _ _).trans ?_)
      suffices ∀ c' : (Graph.ofSimpleGraph G).Walk u u, c' = c → ∀ hc',
          HEq (Graph.EarStart.cycle c' hc') (Graph.EarStart.cycle c hc) from
        this _ c.toGraph_toSimpleGraph _
      rintro _ rfl _
      rfl

end EarStart

end Graph

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- An ear decomposition of a subgraph `H` of a simple graph `G`, as an ear decomposition of
`H.toGraph` in `Graph.ofSimpleGraph G` with the graphs of the same stages and the transported
ears. -/
@[expose, reducible]
def toGraph (d : G.EarDecomposition H) : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  length := d.length
  graphAfter i := (d.subgraphAfter i).toGraph
  start := d.start.toGraph
  earAt i := ⟨_, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by rw [d.subgraphAfter_succ, Ear.add_toGraph]
  graphAfter_last := by rw [d.subgraphAfter_last]

@[simp]
theorem length_toGraph (d : G.EarDecomposition H) : d.toGraph.length = d.length := rfl

@[simp]
theorem graphAfter_toGraph (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toGraph.graphAfter i = (d.subgraphAfter i).toGraph := rfl

@[simp]
theorem earAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.earAt i = ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩ := rfl

@[simp]
theorem start_toGraph (d : G.EarDecomposition H) : d.toGraph.start = d.start.toGraph := rfl

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, ← subgraphAfter_zero]

theorem walkAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, ((d.walkAt i).2.2 : G.Walk _ _).toGraph⟩ := by
  rw [walkAt_def]
  exact (Graph.EarDecomposition.walkAt_eq _ _).trans (d.earAt i).toWalk_toGraph

theorem kindAt_toGraph_eq_open_iff (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.kindAt i = .open ↔ d.kindAt i = .«open» := by
  rw [kindAt_def, ← (d.earAt i).kind_toGraph_eq_open_iff]
  exact Iff.of_eq (congrArg (· = .open) (Graph.EarDecomposition.kindAt_eq d.toGraph i))

theorem kindAt_toGraph_eq_closed_iff (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.kindAt i = .closed ↔ d.kindAt i = .closed := by
  rw [kindAt_def, ← (d.earAt i).kind_toGraph_eq_closed_iff]
  exact Iff.of_eq (congrArg (· = .closed) (Graph.EarDecomposition.kindAt_eq d.toGraph i))

@[simp]
theorem isOpen_toGraph (d : G.EarDecomposition H) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff]
  exact and_congr d.start.isCycle_toGraph (forall_congr' d.kindAt_toGraph_eq_open_iff)

/-- A transported decomposition starts from a single vertex exactly when the original one does. -/
@[simp]
theorem isVertexStart_toGraph (d : G.EarDecomposition H) :
    d.toGraph.IsVertexStart ↔ ∃ v, d.initial = G.singletonSubgraph v := by
  rw [Graph.EarDecomposition.isVertexStart_iff, initial_toGraph]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subgraph.toGraph_inj.mp (by rw [hv, Subgraph.toGraph_singletonSubgraph])⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Set.mem_univ v⟩, by rw [hv, Subgraph.toGraph_singletonSubgraph]⟩

/-- Transporting a decomposition commutes with reindexing its target. -/
theorem toGraph_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  cases h
  simp only [copy_rfl, Graph.EarDecomposition.copy_rfl]

/-- Transporting a prefix of an ear decomposition gives the corresponding prefix of the
transported decomposition. -/
theorem toGraph_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k := by
  have hleft : (d.prefix k).toGraph.length = k :=
    (length_toGraph (d.prefix k)).trans (d.length_prefix k)
  have hright : (d.toGraph.prefix k).length = k := d.toGraph.length_prefix k
  have hlen : (d.prefix k).toGraph.length = (d.toGraph.prefix k).length :=
    hleft.trans hright.symm
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ?_
  · exact (d.toGraph.heq_start_prefix k).symm
  · refine (Fin.heq_fun_iff hlen).mpr fun i ↦ ?_
    let j : Fin k := Fin.cast hleft i
    have hj : (⟨i, hlen ▸ i.2⟩ : Fin (d.toGraph.prefix k).length) =
        Fin.cast hright.symm j := Fin.ext rfl
    rw [hj, Graph.EarDecomposition.earAt_prefix, earAt_toGraph, earAt_toGraph]
    exact Sigma.ext (congrArg Subgraph.toGraph (d.subgraphAfter_prefix k j.castSucc))
      (heq_of_eq (congrArg Ear.toGraph (d.earAt_prefix k j)))

/-- Transporting a decomposition to `Graph.ofSimpleGraph G` and back recovers it, reindexed along
`SimpleGraph.Subgraph.toSimpleGraphSubgraph_toGraph`. -/
@[simp]
theorem toSimpleGraph_toGraph (d : G.EarDecomposition H) :
    d.toGraph.toSimpleGraph = d.copy (H.toSimpleGraphSubgraph_toGraph _).symm := by
  refine EarDecomposition.ext rfl ?_ ?_ fun i ↦ ?_
  · simp
  · exact d.start.heq_toSimpleGraph_toGraph
  · refine (walkAt_def _ i).trans (Eq.trans ?_ ((walkAt_copy d _ _).trans (walkAt_def d _)).symm)
    exact (congrArg Ear.toWalk (Graph.EarDecomposition.earAt_toSimpleGraph d.toGraph i)).trans
      ((Ear.toWalk_copy _ _).trans
        ((congrArg Ear.toWalk (d.earAt i).toSimpleGraph_toGraph).trans (Ear.toWalk_copy _ _)))

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transporting a decomposition to the simple graph and back recovers it, reindexed along
`Graph.toGraph_toSimpleGraphSubgraph`. -/
@[simp]
theorem toGraph_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.toGraph = d.copy (K.toGraph_toSimpleGraphSubgraph d.final_le).symm := by
  refine EarDecomposition.ext _ _ (d.length_copy _).symm
    (d.start.heq_toGraph_toSimpleGraph.trans (d.heq_start_copy _).symm)
    ((Fin.heq_fun_iff (d.length_copy _).symm).mpr fun i ↦ ?_)
  rw [earAt_copy]
  refine Sigma.ext ?_ ?_
  · exact (Graph.toGraph_toSimpleGraphSubgraph _ _).trans (d.earAt_fst _).symm
  · exact (SimpleGraph.Ear.heq_toGraph_copy _ _).trans (Ear.heq_toGraph_toSimpleGraph _)

/-- A transported decomposition starts from a single vertex exactly when the original one does. -/
theorem exists_initial_toSimpleGraph_eq_singletonSubgraph_iff
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    (∃ v, d.toSimpleGraph.initial = G.singletonSubgraph v) ↔ d.IsVertexStart := by
  rw [← SimpleGraph.EarDecomposition.isVertexStart_toGraph, toGraph_toSimpleGraph,
    isVertexStart_copy]

/-- Transporting a prefix of a decomposition gives the corresponding prefix of the transported
decomposition. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) : (d.prefix k).toSimpleGraph = d.toSimpleGraph.prefix k := by
  have hzero : (d.prefix k).graphAfter 0 = d.graphAfter 0 := by
    simpa only [initial_eq_graphAfter] using d.initial_prefix k
  refine SimpleGraph.EarDecomposition.ext (d.length_prefix k) ?_ ?_ fun i ↦ ?_
  · exact (initial_toSimpleGraph _).trans ((Graph.toSimpleGraphSubgraph_congr hzero _ _).trans
      ((SimpleGraph.EarDecomposition.initial_prefix _ k).trans (initial_toSimpleGraph d)).symm)
  · exact EarStart.heq_toSimpleGraph_of_heq hzero (d.heq_start_prefix k)
  · refine (walkAt_toSimpleGraph _ i).trans (Eq.trans ?_
      ((SimpleGraph.EarDecomposition.walkAt_prefix _ k _).trans (walkAt_toSimpleGraph d _)).symm)
    have hi : (d.prefix k).walkAt i = _ := d.walkAt_prefix k (i.cast (d.length_prefix k))
    rw [hi]
    rfl

end Graph.EarDecomposition

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-- Ear decompositions of a subgraph `H` of a simple graph `G` correspond to ear decompositions of
`H.toGraph` in `Graph.ofSimpleGraph G`. -/
def earDecompositionEquivOfSimpleGraph (H : G.Subgraph) :
    G.EarDecomposition H ≃ (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  toFun d := d.toGraph
  invFun d := d.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph _)
  left_inv d := by
    dsimp only
    rw [EarDecomposition.toSimpleGraph_toGraph]
    rfl
  right_inv d := by
    dsimp only
    rw [EarDecomposition.toGraph_copy, Graph.EarDecomposition.toGraph_toSimpleGraph,
      Graph.EarDecomposition.copy_copy, Graph.EarDecomposition.copy_rfl]

@[simp]
theorem earDecompositionEquivOfSimpleGraph_apply {H : G.Subgraph}
    (d : G.EarDecomposition H) : H.earDecompositionEquivOfSimpleGraph d = d.toGraph := (rfl)

@[simp]
theorem earDecompositionEquivOfSimpleGraph_symm_apply {H : G.Subgraph}
    (d : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph) :
    H.earDecompositionEquivOfSimpleGraph.symm d =
      d.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph _) := (rfl)

end SimpleGraph.Subgraph
