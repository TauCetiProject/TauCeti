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
`Graph.ofSimpleGraph G`. This file transports ears, initial stages, and ear decompositions in both
directions and shows that the two transports are mutually inverse.

The direction from `Graph.ofSimpleGraph G` to `G` drops the redundant `Sym2 V` edge identities via
`Graph.toSimpleGraphSubgraph`; the direction from `G` to `Graph.ofSimpleGraph G` adds them via
`SimpleGraph.Subgraph.toGraph`. Both preserve the number of ears, every prefix subgraph, the
initial vertex or cycle, the walk and kind of every ear, prefix decompositions, and the
open-decomposition predicate. Results proved for either interface therefore apply to the other.

For a decomposition of all of `Graph.ofSimpleGraph G`, the target subgraph simplifies to `⊤` by
`Graph.toSimpleGraphSubgraph_ofSimpleGraph`; `SimpleGraph.EarDecomposition.copy` can then reindex
the transported decomposition to that canonical target.

## Main declarations

* `Graph.EarDecomposition.toSimpleGraph`, `SimpleGraph.EarDecomposition.toGraph`: the two
  transports of ear decompositions.
* `SimpleGraph.earDecompositionEquivOfSimpleGraph`: the transports form an equivalence.

## Implementation notes

`SimpleGraph.EarDecomposition.toGraph` is reducible and exposed, so the length of a transported
decomposition unfolds to the original length at reducible transparency, and `rw` and `simp` accept
`Fin` indices over either length.
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

namespace SimpleGraph.Ear

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Transport an ear over a simple subgraph `H` to an ear over `H.toGraph` in
`Graph.ofSimpleGraph G`. -/
def toGraph : G.Ear H → (Graph.ofSimpleGraph G).Ear H.toGraph
  | .«open» p hp hu hv huv hint hedge =>
      .open H.toGraph_le_ofSimpleGraph p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa using hu) (by simpa using hv) huv (by simpa using hint) (by simpa using hedge)
  | .closed c hc hu hint =>
      .closed H.toGraph_le_ofSimpleGraph c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa using hu) (by simpa using hint) fun _ he ↦ by
          simpa using closed_edges_notMem_edgeSet hint (by simpa using he)

@[simp]
theorem toWalk_toGraph (e : G.Ear H) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» => rw [toGraph, Graph.Ear.toWalk_open, toWalk_open]
  | closed => rw [toGraph, Graph.Ear.toWalk_closed, toWalk_closed]

@[simp]
theorem toSimpleGraph_kind_toGraph (e : G.Ear H) : e.toGraph.kind.toSimpleGraph = e.kind := by
  cases e <;> simp [toGraph]

/-- The graph traced by a transported ear is the graph of the subgraph traced by the ear. -/
@[simp]
theorem toGraph_toGraph (e : G.Ear H) : e.toGraph.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph]

/-- Adjoining a transported ear gives the graph of the subgraph obtained by adjoining the ear. -/
@[simp]
theorem add_toGraph (e : G.Ear H) : e.toGraph.add = e.adjoin.toGraph := by
  refine Graph.ext ?_ fun f x y ↦ ?_
  · simp [Graph.Ear.vertexSet_add, verts_adjoin]
  · rw [Graph.Ear.add_eq_union, Graph.Compatible.union_isLink, toGraph_toGraph]
    simp [adjoin_def, and_or_left]

end SimpleGraph.Ear

namespace SimpleGraph.EarStart

variable {V : Type u} {G : SimpleGraph V}

/-- Transport the initial vertex or cycle of a simple-graph ear decomposition to
`Graph.ofSimpleGraph G`. -/
def toGraph : {H : G.Subgraph} → G.EarStart H → (Graph.ofSimpleGraph G).EarStart H.toGraph
  | _, .vertex v =>
      (Subgraph.toGraph_singletonSubgraph v).symm ▸ .vertex ⟨v, Set.mem_univ v⟩
  | _, .cycle c hc =>
      c.toGraph_toSubgraph.symm ▸ .cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)

@[simp]
theorem isCycle_toGraph {H : G.Subgraph} (s : G.EarStart H) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s <;> simp [toGraph, Graph.EarStart.isCycle_iff_of_heq _ (eqRec_heq _ _)]

end SimpleGraph.EarStart

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Transport an ear decomposition of a simple subgraph `H` to a decomposition of `H.toGraph` in
`Graph.ofSimpleGraph G`, retaining every prefix and displayed ear. -/
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

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, ← subgraphAfter_zero]

theorem start_toGraph (d : G.EarDecomposition H) : d.toGraph.start = d.start.toGraph := rfl

theorem walkAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.walkAt i = ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toGraph⟩ := by
  rw [walkAt_def]
  exact (Graph.EarDecomposition.walkAt_eq _ _).trans (d.earAt i).toWalk_toGraph

theorem toSimpleGraph_kindAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.toGraph.kindAt i).toSimpleGraph = d.kindAt i := by
  rw [kindAt_def, ← (d.earAt i).toSimpleGraph_kind_toGraph]
  exact congrArg Graph.EarKind.toSimpleGraph (Graph.EarDecomposition.kindAt_eq d.toGraph i)

@[simp]
theorem isOpen_toGraph (d : G.EarDecomposition H) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff]
  refine and_congr d.start.isCycle_toGraph (forall_congr' fun i ↦ ?_)
  rw [← d.toSimpleGraph_kindAt_toGraph i, Graph.EarKind.toSimpleGraph_eq_open_iff]

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

/-- Transporting a prefix of an ear decomposition gives the corresponding prefix of the
transported decomposition. -/
theorem toGraph_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k := by
  have hlen := d.toGraph.length_prefix k
  refine Graph.EarDecomposition.ext _ _ hlen.symm (d.toGraph.heq_start_prefix k).symm
    (Function.hfunext (congrArg Fin hlen.symm) fun j j' hj ↦ ?_)
  obtain rfl : j' = Fin.cast hlen.symm j := Fin.ext ((Fin.heq_ext_iff hlen.symm).mp hj).symm
  exact heq_of_eq (d.toGraph.earAt_prefix k j).symm

end SimpleGraph.EarDecomposition

/-! ### Round trips -/

namespace SimpleGraph.Ear

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

@[simp]
theorem toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph _) = e :=
  Ear.ext <| by
    rw [toWalk_copy, Graph.Ear.toWalk_toSimpleGraph, toWalk_toGraph]
    dsimp only
    rw [Walk.toSimpleGraph_toGraph]

end SimpleGraph.Ear

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

private theorem heq_of_toWalk_eq {L : Graph V (Sym2 V)} (hL : L = K)
    (f : (Graph.ofSimpleGraph G).Ear L) (e : (Graph.ofSimpleGraph G).Ear K)
    (h : f.toWalk = e.toWalk) : f ≍ e := by
  subst hL
  exact heq_of_eq (Ear.ext _ _ h)

theorem heq_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toGraph ≍ e :=
  heq_of_toWalk_eq (K.toGraph_toSimpleGraphSubgraph e.base_le) _ _ <| by
    rw [SimpleGraph.Ear.toWalk_toGraph, toWalk_toSimpleGraph]
    dsimp only
    rw [Walk.toGraph_toSimpleGraph]

private theorem heq_toGraph_copy_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    {H : G.Subgraph} (h : K.toSimpleGraphSubgraph e.base_le = H) :
    (e.toSimpleGraph.copy h).toGraph ≍ e := by
  subst h
  rw [SimpleGraph.Ear.copy_rfl]
  exact e.heq_toGraph_toSimpleGraph

end Graph.Ear

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V}

private theorem toSimpleGraph_eqRec_heq {K L : Graph V (Sym2 V)} (h : K = L)
    (s : (Graph.ofSimpleGraph G).EarStart K) : (h ▸ s).toSimpleGraph ≍ s.toSimpleGraph := by
  subst h
  rfl

private theorem toGraph_eqRec_heq {H₁ H₂ : G.Subgraph} (h : H₁ = H₂) (s : G.EarStart H₁) :
    (h ▸ s).toGraph ≍ s.toGraph := by
  subst h
  rfl

theorem toSimpleGraph_heq_of_heq {K₁ K₂ : Graph V (Sym2 V)}
    {s₁ : (Graph.ofSimpleGraph G).EarStart K₁} {s₂ : (Graph.ofSimpleGraph G).EarStart K₂}
    (hK : K₁ = K₂) (hs : s₁ ≍ s₂) : s₁.toSimpleGraph ≍ s₂.toSimpleGraph := by
  subst hK
  cases eq_of_heq hs
  rfl

theorem heq_toGraph_toSimpleGraph {K : Graph V (Sym2 V)}
    (s : (Graph.ofSimpleGraph G).EarStart K) : s.toSimpleGraph.toGraph ≍ s := by
  cases s with
  | vertex v =>
    unfold toSimpleGraph
    refine (toGraph_eqRec_heq _ _).trans ?_
    unfold SimpleGraph.EarStart.toGraph
    exact eqRec_heq _ _
  | @cycle u c hc =>
    unfold toSimpleGraph
    refine (toGraph_eqRec_heq _ _).trans ?_
    unfold SimpleGraph.EarStart.toGraph
    refine (eqRec_heq _ _).trans ?_
    suffices ∀ c' : (Graph.ofSimpleGraph G).Walk u u, c' = c → ∀ hc', cycle c' hc' ≍ cycle c hc
      from this _ c.toGraph_toSimpleGraph _
    rintro _ rfl _
    rfl

end Graph.EarStart

namespace SimpleGraph.EarStart

variable {V : Type u} {G : SimpleGraph V}

theorem heq_toSimpleGraph_toGraph {H : G.Subgraph} (s : G.EarStart H) :
    s.toGraph.toSimpleGraph ≍ s := by
  cases s with
  | vertex v =>
    unfold toGraph
    exact (Graph.EarStart.toSimpleGraph_eqRec_heq _ _).trans
      (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | @cycle u c hc =>
    unfold toGraph
    refine (Graph.EarStart.toSimpleGraph_eqRec_heq _ _).trans
      ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans ?_)
    suffices ∀ c' : G.Walk u u, c' = c → ∀ hc', cycle c' hc' ≍ cycle c hc
      from this _ c.toSimpleGraph_toGraph _
    rintro _ rfl _
    rfl

end SimpleGraph.EarStart

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {K : Graph V (Sym2 V)}

private theorem sigma_toSimpleGraph_eq {w : Σ u v, (Graph.ofSimpleGraph G).Walk u v}
    {w' : Σ u v, G.Walk u v} (h : w = ⟨w'.1, w'.2.1, w'.2.2.toGraph⟩) :
    (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : Σ u v, G.Walk u v) = w' := by
  subst h
  dsimp only
  rw [Walk.toSimpleGraph_toGraph]

/-- Transporting a decomposition to `Graph.ofSimpleGraph G` and back recovers it, after both
target graphs are reindexed along the identification of `H` with `K`. -/
@[simp]
theorem toSimpleGraph_copy_toGraph (d : G.EarDecomposition H) (hK : H.toGraph = K)
    (hH : K.toSimpleGraphSubgraph (d.toGraph.copy hK).final_le = H) :
    (d.toGraph.copy hK).toSimpleGraph.copy hH = d := by
  subst hK
  refine SimpleGraph.EarDecomposition.ext rfl ?_ ?_ fun i ↦ ?_
  · rw [initial_copy, Graph.EarDecomposition.initial_toSimpleGraph]
    exact (Subgraph.toSimpleGraphSubgraph_toGraph _ _).trans (subgraphAfter_zero d)
  · rw [start_copy, Graph.EarDecomposition.start_toSimpleGraph]
    exact d.start.heq_toSimpleGraph_toGraph
  · refine (walkAt_copy _ _ _).trans ((Graph.EarDecomposition.walkAt_toSimpleGraph _ _).trans ?_)
    exact sigma_toSimpleGraph_eq
      ((Graph.EarDecomposition.walkAt_copy _ _ _).trans (d.walkAt_toGraph i))

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {K : Graph V (Sym2 V)}

/-- Transporting a decomposition of a subgraph of `Graph.ofSimpleGraph G` to `G` and back
recovers it, after both target graphs are reindexed along the identification of `H` with `K`. -/
@[simp]
theorem toGraph_copy_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (hH : K.toSimpleGraphSubgraph d.final_le = H) (hK : H.toGraph = K) :
    (d.toSimpleGraph.copy hH).toGraph.copy hK = d := by
  refine Graph.EarDecomposition.ext _ _ rfl
    ((heq_start_copy _ _).trans d.start.heq_toGraph_toSimpleGraph)
    (heq_of_eq (funext fun i ↦ Sigma.ext ?_ ?_))
  · exact (Graph.toGraph_toSimpleGraphSubgraph _ _).trans (d.earAt_fst i).symm
  · exact Graph.Ear.heq_toGraph_copy_toSimpleGraph _ _

/-- Transporting a prefix of a decomposition of a subgraph of `Graph.ofSimpleGraph G` gives the
corresponding prefix of the transported decomposition. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) : (d.prefix k).toSimpleGraph = d.toSimpleGraph.prefix k := by
  have hlen := d.length_prefix k
  have hzero : (d.prefix k).graphAfter 0 = d.graphAfter 0 := by
    simpa only [initial_eq_graphAfter] using d.initial_prefix k
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ fun i ↦ ?_
  · exact (initial_toSimpleGraph _).trans ((Graph.toSimpleGraphSubgraph_congr hzero _ _).trans
      ((initial_toSimpleGraph d).symm.trans
        (SimpleGraph.EarDecomposition.initial_prefix d.toSimpleGraph k).symm))
  · exact Graph.EarStart.toSimpleGraph_heq_of_heq hzero (d.heq_start_prefix k)
  · refine (walkAt_toSimpleGraph _ i).trans (Eq.trans ?_
      ((SimpleGraph.EarDecomposition.walkAt_prefix _ k _).trans (walkAt_toSimpleGraph d _)).symm)
    exact congrArg (fun w : Σ u v, (Graph.ofSimpleGraph G).Walk u v ↦
      (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : Σ u v, G.Walk u v)) (d.walkAt_prefix k (i.cast hlen))

end Graph.EarDecomposition

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Ear decompositions of a subgraph `H` of a simple graph `G` correspond to ear decompositions of
an equal target graph in `Graph.ofSimpleGraph G`. -/
def earDecompositionEquivOfSimpleGraph {H : G.Subgraph} {K : Graph V (Sym2 V)}
    (h : H.toGraph = K) :
    G.EarDecomposition H ≃ (Graph.ofSimpleGraph G).EarDecomposition K where
  toFun d := d.toGraph.copy h
  invFun d := d.toSimpleGraph.copy <|
    (Graph.toSimpleGraphSubgraph_congr h.symm _ H.toGraph_le_ofSimpleGraph).trans
      (H.toSimpleGraphSubgraph_toGraph _)
  left_inv d := d.toSimpleGraph_copy_toGraph h _
  right_inv d := d.toGraph_copy_toSimpleGraph _ h

@[simp]
theorem earDecompositionEquivOfSimpleGraph_apply {H : G.Subgraph} {K : Graph V (Sym2 V)}
    (h : H.toGraph = K) (d : G.EarDecomposition H) :
    earDecompositionEquivOfSimpleGraph h d = d.toGraph.copy h := (rfl)

@[simp]
theorem earDecompositionEquivOfSimpleGraph_symm_apply {H : G.Subgraph}
    {K : Graph V (Sym2 V)} (h : H.toGraph = K)
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    (earDecompositionEquivOfSimpleGraph h).symm d = d.toSimpleGraph.copy
      ((Graph.toSimpleGraphSubgraph_congr h.symm _ H.toGraph_le_ofSimpleGraph).trans
        (H.toSimpleGraphSubgraph_toGraph _)) := (rfl)

end SimpleGraph
