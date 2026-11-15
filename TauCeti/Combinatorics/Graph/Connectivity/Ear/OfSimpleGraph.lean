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

This file establishes the bidirectional correspondence between ears, initial stages, and ear
decompositions of subgraphs of `Graph.ofSimpleGraph G` and the `SimpleGraph.Subgraph`-based ear
interface of a simple graph `G`:

* `Graph.Ear.toSimpleGraph`, `Graph.EarStart.toSimpleGraph`, and
  `Graph.EarDecomposition.toSimpleGraph` forget the redundant `Sym2 V` edge identities on graphs
  below `Graph.ofSimpleGraph G`.
* `SimpleGraph.Ear.toGraph`, `SimpleGraph.EarStart.toGraph`, and
  `SimpleGraph.EarDecomposition.toGraph` reconstruct the edge-labelled multigraph data over
  `H.toGraph`, recovering the closed-ear unused-edge condition from
  `SimpleGraph.Ear.closed_edges_notMem_edgeSet`.
* Both directions commute with `vertex`, `cycle`, `copy`, `snoc`, and `prefix`, preserve initial
  stages, stage subgraphs, ear kinds, ear walks, openness, and vertex-startedness, and compose to
  the identity up to canonical `copy` reindexing, yielding
  `SimpleGraph.Subgraph.earEquivOfSimpleGraph`,
  `SimpleGraph.Subgraph.earDecompositionEquivOfSimpleGraph`, and the whole-graph equivalence
  `SimpleGraph.earDecompositionEquivOfSimpleGraph`.

## Implementation notes

Only `Graph.EarDecomposition.toSimpleGraph` and `SimpleGraph.EarDecomposition.toGraph` carry
`@[expose]`, matching `SimpleGraph.EarDecomposition.copy`, `snoc`, and `prefix`, so that dependent
`Fin` indices over `.length` and target subgraphs of `.prefix` reduce in types without `Fin.cast`
or `.copy` wrappers. All other conversion and equivalence definitions keep their bodies unexposed
with characteristic `@[simp]` lemmas proved via `:= (rfl)`.
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

namespace SimpleGraph.EarKind

/-- Convert a simple-graph ear kind (`open` or `closed`) to the corresponding `Graph.EarKind`. -/
def toGraph : SimpleGraph.EarKind → Graph.EarKind
  | .«open» => .open
  | .closed => .closed

@[simp] theorem toGraph_open : toGraph .«open» = .open := (rfl)
@[simp] theorem toGraph_closed : toGraph .closed = .closed := (rfl)

@[simp]
theorem toGraph_eq_open_iff {k : SimpleGraph.EarKind} : k.toGraph = .open ↔ k = .«open» := by
  cases k <;> simp

@[simp]
theorem toGraph_eq_closed_iff {k : SimpleGraph.EarKind} : k.toGraph = .closed ↔ k = .closed := by
  cases k <;> simp

theorem toGraph_injective : Function.Injective toGraph := by
  intro k l h
  cases k <;> cases l <;> simp_all

@[simp]
theorem toGraph_inj {k l : SimpleGraph.EarKind} : k.toGraph = l.toGraph ↔ k = l :=
  toGraph_injective.eq_iff

@[simp]
theorem toSimpleGraph_toGraph (k : SimpleGraph.EarKind) : k.toGraph.toSimpleGraph = k := by
  cases k <;> simp

end SimpleGraph.EarKind

namespace Graph.EarKind

@[simp]
theorem toGraph_toSimpleGraph (k : Graph.EarKind) : k.toSimpleGraph.toGraph = k := by
  cases k <;> simp

/-- Equivalence between multigraph ear kinds and simple-graph ear kinds. -/
def equivSimpleGraph : Graph.EarKind ≃ SimpleGraph.EarKind where
  toFun := toSimpleGraph
  invFun := SimpleGraph.EarKind.toGraph
  left_inv := toGraph_toSimpleGraph
  right_inv := SimpleGraph.EarKind.toSimpleGraph_toGraph

@[simp]
theorem equivSimpleGraph_apply (k : Graph.EarKind) : equivSimpleGraph k = k.toSimpleGraph := (rfl)

@[simp]
theorem equivSimpleGraph_symm_apply (k : SimpleGraph.EarKind) :
    equivSimpleGraph.symm k = k.toGraph := (rfl)

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

@[simp]
theorem toSimpleGraph_copy {K' : Graph V (Sym2 V)} (e : (Graph.ofSimpleGraph G).Ear K)
    (h : K = K') :
    (e.copy h).toSimpleGraph =
      e.toSimpleGraph.copy (Graph.toSimpleGraphSubgraph_congr h e.base_le (e.copy h).base_le) := by
  ext1
  rw [toWalk_toSimpleGraph, SimpleGraph.Ear.toWalk_copy, Graph.Ear.toWalk_copy,
    toWalk_toSimpleGraph]

end Graph.Ear

namespace SimpleGraph.Ear

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Transport a simple-graph ear over `H : G.Subgraph` to an edge-labelled ear of
`Graph.ofSimpleGraph G` over `H.toGraph`. In the closed case, the unused-edge requirement follows
from `SimpleGraph.Ear.closed_edges_notMem_edgeSet`. -/
def toGraph (e : G.Ear H) : (Graph.ofSimpleGraph G).Ear H.toGraph :=
  match e with
  | .«open» p hp hu hv huv hint hedge =>
      .open H.toGraph_le_ofSimpleGraph p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa using hu) (by simpa using hv) huv
        (by simpa using hint) (by simpa using hedge)
  | .closed c hc hu hint =>
      .closed H.toGraph_le_ofSimpleGraph c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa using hu) (by simpa using hint)
        (fun f hf ↦ by
          rw [SimpleGraph.Subgraph.edgeSet_toGraph]
          exact SimpleGraph.Ear.closed_edges_notMem_edgeSet hint (by simpa using hf))

@[simp]
theorem toGraph_open {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ H.verts)
    (hv : v ∈ H.verts) (huv : u ≠ v) (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ H.verts)
    (hedge : ∀ f ∈ p.edges, f ∉ H.edgeSet) :
    (SimpleGraph.Ear.«open» p hp hu hv huv hint hedge).toGraph =
      Graph.Ear.open H.toGraph_le_ofSimpleGraph p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa using hu) (by simpa using hv) huv
        (by simpa using hint) (by simpa using hedge) := (rfl)

@[simp]
theorem toGraph_closed {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hu : u ∈ H.verts)
    (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts) :
    (SimpleGraph.Ear.closed c hc hu hint).toGraph =
      Graph.Ear.closed H.toGraph_le_ofSimpleGraph c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa using hu) (by simpa using hint)
        (fun f hf ↦ by
          rw [SimpleGraph.Subgraph.edgeSet_toGraph]
          exact SimpleGraph.Ear.closed_edges_notMem_edgeSet hint (by simpa using hf)) := (rfl)

@[simp]
theorem kind_toGraph (e : G.Ear H) : e.toGraph.kind = e.kind.toGraph := by
  cases e <;> simp [toGraph, SimpleGraph.EarKind.toGraph]

@[simp]
theorem toWalk_toGraph (e : G.Ear H) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» => unfold toGraph; rw [Graph.Ear.toWalk_open, SimpleGraph.Ear.toWalk_open]
  | closed => unfold toGraph; rw [Graph.Ear.toWalk_closed, SimpleGraph.Ear.toWalk_closed]

/-- The multigraph traced by a transported ear is the graph associated to the simple subgraph
traced by the ear. -/
@[simp]
theorem toGraph_toGraph (e : G.Ear H) : e.toGraph.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp

/-- Transporting an ear to `Graph.ofSimpleGraph G` commutes with adjoining it to its base. -/
@[simp]
theorem add_toGraph (e : G.Ear H) : e.toGraph.add = e.adjoin.toGraph := by
  refine (Graph.Compatible.of_le_le e.toGraph.add_le e.adjoin.toGraph_le_ofSimpleGraph).ext ?_ ?_
  · simp [toGraph_toGraph]
  · simp [toGraph_toGraph]

@[simp]
theorem toGraph_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    (e.copy h).toGraph = e.toGraph.copy (congrArg Subgraph.toGraph h) := by
  subst h
  simp

@[simp]
theorem toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph =
      e.copy (H.toSimpleGraphSubgraph_toGraph e.toGraph.base_le).symm := by
  ext1
  rw [e.toGraph.toWalk_toSimpleGraph, e.toWalk_toGraph]
  simp

end SimpleGraph.Ear

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

@[simp]
theorem toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toGraph = e.copy (K.toGraph_toSimpleGraphSubgraph e.base_le).symm := by
  ext1
  rw [e.toSimpleGraph.toWalk_toGraph, e.toWalk_toSimpleGraph]
  simp

end Graph.Ear

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-- Ears over `H : G.Subgraph` are canonically equivalent to ears of `Graph.ofSimpleGraph G` over
`H.toGraph`. -/
def earEquivOfSimpleGraph (H : G.Subgraph) :
    G.Ear H ≃ (Graph.ofSimpleGraph G).Ear H.toGraph where
  toFun := SimpleGraph.Ear.toGraph
  invFun e := e.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph e.base_le)
  left_inv e := by simp
  right_inv e := by simp

@[simp]
theorem earEquivOfSimpleGraph_apply (H : G.Subgraph) (e : G.Ear H) :
    H.earEquivOfSimpleGraph e = e.toGraph := (rfl)

@[simp]
theorem earEquivOfSimpleGraph_symm_apply (H : G.Subgraph)
    (e : (Graph.ofSimpleGraph G).Ear H.toGraph) :
    H.earEquivOfSimpleGraph.symm e =
      e.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph e.base_le) := (rfl)

end SimpleGraph.Subgraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Ears of `Graph.ofSimpleGraph G` over `K ≤ Graph.ofSimpleGraph G` are canonically equivalent to
ears over `K.toSimpleGraphSubgraph hK`. -/
def earEquivSimpleGraph (hK : K ≤ Graph.ofSimpleGraph G) :
    (Graph.ofSimpleGraph G).Ear K ≃ G.Ear (K.toSimpleGraphSubgraph hK) where
  toFun e := e.toSimpleGraph.copy (toSimpleGraphSubgraph_congr rfl e.base_le hK)
  invFun e := e.toGraph.copy (K.toGraph_toSimpleGraphSubgraph hK)
  left_inv e := by simp
  right_inv e := by simp

@[simp]
theorem earEquivSimpleGraph_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (e : (Graph.ofSimpleGraph G).Ear K) :
    earEquivSimpleGraph hK e =
      e.toSimpleGraph.copy (toSimpleGraphSubgraph_congr rfl e.base_le hK) := (rfl)

@[simp]
theorem earEquivSimpleGraph_symm_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (e : G.Ear (K.toSimpleGraphSubgraph hK)) :
    (earEquivSimpleGraph hK).symm e = e.toGraph.copy (K.toGraph_toSimpleGraphSubgraph hK) := (rfl)

end Graph

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

theorem heq_toSimpleGraph_of_heq {K₁ K₂ : Graph V (Sym2 V)}
    {s₁ : (Graph.ofSimpleGraph G).EarStart K₁} {s₂ : (Graph.ofSimpleGraph G).EarStart K₂}
    (hK : K₁ = K₂) (hs : HEq s₁ s₂) :
    HEq s₁.toSimpleGraph s₂.toSimpleGraph := by
  subst hK
  cases eq_of_heq hs
  rfl

end Graph.EarStart

namespace SimpleGraph.EarStart

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Transport the initial vertex or cycle witness of a simple-graph ear decomposition to the
corresponding initial stage of `Graph.ofSimpleGraph G`. -/
def toGraph (s : G.EarStart H) : (Graph.ofSimpleGraph G).EarStart H.toGraph := by
  cases s with
  | vertex v =>
      exact (SimpleGraph.Subgraph.toGraph_singletonSubgraph (G := G) v).symm ▸
        .vertex ⟨v, by simp⟩
  | cycle c hc =>
      exact (SimpleGraph.Walk.toGraph_toSubgraph c).symm ▸
        .cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)

/-- Transporting a vertex initial stage selects the corresponding multigraph vertex stage. -/
theorem heq_toGraph_vertex (v : V) :
    HEq (SimpleGraph.EarStart.vertex (G := G) v).toGraph
      (Graph.EarStart.vertex (G := Graph.ofSimpleGraph G) ⟨v, by simp⟩) := by
  unfold toGraph
  exact eqRec_heq _ _

/-- Transporting a cycle initial stage selects the corresponding multigraph cycle stage. -/
theorem heq_toGraph_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    HEq (SimpleGraph.EarStart.cycle c hc).toGraph
      (Graph.EarStart.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)) := by
  unfold toGraph
  exact eqRec_heq _ _

@[simp]
theorem isCycle_toGraph (s : G.EarStart H) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.isCycle_iff_of_heq
        (SimpleGraph.Subgraph.toGraph_singletonSubgraph v) (heq_toGraph_vertex v)).trans
        ((Graph.EarStart.isCycle_vertex ⟨v, by simp⟩).trans
          (SimpleGraph.EarStart.isCycle_vertex v).symm)
  | cycle c hc =>
      exact (Graph.EarStart.isCycle_iff_of_heq
        (SimpleGraph.Walk.toGraph_toSubgraph c) (heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.isCycle_cycle c.toGraph _).trans
          (SimpleGraph.EarStart.isCycle_cycle c hc).symm)

theorem heq_toGraph_of_heq {H₁ H₂ : G.Subgraph} {s₁ : G.EarStart H₁} {s₂ : G.EarStart H₂}
    (hH : H₁ = H₂) (hs : HEq s₁ s₂) :
    HEq s₁.toGraph s₂.toGraph := by
  subst hH
  cases eq_of_heq hs
  rfl

private theorem cycle_heq {u : V} {c₁ c₂ : G.Walk u u} (h : c₁ = c₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) :
    HEq (SimpleGraph.EarStart.cycle c₁ hc₁) (SimpleGraph.EarStart.cycle c₂ hc₂) := by
  subst h
  rfl

/-- Transporting an initial stage to `Graph.ofSimpleGraph G` and back recovers the original stage
up to heterogeneous equality. -/
theorem heq_toSimpleGraph_toGraph (s : G.EarStart H) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.heq_toSimpleGraph_of_heq
        (SimpleGraph.Subgraph.toGraph_singletonSubgraph v) (heq_toGraph_vertex v)).trans
        (Graph.EarStart.heq_toSimpleGraph_vertex ⟨v, by simp⟩)
  | cycle c hc =>
      exact (Graph.EarStart.heq_toSimpleGraph_of_heq
        (SimpleGraph.Walk.toGraph_toSubgraph c) (heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle c.toGraph _).trans
          (cycle_heq (SimpleGraph.Walk.toSimpleGraph_toGraph c) _ hc))

end SimpleGraph.EarStart

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

private theorem cycle_heq {x : V} {p₁ p₂ : (Graph.ofSimpleGraph G).Walk x x} (h : p₁ = p₂)
    (hp₁ : p₁.IsCycle) (hp₂ : p₂.IsCycle) :
    HEq (Graph.EarStart.cycle p₁ hp₁) (Graph.EarStart.cycle p₂ hp₂) := by
  subst h
  rfl

/-- Transporting an initial stage of `Graph.ofSimpleGraph G` to `G` and back recovers the original
stage up to heterogeneous equality. -/
theorem heq_toGraph_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      have hv : (⟨v.1, by simp⟩ : V(Graph.ofSimpleGraph G)) = v := Subtype.ext rfl
      exact (SimpleGraph.EarStart.heq_toGraph_of_heq
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 _)
        (heq_toSimpleGraph_vertex v)).trans
        ((SimpleGraph.EarStart.heq_toGraph_vertex v.1).trans (by rw [hv]))
  | cycle p hp =>
      exact (SimpleGraph.EarStart.heq_toGraph_of_heq
        (Graph.Walk.toSimpleGraphSubgraph_walkGraph p _)
        (heq_toSimpleGraph_cycle p hp)).trans
        ((SimpleGraph.EarStart.heq_toGraph_cycle p.toSimpleGraph _).trans
          (cycle_heq (Graph.Walk.toGraph_toSimpleGraph p) _ hp))

end Graph.EarStart

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

private theorem earStart_subst_heq {H₁ H₂ : G.Subgraph} (h : H₁ = H₂) (s : G.EarStart H₁) :
    HEq (h ▸ s) s := by
  subst h
  rfl

/-- Initial-stage witnesses on `H : G.Subgraph` are canonically equivalent to initial-stage
witnesses on `H.toGraph` in `Graph.ofSimpleGraph G`. -/
def earStartEquivOfSimpleGraph (H : G.Subgraph) :
    G.EarStart H ≃ (Graph.ofSimpleGraph G).EarStart H.toGraph where
  toFun := SimpleGraph.EarStart.toGraph
  invFun s := H.toSimpleGraphSubgraph_toGraph s.le ▸ s.toSimpleGraph
  left_inv s := eq_of_heq <|
    (earStart_subst_heq (H.toSimpleGraphSubgraph_toGraph s.toGraph.le)
      s.toGraph.toSimpleGraph).trans s.heq_toSimpleGraph_toGraph
  right_inv s := by
    dsimp only
    exact eq_of_heq <|
      (SimpleGraph.EarStart.heq_toGraph_of_heq
        (H.toSimpleGraphSubgraph_toGraph s.le).symm
        (earStart_subst_heq (H.toSimpleGraphSubgraph_toGraph s.le) s.toSimpleGraph)).trans
        s.heq_toGraph_toSimpleGraph

@[simp]
theorem earStartEquivOfSimpleGraph_apply (H : G.Subgraph) (s : G.EarStart H) :
    H.earStartEquivOfSimpleGraph s = s.toGraph := (rfl)

@[simp]
theorem earStartEquivOfSimpleGraph_symm_apply (H : G.Subgraph)
    (s : (Graph.ofSimpleGraph G).EarStart H.toGraph) :
    H.earStartEquivOfSimpleGraph.symm s =
      (H.toSimpleGraphSubgraph_toGraph s.le ▸ s.toSimpleGraph) := (rfl)

end SimpleGraph.Subgraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

private theorem earStart_subst_heq {K₁ K₂ : Graph V (Sym2 V)} (h : K₁ = K₂)
    (s : (Graph.ofSimpleGraph G).EarStart K₁) : HEq (h ▸ s) s := by
  subst h
  rfl

/-- Initial-stage witnesses of `Graph.ofSimpleGraph G` on `K ≤ Graph.ofSimpleGraph G` are
canonically equivalent to initial-stage witnesses on `K.toSimpleGraphSubgraph hK`. -/
def earStartEquivSimpleGraph (hK : K ≤ Graph.ofSimpleGraph G) :
    (Graph.ofSimpleGraph G).EarStart K ≃ G.EarStart (K.toSimpleGraphSubgraph hK) where
  toFun s := toSimpleGraphSubgraph_congr rfl s.le hK ▸ s.toSimpleGraph
  invFun s := K.toGraph_toSimpleGraphSubgraph hK ▸ s.toGraph
  left_inv s := by
    dsimp only
    exact eq_of_heq <|
      (earStart_subst_heq (K.toGraph_toSimpleGraphSubgraph hK) _).trans <|
        (SimpleGraph.EarStart.heq_toGraph_of_heq
          (toSimpleGraphSubgraph_congr rfl s.le hK).symm
          (SimpleGraph.Subgraph.earStart_subst_heq
            (toSimpleGraphSubgraph_congr rfl s.le hK) s.toSimpleGraph)).trans
          s.heq_toGraph_toSimpleGraph
  right_inv s := by
    dsimp only
    exact eq_of_heq <|
      (SimpleGraph.Subgraph.earStart_subst_heq
        (toSimpleGraphSubgraph_congr rfl (K.toGraph_toSimpleGraphSubgraph hK ▸ s.toGraph).le hK)
        (K.toGraph_toSimpleGraphSubgraph hK ▸ s.toGraph).toSimpleGraph).trans <|
        (Graph.EarStart.heq_toSimpleGraph_of_heq
          (K.toGraph_toSimpleGraphSubgraph hK).symm
          (earStart_subst_heq (K.toGraph_toSimpleGraphSubgraph hK) s.toGraph)).trans
          s.heq_toSimpleGraph_toGraph

@[simp]
theorem earStartEquivSimpleGraph_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (s : (Graph.ofSimpleGraph G).EarStart K) :
    earStartEquivSimpleGraph hK s =
      (toSimpleGraphSubgraph_congr rfl s.le hK ▸ s.toSimpleGraph) := (rfl)

@[simp]
theorem earStartEquivSimpleGraph_symm_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (s : G.EarStart (K.toSimpleGraphSubgraph hK)) :
    (earStartEquivSimpleGraph hK).symm s =
      (K.toGraph_toSimpleGraphSubgraph hK ▸ s.toGraph) := (rfl)

end Graph

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
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff]
  refine and_congr d.start.isCycle_toSimpleGraph ?_
  exact forall_congr' fun i : Fin d.length ↦ by
    rw [d.kindAt_toSimpleGraph i]
    simp

/-- The transported decomposition starts at a singleton subgraph if and only if the multigraph
decomposition is vertex-started. -/
theorem exists_initial_toSimpleGraph_eq_singletonSubgraph_iff
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    (∃ v : V, d.toSimpleGraph.initial = G.singletonSubgraph v) ↔ d.IsVertexStart := by
  rw [Graph.EarDecomposition.isVertexStart_iff, initial_toSimpleGraph,
    Graph.EarDecomposition.initial_eq_graphAfter]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨⟨v, by simp⟩, ?_⟩
    have h := congrArg SimpleGraph.Subgraph.toGraph hv
    simpa only [Graph.toGraph_toSimpleGraphSubgraph,
      SimpleGraph.Subgraph.toGraph_singletonSubgraph] using h
  · rintro ⟨v, hv⟩
    refine ⟨v.1, ?_⟩
    have hle : Graph.noEdge {v.1} (Sym2 V) ≤ Graph.ofSimpleGraph G := hv ▸ d.graphAfter_le 0
    exact (Graph.toSimpleGraphSubgraph_congr hv (d.graphAfter_le 0) hle).trans
      (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 hle)

@[simp]
theorem toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    (Graph.EarDecomposition.vertex v).toSimpleGraph =
      (SimpleGraph.EarDecomposition.vertex G v.1).copy
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1
          (Graph.EarDecomposition.vertex v).final_le).symm := by
  refine SimpleGraph.EarDecomposition.ext (by simp) ?_ ?_ (fun i ↦ Fin.elim0 (Fin.cast (by simp) i))
  · simp [Graph.EarDecomposition.graphAfter_vertex_zero]
  · rw [SimpleGraph.EarDecomposition.start_copy, SimpleGraph.EarDecomposition.start_vertex]
    exact (Graph.EarStart.heq_toSimpleGraph_of_heq
      (Graph.EarDecomposition.graphAfter_vertex_zero v)
      (Graph.EarDecomposition.heq_start_vertex v)).trans
      ((Graph.EarStart.heq_toSimpleGraph_vertex v).trans (eqRec_heq _ _).symm)

@[simp]
theorem toSimpleGraph_cycle {x : V} (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) :
    (Graph.EarDecomposition.cycle p hp).toSimpleGraph =
      (SimpleGraph.EarDecomposition.cycle p.toSimpleGraph
        (p.isCycle_toSimpleGraph_iff.mpr hp)).copy
        (Graph.Walk.toSimpleGraphSubgraph_walkGraph p
          (Graph.EarDecomposition.cycle p hp).final_le).symm := by
  refine SimpleGraph.EarDecomposition.ext (by simp) ?_ ?_ (fun i ↦ Fin.elim0 (Fin.cast (by simp) i))
  · simp [Graph.EarDecomposition.graphAfter_cycle_zero]
  · rw [SimpleGraph.EarDecomposition.start_copy, SimpleGraph.EarDecomposition.start_cycle]
    exact (Graph.EarStart.heq_toSimpleGraph_of_heq
      (Graph.EarDecomposition.graphAfter_cycle_zero p hp)
      (Graph.EarDecomposition.heq_start_cycle p hp)).trans
      ((Graph.EarStart.heq_toSimpleGraph_cycle p hp).trans (eqRec_heq _ _).symm)

@[simp]
theorem toSimpleGraph_copy {K' : Graph V (Sym2 V)}
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) (h : K = K') :
    (d.copy h).toSimpleGraph =
      d.toSimpleGraph.copy (Graph.toSimpleGraphSubgraph_congr h d.final_le (h ▸ d.final_le)) := by
  subst h
  rw [d.copy_rfl, d.toSimpleGraph.copy_rfl]

private theorem walkAt_toSimpleGraph_snoc (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (ear : (Graph.ofSimpleGraph G).Ear K) (j : Fin (d.length + 1)) :
    (d.snoc ear).toSimpleGraph.walkAt (Fin.cast (d.length_snoc ear).symm j) =
      (d.toSimpleGraph.snoc ear.toSimpleGraph).walkAt j := by
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · calc
      (d.snoc ear).toSimpleGraph.walkAt
          (Fin.cast (d.length_snoc ear).symm (Fin.last d.length)) =
          ear.toSimpleGraph.toWalk :=
        ((d.snoc ear).walkAt_toSimpleGraph
          (Fin.cast (d.length_snoc ear).symm (Fin.last d.length))).trans <| by
          rw [Graph.EarDecomposition.walkAt_eq, d.earAt_snoc_last ear,
            Graph.Ear.toWalk_toSimpleGraph]
      _ = (d.toSimpleGraph.snoc ear.toSimpleGraph).walkAt (Fin.last d.length) :=
        (d.toSimpleGraph.walkAt_snoc_last ear.toSimpleGraph).symm
  · calc
      (d.snoc ear).toSimpleGraph.walkAt
          (Fin.cast (d.length_snoc ear).symm k.castSucc) =
          d.toSimpleGraph.walkAt k :=
        ((d.snoc ear).walkAt_toSimpleGraph
          (Fin.cast (d.length_snoc ear).symm k.castSucc)).trans <| by
          rw [Graph.EarDecomposition.walkAt_eq, d.earAt_snoc_castSucc ear,
            ← Graph.EarDecomposition.walkAt_eq, ← d.walkAt_toSimpleGraph k]
      _ = (d.toSimpleGraph.snoc ear.toSimpleGraph).walkAt k.castSucc :=
        (d.toSimpleGraph.walkAt_snoc_castSucc ear.toSimpleGraph k).symm

@[simp]
theorem toSimpleGraph_snoc (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (ear : (Graph.ofSimpleGraph G).Ear K) :
    (d.snoc ear).toSimpleGraph =
      (d.toSimpleGraph.snoc ear.toSimpleGraph).copy
        (ear.toSimpleGraphSubgraph_add (d.snoc ear).final_le).symm := by
  have hlen : (d.snoc ear).toSimpleGraph.length =
      ((d.toSimpleGraph.snoc ear.toSimpleGraph).copy
        (ear.toSimpleGraphSubgraph_add (d.snoc ear).final_le).symm).length :=
    d.length_snoc ear
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ (fun i ↦ ?_)
  · simp only [initial_toSimpleGraph, SimpleGraph.EarDecomposition.initial_copy,
      SimpleGraph.EarDecomposition.initial_snoc]
    exact Graph.toSimpleGraphSubgraph_congr (d.graphAfter_snoc_zero ear) _ _
  · refine (Graph.EarStart.heq_toSimpleGraph_of_heq
      (d.graphAfter_snoc_zero ear) (d.heq_start_snoc ear)).trans ?_
    rw [SimpleGraph.EarDecomposition.start_copy, SimpleGraph.EarDecomposition.start_snoc]
    exact (eqRec_heq _ _).symm
  · have hi : Fin.cast (d.length_snoc ear).symm (Fin.cast hlen i) = i := Fin.ext rfl
    calc
      (d.snoc ear).toSimpleGraph.walkAt i =
          (d.toSimpleGraph.snoc ear.toSimpleGraph).walkAt (Fin.cast hlen i) := by
        rw [← hi]
        exact walkAt_toSimpleGraph_snoc d ear (Fin.cast hlen i)
      _ = ((d.toSimpleGraph.snoc ear.toSimpleGraph).copy
            (ear.toSimpleGraphSubgraph_add (d.snoc ear).final_le).symm).walkAt (Fin.cast hlen i) :=
        ((d.toSimpleGraph.snoc ear.toSimpleGraph).walkAt_copy
          (ear.toSimpleGraphSubgraph_add (d.snoc ear).final_le).symm (Fin.cast hlen i)).symm

/-- Transporting an ear decomposition to `SimpleGraph` commutes with taking prefixes. -/
@[simp]
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.length + 1)) :
    (d.prefix i).toSimpleGraph = d.toSimpleGraph.prefix i := by
  let i' : Fin (d.toSimpleGraph.length + 1) := i
  have hlen : (d.prefix i).toSimpleGraph.length = (d.toSimpleGraph.prefix i').length :=
    d.length_prefix i
  have hzero : (d.prefix i).graphAfter 0 = d.graphAfter 0 := by
    rw [← Graph.EarDecomposition.initial_eq_graphAfter, d.initial_prefix i,
      Graph.EarDecomposition.initial_eq_graphAfter]
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ (fun j ↦ ?_)
  · exact ((d.prefix i).initial_toSimpleGraph).trans
      ((Graph.toSimpleGraphSubgraph_congr hzero _ _).trans
        (d.initial_toSimpleGraph.symm.trans (d.toSimpleGraph.initial_prefix i').symm))
  · exact Graph.EarStart.heq_toSimpleGraph_of_heq hzero (d.heq_start_prefix i)
  · have hwalk : ∀ k : Fin i.val,
        (d.prefix i).toSimpleGraph.walkAt (Fin.cast (d.length_prefix i).symm k) =
          (d.toSimpleGraph.prefix i').walkAt k := fun k ↦ by
      calc
        (d.prefix i).toSimpleGraph.walkAt (Fin.cast (d.length_prefix i).symm k) =
            d.toSimpleGraph.walkAt (k.castLE i.is_le) :=
          ((d.prefix i).walkAt_toSimpleGraph (Fin.cast (d.length_prefix i).symm k)).trans <| by
            rw [Graph.EarDecomposition.walkAt_eq, d.earAt_prefix i k,
              ← Graph.EarDecomposition.walkAt_eq]
            exact (d.walkAt_toSimpleGraph (k.castLE i.is_le)).symm
        _ = (d.toSimpleGraph.prefix i').walkAt k :=
          (d.toSimpleGraph.walkAt_prefix i' k).symm
    have hj : Fin.cast (d.length_prefix i).symm (Fin.cast hlen j) = j := Fin.ext rfl
    rw [← hj]
    exact hwalk (Fin.cast hlen j)

end Graph.EarDecomposition

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Transport an ear decomposition of a simple subgraph `H : G.Subgraph` to an ear decomposition of
`H.toGraph` in `Graph.ofSimpleGraph G`, retaining every prefix subgraph and displayed ear. -/
@[expose]
def toGraph (d : G.EarDecomposition H) : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  length := d.length
  graphAfter i := (d.subgraphAfter i).toGraph
  start := d.start.toGraph
  earAt i := ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by
    rw [d.subgraphAfter_succ i, (d.earAt i).add_toGraph]
  graphAfter_last := congrArg Subgraph.toGraph d.subgraphAfter_last

@[simp]
theorem length_toGraph (d : G.EarDecomposition H) : d.toGraph.length = d.length := (rfl)

@[simp]
theorem graphAfter_toGraph (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toGraph.graphAfter i = (d.subgraphAfter i).toGraph := (rfl)

@[simp]
theorem graphAfter_toGraph_zero (d : G.EarDecomposition H) :
    d.toGraph.graphAfter 0 = d.initial.toGraph :=
  congrArg Subgraph.toGraph d.subgraphAfter_zero

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph :=
  d.toGraph.initial_eq_graphAfter.trans d.graphAfter_toGraph_zero

/-- The transported multigraph decomposition retains the transported initial-stage witness. -/
@[simp]
theorem start_toGraph (d : G.EarDecomposition H) : d.toGraph.start = d.start.toGraph := (rfl)

/-- The transported multigraph decomposition displays the transported ear over each prefix graph. -/
@[simp]
theorem earAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.earAt i = ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩ := (rfl)

theorem kindAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.kindAt i = (d.kindAt i).toGraph := by
  let i' : Fin d.toGraph.length := i
  exact (d.toGraph.kindAt_eq i').trans
    ((d.earAt i).kind_toGraph.trans (congrArg EarKind.toGraph (d.kindAt_def i).symm))

theorem walkAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.walkAt i = ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toGraph⟩ := by
  let i' : Fin d.toGraph.length := i
  refine (d.toGraph.walkAt_eq i').trans ((d.earAt i).toWalk_toGraph.trans ?_)
  rw [← d.walkAt_def i]

/-- Transport to `Graph.ofSimpleGraph G` preserves the open-ear-decomposition predicate. -/
@[simp]
theorem isOpen_toGraph (d : G.EarDecomposition H) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff]
  refine and_congr d.start.isCycle_toGraph ?_
  exact forall_congr' fun i : Fin d.length ↦ by rw [d.kindAt_toGraph i]; simp

/-- The transported multigraph decomposition is vertex-started if and only if the simple-graph
decomposition does not start from a cycle. -/
@[simp]
theorem isVertexStart_toGraph_iff_not_isCycle (d : G.EarDecomposition H) :
    d.toGraph.IsVertexStart ↔ ¬ d.start.IsCycle :=
  d.toGraph.isVertexStart_iff_not_start_isCycle.trans (not_congr d.start.isCycle_toGraph)

/-- The transported multigraph decomposition is vertex-started if and only if the initial simple
subgraph is a singleton subgraph. -/
theorem isVertexStart_toGraph_iff (d : G.EarDecomposition H) :
    d.toGraph.IsVertexStart ↔ ∃ v : V, d.initial = G.singletonSubgraph v := by
  rw [Graph.EarDecomposition.isVertexStart_iff, initial_toGraph]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.1, SimpleGraph.Subgraph.toGraph_inj.mp
      (hv.trans (SimpleGraph.Subgraph.toGraph_singletonSubgraph v.1).symm)⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, by simp⟩,
      (congrArg Subgraph.toGraph hv).trans (SimpleGraph.Subgraph.toGraph_singletonSubgraph v)⟩

@[simp]
theorem toGraph_vertex (v : V) :
    (SimpleGraph.EarDecomposition.vertex G v).toGraph =
      (Graph.EarDecomposition.vertex ⟨v, by simp⟩).copy
        (SimpleGraph.Subgraph.toGraph_singletonSubgraph v).symm := by
  refine Graph.EarDecomposition.ext_of_walkAt (by simp) ?_ ?_
    (fun i ↦ Fin.elim0 (Fin.cast (by simp) i))
  · simp
  · have hstart :
        HEq (SimpleGraph.EarDecomposition.vertex G v).start
          (SimpleGraph.EarStart.vertex (G := G) v) := by
      rw [SimpleGraph.EarDecomposition.start_vertex]
      exact eqRec_heq _ _
    exact (SimpleGraph.EarStart.heq_toGraph_of_heq
      (SimpleGraph.EarDecomposition.subgraphAfter_vertex (G := G) v 0) hstart).trans
      ((SimpleGraph.EarStart.heq_toGraph_vertex v).trans
        ((Graph.EarDecomposition.heq_start_vertex ⟨v, by simp⟩).symm.trans
          (Graph.EarDecomposition.heq_start_copy _ _).symm))

@[simp]
theorem toGraph_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    (SimpleGraph.EarDecomposition.cycle c hc).toGraph =
      (Graph.EarDecomposition.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)).copy
        (SimpleGraph.Walk.toGraph_toSubgraph c).symm := by
  refine Graph.EarDecomposition.ext_of_walkAt (by simp) ?_ ?_
    (fun i ↦ Fin.elim0 (Fin.cast (by simp) i))
  · simp
  · have hstart :
        HEq (SimpleGraph.EarDecomposition.cycle c hc).start (SimpleGraph.EarStart.cycle c hc) := by
      rw [SimpleGraph.EarDecomposition.start_cycle]
      exact eqRec_heq _ _
    exact (SimpleGraph.EarStart.heq_toGraph_of_heq
      (SimpleGraph.EarDecomposition.subgraphAfter_cycle c hc 0) hstart).trans
      ((SimpleGraph.EarStart.heq_toGraph_cycle c hc).trans
        ((Graph.EarDecomposition.heq_start_cycle c.toGraph _).symm.trans
          (Graph.EarDecomposition.heq_start_copy _ _).symm))

@[simp]
theorem toGraph_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  subst h
  rw [d.copy_rfl, d.toGraph.copy_rfl]

private theorem walkAt_toGraph_snoc (d : G.EarDecomposition H) (e : G.Ear H)
    (hlen : (d.snoc e).toGraph.length =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).length)
    (j : Fin (d.length + 1)) :
    (d.snoc e).toGraph.walkAt j =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).walkAt (Fin.cast hlen j) := by
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · have hlast :
        Fin.cast ((d.toGraph.snoc e.toGraph).length_copy e.add_toGraph)
          (Fin.cast hlen (Fin.last d.length)) =
        Fin.cast (d.toGraph.length_snoc e.toGraph).symm (Fin.last d.toGraph.length) :=
      Fin.ext rfl
    calc
      (d.snoc e).toGraph.walkAt (Fin.last d.length) =
          ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
        rw [(d.snoc e).walkAt_toGraph (Fin.last d.length), d.walkAt_snoc_last e]
      _ = e.toGraph.toWalk := (e.toWalk_toGraph).symm
      _ = (d.toGraph.snoc e.toGraph).walkAt
            (Fin.cast (d.toGraph.length_snoc e.toGraph).symm (Fin.last d.toGraph.length)) := by
        rw [Graph.EarDecomposition.walkAt_eq, d.toGraph.earAt_snoc_last e.toGraph]
      _ = ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).walkAt
            (Fin.cast hlen (Fin.last d.length)) := by
        rw [Graph.EarDecomposition.walkAt_copy, hlast]
  · have hcast :
        Fin.cast ((d.toGraph.snoc e.toGraph).length_copy e.add_toGraph)
          (Fin.cast hlen k.castSucc) =
        Fin.cast (d.toGraph.length_snoc e.toGraph).symm
          (Fin.cast d.length_toGraph.symm k).castSucc :=
      Fin.ext rfl
    calc
      (d.snoc e).toGraph.walkAt k.castSucc =
          ⟨(d.walkAt k).1, (d.walkAt k).2.1, (d.walkAt k).2.2.toGraph⟩ := by
        rw [(d.snoc e).walkAt_toGraph k.castSucc, d.walkAt_snoc_castSucc e k]
      _ = d.toGraph.walkAt (Fin.cast d.length_toGraph.symm k) :=
        (d.walkAt_toGraph k).symm
      _ = (d.toGraph.snoc e.toGraph).walkAt
            (Fin.cast (d.toGraph.length_snoc e.toGraph).symm
              (Fin.cast d.length_toGraph.symm k).castSucc) := by
        rw [Graph.EarDecomposition.walkAt_eq, Graph.EarDecomposition.walkAt_eq,
          d.toGraph.earAt_snoc_castSucc e.toGraph]
      _ = ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).walkAt
            (Fin.cast hlen k.castSucc) := by
        rw [Graph.EarDecomposition.walkAt_copy, hcast]

@[simp]
theorem toGraph_snoc (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).toGraph = (d.toGraph.snoc e.toGraph).copy e.add_toGraph := by
  have hlen : (d.snoc e).toGraph.length =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).length := by simp
  refine Graph.EarDecomposition.ext_of_walkAt hlen (by simp) ?_
    (fun i ↦ walkAt_toGraph_snoc d e hlen i)
  have hstart : HEq (d.snoc e).start d.start := by
    rw [d.start_snoc e]
    exact eqRec_heq _ _
  exact (SimpleGraph.EarStart.heq_toGraph_of_heq
    (by simp only [subgraphAfter_zero, initial_snoc]) hstart).trans
    ((d.toGraph.heq_start_snoc e.toGraph).symm.trans
      ((d.toGraph.snoc e.toGraph).heq_start_copy e.add_toGraph).symm)

/-- Transporting a simple-graph ear decomposition to `Graph.ofSimpleGraph G` commutes with taking
prefixes. -/
@[simp]
theorem toGraph_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k := by
  let k' : Fin (d.toGraph.length + 1) := k
  have hlen : (d.prefix k).toGraph.length = (d.toGraph.prefix k').length :=
    (d.toGraph.length_prefix k').symm
  refine Graph.EarDecomposition.ext_of_walkAt hlen ?_ ?_ (fun j ↦ ?_)
  · exact (initial_toGraph (d.prefix k)).trans
      ((congrArg Subgraph.toGraph (d.initial_prefix k)).trans
        (d.initial_toGraph.symm.trans (d.toGraph.initial_prefix k').symm))
  · exact (d.toGraph.heq_start_prefix k').symm
  · let j₀ : Fin k.val := j
    have hj : Fin.cast hlen j = Fin.cast (d.toGraph.length_prefix k').symm j₀ :=
      Fin.ext rfl
    calc
      (d.prefix k).toGraph.walkAt j =
          ⟨(d.walkAt (j₀.castLE k.is_le)).1,
            (d.walkAt (j₀.castLE k.is_le)).2.1,
            (d.walkAt (j₀.castLE k.is_le)).2.2.toGraph⟩ := by
        rw [(d.prefix k).walkAt_toGraph j₀, d.walkAt_prefix k j₀]
      _ = d.toGraph.walkAt (Fin.castLE (Nat.le_of_lt_succ k'.isLt) j₀) :=
        (d.walkAt_toGraph (j₀.castLE k.is_le)).symm
      _ = ((d.toGraph.prefix k').earAt
            (Fin.cast (d.toGraph.length_prefix k').symm j₀)).2.toWalk := by
        rw [d.toGraph.earAt_prefix k' j₀, ← d.toGraph.walkAt_eq]
      _ = (d.toGraph.prefix k').walkAt (Fin.cast hlen j) := by
        rw [hj, Graph.EarDecomposition.walkAt_eq]

/-- Transporting a simple-graph ear decomposition to `Graph.ofSimpleGraph G` and back recovers the
original decomposition up to canonical `copy` reindexing. -/
@[simp]
theorem toSimpleGraph_toGraph (d : G.EarDecomposition H) :
    d.toGraph.toSimpleGraph =
      d.copy (H.toSimpleGraphSubgraph_toGraph d.toGraph.final_le).symm := by
  refine ext rfl (by simp) d.start.heq_toSimpleGraph_toGraph (fun i ↦ ?_)
  let i₀ : Fin d.length := i
  calc
    d.toGraph.toSimpleGraph.walkAt i =
        ⟨(d.toGraph.walkAt i₀).1, (d.toGraph.walkAt i₀).2.1,
          (d.toGraph.walkAt i₀).2.2.toSimpleGraph⟩ :=
      d.toGraph.walkAt_toSimpleGraph i₀
    _ = d.walkAt i₀ := by
      rw [d.walkAt_toGraph i₀, SimpleGraph.Walk.toSimpleGraph_toGraph]
    _ = (d.copy (H.toSimpleGraphSubgraph_toGraph d.toGraph.final_le).symm).walkAt
          (Fin.cast rfl i) :=
      (d.walkAt_copy _ i₀).symm

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transporting an ear decomposition of `K ≤ Graph.ofSimpleGraph G` to `G` and back recovers the
original decomposition up to canonical `copy` reindexing. -/
@[simp]
theorem toGraph_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.toGraph = d.copy (K.toGraph_toSimpleGraphSubgraph d.final_le).symm := by
  have hlen : d.toSimpleGraph.toGraph.length =
      (d.copy (K.toGraph_toSimpleGraphSubgraph d.final_le).symm).length :=
    (d.length_copy _).symm
  refine ext_of_walkAt hlen (by simp) ?_ (fun i ↦ ?_)
  · exact d.start.heq_toGraph_toSimpleGraph.trans (d.heq_start_copy _).symm
  · let i₀ : Fin d.length := i
    calc
      d.toSimpleGraph.toGraph.walkAt i =
          ⟨(d.toSimpleGraph.walkAt i₀).1, (d.toSimpleGraph.walkAt i₀).2.1,
            (d.toSimpleGraph.walkAt i₀).2.2.toGraph⟩ :=
        d.toSimpleGraph.walkAt_toGraph i₀
      _ = d.walkAt i₀ := by
        rw [d.walkAt_toSimpleGraph i₀, Graph.Walk.toGraph_toSimpleGraph]
      _ = (d.copy (K.toGraph_toSimpleGraphSubgraph d.final_le).symm).walkAt (Fin.cast hlen i) := by
        rw [d.walkAt_copy]
        rfl

end Graph.EarDecomposition

namespace SimpleGraph.Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-- Ear decompositions of `H : G.Subgraph` are canonically equivalent to ear decompositions of
`H.toGraph` in `Graph.ofSimpleGraph G`. -/
def earDecompositionEquivOfSimpleGraph (H : G.Subgraph) :
    G.EarDecomposition H ≃ (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  toFun := SimpleGraph.EarDecomposition.toGraph
  invFun d := d.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph d.final_le)
  left_inv d := by simp
  right_inv d := by simp

@[simp]
theorem earDecompositionEquivOfSimpleGraph_apply (H : G.Subgraph) (d : G.EarDecomposition H) :
    H.earDecompositionEquivOfSimpleGraph d = d.toGraph := (rfl)

@[simp]
theorem earDecompositionEquivOfSimpleGraph_symm_apply (H : G.Subgraph)
    (d : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph) :
    H.earDecompositionEquivOfSimpleGraph.symm d =
      d.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph d.final_le) := (rfl)

end SimpleGraph.Subgraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Ear decompositions of `K ≤ Graph.ofSimpleGraph G` are canonically equivalent to ear
decompositions of `K.toSimpleGraphSubgraph hK`. -/
def earDecompositionEquivSimpleGraph (hK : K ≤ Graph.ofSimpleGraph G) :
    (Graph.ofSimpleGraph G).EarDecomposition K ≃
      G.EarDecomposition (K.toSimpleGraphSubgraph hK) where
  toFun d := d.toSimpleGraph.copy (toSimpleGraphSubgraph_congr rfl d.final_le hK)
  invFun d := d.toGraph.copy (K.toGraph_toSimpleGraphSubgraph hK)
  left_inv d := by simp
  right_inv d := by simp

@[simp]
theorem earDecompositionEquivSimpleGraph_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    earDecompositionEquivSimpleGraph hK d =
      d.toSimpleGraph.copy (toSimpleGraphSubgraph_congr rfl d.final_le hK) := (rfl)

@[simp]
theorem earDecompositionEquivSimpleGraph_symm_apply (hK : K ≤ Graph.ofSimpleGraph G)
    (d : G.EarDecomposition (K.toSimpleGraphSubgraph hK)) :
    (earDecompositionEquivSimpleGraph hK).symm d =
      d.toGraph.copy (K.toGraph_toSimpleGraphSubgraph hK) := (rfl)

end Graph

namespace SimpleGraph

variable {V : Type u}

/-- Ear decompositions of the whole simple graph `⊤ : G.Subgraph` are canonically equivalent to
ear decompositions of `Graph.ofSimpleGraph G`. -/
def earDecompositionEquivOfSimpleGraph (G : SimpleGraph V) :
    G.EarDecomposition (⊤ : G.Subgraph) ≃
      (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G) where
  toFun d := d.toGraph.copy Subgraph.toGraph_top
  invFun d := d.toSimpleGraph.copy (Graph.toSimpleGraphSubgraph_ofSimpleGraph d.final_le)
  left_inv d := by simp
  right_inv d := by simp

@[simp]
theorem earDecompositionEquivOfSimpleGraph_apply (G : SimpleGraph V)
    (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    G.earDecompositionEquivOfSimpleGraph d = d.toGraph.copy Subgraph.toGraph_top := (rfl)

@[simp]
theorem earDecompositionEquivOfSimpleGraph_symm_apply (G : SimpleGraph V)
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    G.earDecompositionEquivOfSimpleGraph.symm d =
      d.toSimpleGraph.copy (Graph.toSimpleGraphSubgraph_ofSimpleGraph d.final_le) := (rfl)

end SimpleGraph
