/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Order.Fin.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Trace

import TauCeti.Data.Fin.Basic

/-!
# Ear decompositions of multigraphs

This file defines open and closed ears in an edge-labelled multigraph and packages a finite ear
decomposition as construction data.  A decomposition starts from one actual vertex or from a
cycle, then adds ears whose internal vertices and edge identities are new.  Loops and parallel
edges are retained: a loop can be a one-edge closed ear, and two parallel edges can form a
two-edge closed ear.

The prefix interface exposes the graph after every initial segment, the ear added at every step,
and a decomposition of each prefix, together with vertex and edge coverage, pairwise edge
disjointness of the added ears, and normalization of cycle-started decompositions to
vertex-started ones.  It is intended as the common data layer for ear characterizations of edge
connectivity and for constructing strong orientations.

The definitions follow the ear-decomposition conventions of R. Diestel, *Graph Theory*,
Chapter 3, adapted to multigraphs by retaining edge identities.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} (G : Graph α β)

/-- The two kinds of ears added during an ear decomposition. -/
inductive EarKind
  | open
  | closed
  deriving DecidableEq

/-- An ear of `G` relative to a subgraph `H`.

An open ear is a positive path with distinct endpoints in `H`, internal vertices outside `H`,
and edge identities outside `H`.  A closed ear is a cycle meeting `H` only at its base vertex
and using no edge of `H`. -/
inductive Ear (H : Graph α β) : Type (max u v)
  | open (hHG : H ≤ G) {s t : α} (walk : G.Walk s t) (isPath : walk.IsPath)
      (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
      (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
      (edges_new : ∀ e ∈ walk.edges, e ∉ E(H))
  | closed (hHG : H ≤ G) {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle)
      (base_mem : s ∈ V(H))
      (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
      (edges_new : ∀ e ∈ walk.edges, e ∉ E(H))

namespace Ear

variable {G : Graph α β} {H : Graph α β}

/-- Whether an ear is open or closed. -/
def kind : G.Ear H → EarKind
  | .open .. => .open
  | .closed .. => .closed

@[simp]
theorem kind_open {s t : α} (hHG : H ≤ G) (walk : G.Walk s t) (isPath : walk.IsPath)
    (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.open hHG walk isPath start_mem end_mem endpoints_ne internal_new edges_new).kind =
      .open := by
  rw [kind]

@[simp]
theorem kind_closed {s : α} (hHG : H ≤ G) (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (base_mem : s ∈ V(H)) (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.closed hHG walk isCycle base_mem internal_new edges_new).kind = .closed := by
  rw [kind]

/-- The underlying walk of an ear, including its endpoints. -/
def toWalk : G.Ear H → Σ s t : α, G.Walk s t
  | .open _ walk .. => ⟨_, _, walk⟩
  | .closed _ walk .. => ⟨_, _, walk⟩

@[simp]
theorem toWalk_open {s t : α} (hHG : H ≤ G) (walk : G.Walk s t) (isPath : walk.IsPath)
    (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.open hHG walk isPath start_mem end_mem endpoints_ne internal_new edges_new).toWalk =
      ⟨s, t, walk⟩ := by
  rw [toWalk]

@[simp]
theorem toWalk_closed {s : α} (hHG : H ≤ G) (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (base_mem : s ∈ V(H)) (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.closed hHG walk isCycle base_mem internal_new edges_new).toWalk = ⟨s, s, walk⟩ := by
  rw [toWalk]

@[simp]
theorem support_toWalk_open {s t : α} (hHG : H ≤ G) (walk : G.Walk s t) (isPath : walk.IsPath)
    (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.open hHG walk isPath start_mem end_mem endpoints_ne internal_new
      edges_new).toWalk.2.2.support = walk.support := by
  rw [toWalk_open]

@[simp]
theorem edges_toWalk_open {s t : α} (hHG : H ≤ G) (walk : G.Walk s t) (isPath : walk.IsPath)
    (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.open hHG walk isPath start_mem end_mem endpoints_ne internal_new
      edges_new).toWalk.2.2.edges = walk.edges := by
  rw [toWalk_open]

@[simp]
theorem support_toWalk_closed {s : α} (hHG : H ≤ G) (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (base_mem : s ∈ V(H)) (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.closed hHG walk isCycle base_mem internal_new edges_new).toWalk.2.2.support =
      walk.support := by
  rw [toWalk_closed]

@[simp]
theorem edges_toWalk_closed {s : α} (hHG : H ≤ G) (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (base_mem : s ∈ V(H)) (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.closed hHG walk isCycle base_mem internal_new edges_new).toWalk.2.2.edges =
      walk.edges := by
  rw [toWalk_closed]

/-- Ears are equal when they have the same kind and the same endpoint-indexed walk. -/
@[ext]
theorem ext (e f : G.Ear H) (hkind : e.kind = f.kind) (hwalk : e.toWalk = f.toWalk) :
    e = f := by
  cases e <;> cases f <;> simp only [kind, toWalk] at hkind hwalk
  · cases hwalk
    rfl
  · contradiction
  · contradiction
  · cases hwalk
    rfl

/-- The graph traced by an ear. -/
def toGraph (e : G.Ear H) : Graph α β :=
  G.walkGraph e.toWalk.2.2

theorem toGraph_eq (e : G.Ear H) : e.toGraph = G.walkGraph e.toWalk.2.2 :=
  (rfl)

@[simp]
theorem vertexSet_toGraph (e : G.Ear H) :
    V(e.toGraph) = {x | x ∈ e.toWalk.2.2.support} :=
  e.toWalk.2.2.vertexSet_walkGraph

@[simp]
theorem edgeSet_toGraph (e : G.Ear H) :
    E(e.toGraph) = {f | f ∈ e.toWalk.2.2.edges} :=
  e.toWalk.2.2.edgeSet_walkGraph

/-- The base of an ear is a subgraph of its ambient graph. -/
theorem base_le : ∀ _e : G.Ear H, H ≤ G
  | .open hHG .. => hHG
  | .closed hHG .. => hHG

/-- The underlying walk of an ear has positive length. -/
theorem length_pos : ∀ e : G.Ear H, 0 < e.toWalk.2.2.length
  | .open _ walk _ _ _ endpoints_ne _ _ =>
      Nat.pos_of_ne_zero fun h ↦ endpoints_ne (walk.eq_of_length_eq_zero h)
  | .closed _ _walk isCycle _ _ _ =>
      Nat.pos_of_ne_zero fun h ↦ isCycle.not_nil ((Walk.length_eq_zero_iff.mp h))

/-- The graph traced by an ear is a subgraph of its ambient graph. -/
theorem toGraph_le (e : G.Ear H) : e.toGraph ≤ G :=
  e.toWalk.2.2.walkGraph_le_of_pos e.length_pos

/-- The base and traced graph of an ear are compatible subgraphs of the ambient graph. -/
theorem compatible (e : G.Ear H) : H.Compatible e.toGraph :=
  .of_le_le e.base_le e.toGraph_le

/-- The graph obtained by adjoining an ear to its base. -/
def add (e : G.Ear H) : Graph α β :=
  e.compatible.union

theorem add_eq (e : G.Ear H) : e.add = e.compatible.union :=
  (rfl)

@[simp]
theorem vertexSet_add (e : G.Ear H) : V(e.add) = V(H) ∪ V(e.toGraph) :=
  e.compatible.vertexSet_union

@[simp]
theorem edgeSet_add (e : G.Ear H) : E(e.add) = E(H) ∪ E(e.toGraph) :=
  e.compatible.edgeSet_union

/-- Adjoining an ear is the least graph containing its base and traced graph. -/
@[simp]
theorem add_le_iff (e : G.Ear H) {K : Graph α β} :
    e.add ≤ K ↔ H ≤ K ∧ e.toGraph ≤ K :=
  e.compatible.union_le_iff

/-- The base is a subgraph of the result of adjoining an ear. -/
theorem base_le_add (e : G.Ear H) : H ≤ e.add :=
  e.compatible.left_le_union

/-- The graph traced by an ear is a subgraph of the result of adjoining it. -/
theorem toGraph_le_add (e : G.Ear H) : e.toGraph ≤ e.add :=
  e.compatible.right_le_union

/-- Adjoining an ear still gives a subgraph of the ambient graph. -/
theorem add_le (e : G.Ear H) : e.add ≤ G :=
  IsSubgraph.union_le e.base_le e.toGraph_le

/-- Every edge of an ear is absent from its base graph. -/
theorem edge_notMem_base (e : G.Ear H) {f : β} (hf : f ∈ e.toWalk.2.2.edges) :
    f ∉ E(H) := by
  cases e with
  | «open» _ _ _ _ _ _ _ edges_new => exact edges_new f hf
  | «closed» _ _ _ _ _ edges_new => exact edges_new f hf

/-- An open ear has distinct endpoints. -/
theorem endpoints_ne (e : G.Ear H) (he : e.kind = .open) : e.toWalk.1 ≠ e.toWalk.2.1 := by
  cases e with
  | «open» _ _ _ _ _ hst _ _ => exact hst
  | «closed» => exact EarKind.noConfusion he

/-- The starting vertex of an ear lies in its base graph. -/
theorem start_mem_base : ∀ e : G.Ear H, e.toWalk.1 ∈ V(H)
  | .open _ _ _ hs _ _ _ _ => hs
  | .closed _ _ _ hs _ _ => hs

/-- The ending vertex of an ear lies in its base graph. -/
theorem end_mem_base : ∀ e : G.Ear H, e.toWalk.2.1 ∈ V(H)
  | .open _ _ _ _ ht _ _ _ => ht
  | .closed _ _ _ hs _ _ => hs

/-- The base graph of an ear has at least one actual vertex. -/
theorem base_nonempty (e : G.Ear H) : V(H).Nonempty :=
  ⟨e.toWalk.1, e.start_mem_base⟩

/-- The underlying walk of any ear is a trail. -/
theorem isTrail : ∀ e : G.Ear H, e.toWalk.2.2.IsTrail
  | .open _ _ hp _ _ _ _ _ => hp.isTrail
  | .closed _ _ hc _ _ _ => hc.isTrail

/-- The edge set traced by an ear is disjoint from the edge set of its base graph. -/
theorem disjoint_edgeSet_toGraph (e : G.Ear H) : Disjoint E(H) E(e.toGraph) :=
  Set.disjoint_right.mpr fun f hf ↦
    e.edge_notMem_base ((e.toWalk.2.2.mem_edgeSet_walkGraph f).mp hf)

/-- An ear traces at least one edge. -/
theorem edgeSet_toGraph_nonempty (e : G.Ear H) : E(e.toGraph).Nonempty := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil e.toWalk.2.2.edges <|
    by intro h; have hlen := e.length_pos; simp [← Walk.length_edges, h] at hlen
  exact ⟨f, (e.toWalk.2.2.mem_edgeSet_walkGraph f).mpr hf⟩

/-- Adjoining an ear strictly enlarges the edge set. -/
theorem edgeSet_ssubset_add (e : G.Ear H) : E(H) ⊂ E(e.add) := by
  obtain ⟨f, hf⟩ := e.edgeSet_toGraph_nonempty
  exact ssubset_iff_exists.mpr
    ⟨subset_union_left.trans_eq e.edgeSet_add.symm, f,
      e.edgeSet_add.symm ▸ Or.inr hf,
      e.edge_notMem_base ((e.toWalk.2.2.mem_edgeSet_walkGraph f).mp hf)⟩

/-- Adjoining an ear strictly enlarges the base graph. -/
theorem base_lt_add (e : G.Ear H) : H < e.add :=
  lt_of_le_of_ne e.base_le_add fun h ↦ e.edgeSet_ssubset_add.ne (congrArg edgeSet h)

/-- Adjoining an ear strictly shrinks the set of remaining ambient edges. -/
theorem sdiff_edgeSet_add_ssubset (e : G.Ear H) :
    E(G) \ E(e.add) ⊂ E(G) \ E(H) := by
  obtain ⟨f, hf⟩ := e.edgeSet_toGraph_nonempty
  refine ssubset_iff_exists.mpr
    ⟨fun g hg ↦ ⟨hg.1, fun hgH ↦ hg.2 (e.base_le_add.edgeSet_mono hgH)⟩, f, ?_, ?_⟩
  · exact ⟨e.toGraph_le.edgeSet_mono hf,
      e.edge_notMem_base ((e.toWalk.2.2.mem_edgeSet_walkGraph f).mp hf)⟩
  · intro hmem
    exact hmem.2 (e.edgeSet_add.symm ▸ Or.inr hf)

/-- A single unused link between distinct vertices of `H` forms an open ear. -/
def ofIsLink {f : β} {s t : α} (hHG : H ≤ G) (h : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hst : s ≠ t) (hf : f ∉ E(H)) : G.Ear H :=
  .open hHG h.toWalk (h.isPath_toWalk_iff.mpr hst) hs ht hst
    (fun x hx hxs hxt ↦ by
      rw [IsLink.support_toWalk] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      exact hx.elim (fun h ↦ absurd h hxs) (fun h ↦ absurd h hxt))
    (fun g hg ↦ by
      rw [IsLink.edges_toWalk, List.mem_singleton] at hg
      exact hg ▸ hf)

@[simp]
theorem kind_ofIsLink {f : β} {s t : α} (hHG : H ≤ G) (h : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hst : s ≠ t) (hf : f ∉ E(H)) :
    (ofIsLink hHG h hs ht hst hf).kind = .open := by
  rw [ofIsLink, kind_open]

@[simp]
theorem toWalk_ofIsLink {f : β} {s t : α} (hHG : H ≤ G) (h : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hst : s ≠ t) (hf : f ∉ E(H)) :
    (ofIsLink hHG h hs ht hst hf).toWalk = ⟨s, t, h.toWalk⟩ := by
  rw [ofIsLink, toWalk_open]

@[simp]
theorem support_toWalk_ofIsLink {f : β} {s t : α} (hHG : H ≤ G) (h : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hst : s ≠ t) (hf : f ∉ E(H)) :
    (ofIsLink hHG h hs ht hst hf).toWalk.2.2.support = [s, t] := by
  rw [toWalk_ofIsLink, h.support_toWalk]

@[simp]
theorem edges_toWalk_ofIsLink {f : β} {s t : α} (hHG : H ≤ G) (h : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hst : s ≠ t) (hf : f ∉ E(H)) :
    (ofIsLink hHG h hs ht hst hf).toWalk.2.2.edges = [f] := by
  rw [toWalk_ofIsLink, h.edges_toWalk]

/-- A single unused loop at a vertex of `H` forms a closed ear. -/
def ofIsLoopAt {f : β} {s : α} (hHG : H ≤ G) (h : G.IsLoopAt f s)
    (hs : s ∈ V(H)) (hf : f ∉ E(H)) : G.Ear H :=
  let hl : G.IsLink f s s := isLink_self_iff.mpr h
  .closed hHG hl.toWalk hl.isCycle_toWalk hs
    (fun x hx hxs ↦ by
      rw [IsLink.support_toWalk] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      exact absurd hx hxs)
    (fun g hg ↦ by
      rw [IsLink.edges_toWalk, List.mem_singleton] at hg
      exact hg ▸ hf)

@[simp]
theorem kind_ofIsLoopAt {f : β} {s : α} (hHG : H ≤ G) (h : G.IsLoopAt f s)
    (hs : s ∈ V(H)) (hf : f ∉ E(H)) :
    (ofIsLoopAt hHG h hs hf).kind = .closed := by
  rw [ofIsLoopAt, kind_closed]

@[simp]
theorem toWalk_ofIsLoopAt {f : β} {s : α} (hHG : H ≤ G) (h : G.IsLoopAt f s)
    (hs : s ∈ V(H)) (hf : f ∉ E(H)) :
    (ofIsLoopAt hHG h hs hf).toWalk = ⟨s, s, (isLink_self_iff.mpr h).toWalk⟩ := by
  rw [ofIsLoopAt, toWalk_closed]

@[simp]
theorem support_toWalk_ofIsLoopAt {f : β} {s : α} (hHG : H ≤ G) (h : G.IsLoopAt f s)
    (hs : s ∈ V(H)) (hf : f ∉ E(H)) :
    (ofIsLoopAt hHG h hs hf).toWalk.2.2.support = [s, s] := by
  rw [toWalk_ofIsLoopAt, IsLink.support_toWalk]

@[simp]
theorem edges_toWalk_ofIsLoopAt {f : β} {s : α} (hHG : H ≤ G) (h : G.IsLoopAt f s)
    (hs : s ∈ V(H)) (hf : f ∉ E(H)) :
    (ofIsLoopAt hHG h hs hf).toWalk.2.2.edges = [f] := by
  rw [toWalk_ofIsLoopAt, IsLink.edges_toWalk]

end Ear

/-- The possible initial graphs of an ear decomposition: one actual vertex or the graph traced by
a cycle. -/
inductive EarStart (G : Graph α β) : Graph α β → Type (max u v)
  | vertex (v : V(G)) : G.EarStart (Graph.noEdge {v.1} β)
  | cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
      G.EarStart (G.walkGraph walk)

namespace EarStart

variable {G H : Graph α β}

/-- Whether the initial graph is a cycle rather than a single vertex. -/
def IsCycle : G.EarStart H → Prop
  | .vertex _ => False
  | .cycle _ _ => True

@[simp]
theorem isCycle_vertex (v : V(G)) : (EarStart.vertex v).IsCycle ↔ False :=
  Iff.rfl

@[simp]
theorem isCycle_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).IsCycle ↔ True :=
  Iff.rfl

private theorem isCycle_transport {K L : Graph α β} (h : K = L) (start : G.EarStart K) :
    (h ▸ start).IsCycle ↔ start.IsCycle := by
  subst h
  rfl

/-- Every allowed initial graph is a subgraph of its ambient graph. -/
theorem le : ∀ _start : G.EarStart H, H ≤ G
  | .vertex v => Graph.noEdge_le_iff.mpr (by simp [v.property])
  | .cycle walk isCycle => walk.walkGraph_le_of_pos <|
      Nat.pos_of_ne_zero fun h ↦ isCycle.not_nil (Walk.length_eq_zero_iff.mp h)

/-- Every allowed initial graph has at least one actual vertex. -/
theorem nonempty : ∀ _start : G.EarStart H, V(H).Nonempty
  | .vertex v => ⟨v.1, by simp⟩
  | .cycle (s := s) walk _ => ⟨s, by simp [Walk.vertexSet_walkGraph]⟩

/-- A vertex-started initial graph has no edges. -/
theorem edgeSet_eq_empty_of_not_isCycle : ∀ {start : G.EarStart H}, ¬ start.IsCycle → E(H) = ∅
  | .vertex _, _ => by simp
  | .cycle _ _, h => absurd trivial h

end EarStart

/-- A finite ear decomposition in `G`, indexed by its final graph `H`.

The stage sequence and successor equations determine the construction completely.  In
particular, a term of `G.EarDecomposition G` covers every actual vertex and edge of `G`. -/
structure EarDecomposition (G H : Graph α β) : Type (max u v) where
  /-- The number of ears following the initial graph. -/
  length : ℕ
  /-- The graph after each prefix; zero is the initial graph and the last index is final. -/
  graphAfter : Fin (length + 1) → Graph α β
  /-- The initial graph is one actual vertex or one cycle. -/
  start : G.EarStart (graphAfter 0)
  /-- The base graph and ear added at each step. -/
  earAt : Fin length → Σ K : Graph α β, G.Ear K
  /-- The stored base of each ear is the graph at the preceding stage. -/
  earAt_fst : ∀ i, (earAt i).1 = graphAfter i.castSucc
  /-- A successor stage is obtained by adjoining its displayed ear. -/
  graphAfter_succ : ∀ i, graphAfter i.succ = (earAt i).2.add
  /-- The last stage is the indexed final graph. -/
  graphAfter_last : graphAfter (Fin.last length) = H

attribute [simp] EarDecomposition.graphAfter_last

namespace EarDecomposition

variable {G H : Graph α β}

/-- Ear decompositions are extensional in their stage graphs, initial data, and ears. -/
@[ext]
theorem ext (d e : G.EarDecomposition H) (hlength : d.length = e.length)
    (hgraphAfter : HEq d.graphAfter e.graphAfter) (hstart : HEq d.start e.start)
    (hearAt : HEq d.earAt e.earAt) : d = e := by
  cases d
  cases e
  cases hlength
  cases hgraphAfter
  cases hstart
  cases hearAt
  rfl

/-- The initial graph of a decomposition. -/
def initial (d : G.EarDecomposition H) : Graph α β :=
  d.graphAfter 0

@[simp]
theorem initial_eq_graphAfter (d : G.EarDecomposition H) : d.initial = d.graphAfter 0 :=
  by rw [initial]

/-- The kind of the ear added at a specified step. -/
def kindAt (d : G.EarDecomposition H) (i : Fin d.length) : EarKind :=
  (d.earAt i).2.kind

@[simp]
theorem kindAt_eq (d : G.EarDecomposition H) (i : Fin d.length) :
    d.kindAt i = (d.earAt i).2.kind :=
  by rw [kindAt]

/-- The underlying walk of the ear added at a specified step. -/
def walkAt (d : G.EarDecomposition H) (i : Fin d.length) :
    Σ s t : α, G.Walk s t :=
  (d.earAt i).2.toWalk

@[simp]
theorem walkAt_eq (d : G.EarDecomposition H) (i : Fin d.length) :
    d.walkAt i = (d.earAt i).2.toWalk :=
  by rw [walkAt]

/-- An open ear decomposition starts from a cycle and adds only open ears. -/
def IsOpen (d : G.EarDecomposition H) : Prop :=
  d.start.IsCycle ∧ ∀ i, d.kindAt i = .open

/-- Characterization of an open ear decomposition by its initial data and ear kinds. -/
theorem isOpen_iff (d : G.EarDecomposition H) :
    d.IsOpen ↔ d.start.IsCycle ∧ ∀ i, d.kindAt i = .open :=
  Iff.rfl

/-- An open ear decomposition starts from a cycle. -/
theorem IsOpen.start_isCycle {d : G.EarDecomposition H} (hd : d.IsOpen) :
    d.start.IsCycle :=
  hd.1

/-- Every displayed ear of an open ear decomposition is open. -/
theorem IsOpen.kindAt_eq_open {d : G.EarDecomposition H} (hd : d.IsOpen)
    (i : Fin d.length) : d.kindAt i = .open :=
  hd.2 i

/-- A decomposition consisting only of one actual vertex. -/
def vertex (v : V(G)) : G.EarDecomposition (Graph.noEdge {v.1} β) where
  length := 0
  graphAfter _ := Graph.noEdge {v.1} β
  start := .vertex v
  earAt i := Fin.elim0 i
  earAt_fst i := Fin.elim0 i
  graphAfter_succ i := Fin.elim0 i
  graphAfter_last := rfl

@[simp]
theorem length_vertex (v : V(G)) : (vertex v).length = 0 := (rfl)

/-- The initial graph of a single-vertex decomposition is that vertex without edges. -/
theorem initial_vertex (v : V(G)) : (vertex v).initial = Graph.noEdge {v.1} β := (rfl)

@[simp]
theorem not_start_isCycle_vertex (v : V(G)) : ¬ (vertex v).start.IsCycle :=
  fun h ↦ h

/-- A decomposition consisting only of one cycle. -/
def cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    G.EarDecomposition (G.walkGraph walk) where
  length := 0
  graphAfter _ := G.walkGraph walk
  start := .cycle walk isCycle
  earAt i := Fin.elim0 i
  earAt_fst i := Fin.elim0 i
  graphAfter_succ i := Fin.elim0 i
  graphAfter_last := rfl

@[simp]
theorem length_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).length = 0 := (rfl)

/-- The initial graph of a single-cycle decomposition is the graph traced by that cycle. -/
theorem initial_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).initial = G.walkGraph walk := (rfl)

@[simp]
theorem start_isCycle_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).start.IsCycle :=
  trivial

/-- A decomposition containing just its initial cycle is open. -/
theorem isOpen_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).IsOpen :=
  ⟨trivial, fun i ↦ Fin.elim0 i⟩

/-- Reindex the final graph of an ear decomposition along an equality of graphs. -/
protected def copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    G.EarDecomposition H' where
  length := d.length
  graphAfter := d.graphAfter
  start := d.start
  earAt := d.earAt
  earAt_fst := d.earAt_fst
  graphAfter_succ := d.graphAfter_succ
  graphAfter_last := d.graphAfter_last.trans h

@[simp]
theorem length_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).length = d.length := (rfl)

@[simp]
theorem graphAfter_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin (d.length + 1)) :
    (d.copy h).graphAfter (Fin.cast (congrArg (· + 1) (length_copy d h).symm) i) =
      d.graphAfter i := (rfl)

/-- Reindexing the final graph preserves the initial graph. -/
theorem initial_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).initial = d.initial := (rfl)

@[simp]
theorem start_isCycle_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).start.IsCycle ↔ d.start.IsCycle := Iff.rfl

@[simp]
theorem earAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin d.length) :
    (d.copy h).earAt (Fin.cast (length_copy d h).symm i) = d.earAt i := (rfl)

/-- Reindexing the final graph preserves the kind of each ear. -/
theorem kindAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin d.length) :
    (d.copy h).kindAt (Fin.cast (length_copy d h).symm i) = d.kindAt i := (rfl)

/-- Reindexing the final graph preserves the walk of each ear. -/
theorem walkAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin d.length) :
    (d.copy h).walkAt (Fin.cast (length_copy d h).symm i) = d.walkAt i := (rfl)

@[simp]
theorem isOpen_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).IsOpen ↔ d.IsOpen := Iff.rfl

private theorem snoc_graphAfter_zero (d : G.EarDecomposition H) (ear : G.Ear H) :
    Fin.lastCases ear.add d.graphAfter (0 : Fin (d.length + 2)) = d.graphAfter 0 := by
  rw [← Fin.castSucc_zero, Fin.lastCases_castSucc]

/-- Adjoin one ear at the end of a decomposition. -/
def snoc (d : G.EarDecomposition H) (ear : G.Ear H) : G.EarDecomposition ear.add where
  length := d.length + 1
  graphAfter i := Fin.lastCases ear.add d.graphAfter i
  start := (snoc_graphAfter_zero d ear).symm ▸ d.start
  earAt i := by
    exact Fin.lastCases ⟨H, ear⟩ d.earAt i
  earAt_fst i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using d.graphAfter_last.symm
    · simpa only [Fin.lastCases_castSucc] using d.earAt_fst j
  graphAfter_succ i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_last]
    · rw [Fin.succ_castSucc, Fin.lastCases_castSucc,
        d.graphAfter_succ, Fin.lastCases_castSucc]
  graphAfter_last := Fin.lastCases_last

@[simp]
theorem length_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).length = d.length + 1 := (rfl)

@[simp]
theorem graphAfter_snoc_castSucc (d : G.EarDecomposition H) (ear : G.Ear H)
    (i : Fin (d.length + 1)) :
    (d.snoc ear).graphAfter
      (Fin.cast (length_snoc d ear).symm i).castSucc = d.graphAfter i :=
  by
    -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
    change Fin.lastCases ear.add d.graphAfter (Fin.cast rfl i).castSucc = d.graphAfter i
    rw [Fin.cast_eq_self, Fin.lastCases_castSucc]

/-- Adjoining an ear preserves the initial graph of a decomposition. -/
theorem initial_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).initial = d.initial := by
  have h0 : (0 : Fin ((d.snoc ear).length + 1)) =
      (Fin.cast (length_snoc d ear).symm 0).castSucc := rfl
  rw [initial_eq_graphAfter, h0, graphAfter_snoc_castSucc, ← initial_eq_graphAfter]

@[simp]
theorem earAt_snoc_castSucc (d : G.EarDecomposition H) (ear : G.Ear H)
    (i : Fin d.length) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm i.castSucc) = d.earAt i :=
  by
    -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
    change Fin.lastCases ⟨H, ear⟩ d.earAt (Fin.cast rfl i.castSucc) = d.earAt i
    rw [Fin.cast_eq_self, Fin.lastCases_castSucc]

@[simp]
theorem earAt_snoc_last (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm (Fin.last d.length)) =
      ⟨H, ear⟩ :=
  by
    -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
    change Fin.lastCases (⟨H, ear⟩ : Σ K, G.Ear K) d.earAt
      (Fin.cast rfl (Fin.last d.length)) =
      (⟨H, ear⟩ : Σ K, G.Ear K)
    rw [Fin.cast_eq_self, Fin.lastCases_last]

/-- Adjoining an ear preserves whether the decomposition starts from a cycle. -/
@[simp]
theorem start_isCycle_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).start.IsCycle ↔ d.start.IsCycle := by
  exact EarStart.isCycle_transport (snoc_graphAfter_zero d ear).symm d.start

/-- Adjoining an ear preserves the kind of every earlier ear. -/
theorem kindAt_snoc_castSucc (d : G.EarDecomposition H) (ear : G.Ear H)
    (i : Fin d.length) :
    (d.snoc ear).kindAt (Fin.cast (length_snoc d ear).symm i.castSucc) = d.kindAt i := by
  rw [kindAt_eq, earAt_snoc_castSucc, ← kindAt_eq]

/-- The last ear of `d.snoc ear` has kind `ear.kind`. -/
theorem kindAt_snoc_last (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).kindAt (Fin.cast (length_snoc d ear).symm (Fin.last d.length)) =
      ear.kind := by
  rw [kindAt_eq, earAt_snoc_last]

/-- Adjoining an open ear preserves and reflects openness of a decomposition. -/
@[simp]
theorem isOpen_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).IsOpen ↔ d.IsOpen ∧ ear.kind = .open := by
  rw [isOpen_iff, isOpen_iff, start_isCycle_snoc]
  constructor
  · rintro ⟨hstart, hkinds⟩
    refine ⟨⟨hstart, fun i ↦ ?_⟩, ?_⟩
    · simpa only [kindAt_snoc_castSucc] using
        hkinds (Fin.cast (length_snoc d ear).symm i.castSucc)
    · simpa only [kindAt_snoc_last] using
        hkinds (Fin.cast (length_snoc d ear).symm (Fin.last d.length))
  · rintro ⟨⟨hstart, hkinds⟩, hear⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    have hkind : ∀ j : Fin (d.length + 1),
        (d.snoc ear).kindAt (Fin.cast (length_snoc d ear).symm j) = .open := by
      intro j
      refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · exact kindAt_snoc_last d ear |>.trans hear
      · exact kindAt_snoc_castSucc d ear k |>.trans (hkinds k)
    simpa using hkind (Fin.cast (length_snoc d ear) i)

/-- Every stage of an ear decomposition is a subgraph of the ambient graph. -/
theorem graphAfter_le (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.graphAfter i ≤ G := by
  induction i using Fin.cases with
  | zero => exact d.start.le
  | succ i => rw [d.graphAfter_succ]; exact (d.earAt i).2.add_le

/-- The final graph of an ear decomposition is a subgraph of the ambient graph. -/
theorem final_le (d : G.EarDecomposition H) : H ≤ G := by
  rw [← d.graphAfter_last]
  exact d.graphAfter_le (Fin.last d.length)

/-- The graph at one prefix is a subgraph of the next prefix graph. -/
theorem graphAfter_castSucc_le_succ (d : G.EarDecomposition H) (i : Fin d.length) :
    d.graphAfter i.castSucc ≤ d.graphAfter i.succ := by
  rw [d.graphAfter_succ]
  rw [← d.earAt_fst i]
  exact (d.earAt i).2.base_le_add

/-- Each added ear strictly enlarges the prefix graph. -/
theorem graphAfter_castSucc_lt_succ (d : G.EarDecomposition H) (i : Fin d.length) :
    d.graphAfter i.castSucc < d.graphAfter i.succ := by
  rw [d.graphAfter_succ, ← d.earAt_fst i]
  exact (d.earAt i).2.base_lt_add

/-- The stage graphs of an ear decomposition grow strictly with the step index. -/
theorem strictMono_graphAfter (d : G.EarDecomposition H) : StrictMono d.graphAfter :=
  Fin.strictMono_iff_lt_succ.mpr d.graphAfter_castSucc_lt_succ

/-- The stage graphs of an ear decomposition are monotone in the step index. -/
theorem monotone_graphAfter (d : G.EarDecomposition H) : Monotone d.graphAfter :=
  d.strictMono_graphAfter.monotone

/-- The initial graph is a subgraph of every stage graph. -/
theorem initial_le_graphAfter (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.initial ≤ d.graphAfter i :=
  d.monotone_graphAfter (Fin.zero_le i)

/-- The initial graph is a subgraph of the final graph. -/
theorem initial_le (d : G.EarDecomposition H) : d.initial ≤ H :=
  (d.initial_le_graphAfter (Fin.last d.length)).trans_eq d.graphAfter_last

/-- Every stage graph is a subgraph of the final graph. -/
theorem graphAfter_le_final (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.graphAfter i ≤ H :=
  (d.monotone_graphAfter (Fin.le_last i)).trans_eq d.graphAfter_last

/-- Every stage of an ear decomposition has at least one actual vertex. -/
theorem nonempty_graphAfter (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    V(d.graphAfter i).Nonempty :=
  d.start.nonempty.mono (d.initial_le_graphAfter i).vertexSet_mono

/-- The final graph of an ear decomposition has at least one actual vertex. -/
theorem nonempty (d : G.EarDecomposition H) : V(H).Nonempty := by
  rw [← congrArg vertexSet d.graphAfter_last]
  exact d.nonempty_graphAfter (Fin.last d.length)

/-- The graph traced by the `i`-th ear is contained in the stage immediately following it. -/
theorem toGraph_earAt_le_graphAfter_succ (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.earAt i).2.toGraph ≤ d.graphAfter i.succ := by
  rw [d.graphAfter_succ]
  exact (d.earAt i).2.toGraph_le_add

/-- The graph traced by every ear in a decomposition is contained in the final graph. -/
theorem toGraph_earAt_le (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.earAt i).2.toGraph ≤ H :=
  (d.toGraph_earAt_le_graphAfter_succ i).trans (d.graphAfter_le_final i.succ)

/-- The decomposition formed by the first `i` ears. -/
def «prefix» (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    G.EarDecomposition (d.graphAfter i) where
  length := i.val
  graphAfter j := d.graphAfter (Fin.castLE (Nat.succ_le_iff.mpr i.isLt) j)
  start := (congrArg d.graphAfter (Fin.castLE_zero _)).symm ▸ d.start
  earAt j := d.earAt (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  earAt_fst j := by
    rw [d.earAt_fst, Fin.castSucc_castLE, Fin.castLE_castSucc]
  graphAfter_succ j := by
    rw [Fin.castLE_succ]
    exact d.graphAfter_succ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  graphAfter_last := by
    rw [Fin.castLE_last]

/-- Prefixing preserves whether the decomposition starts from a cycle. -/
@[simp]
theorem start_isCycle_prefix (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    (d.prefix i).start.IsCycle ↔ d.start.IsCycle := by
  exact EarStart.isCycle_transport
    (congrArg d.graphAfter (Fin.castLE_zero _)).symm d.start

/-- Induction over prefix decompositions in construction order. The zero prefix carries the
initial vertex or cycle, and the successor case adds the next displayed ear. -/
theorem prefix_induction (d : G.EarDecomposition H)
    {P : ∀ {K : Graph α β}, G.EarDecomposition K → Prop}
    (initial : P (d.prefix 0))
    (snoc : ∀ i : Fin d.length, P (d.prefix i.castSucc) → P (d.prefix i.succ))
    (i : Fin (d.length + 1)) : P (d.prefix i) := by
  exact Fin.induction initial snoc i

/-- Induction over stage graphs from the initial vertex or cycle through the displayed ears. -/
theorem graphAfter_induction (d : G.EarDecomposition H) {P : Graph α β → Prop}
    (initial : P d.initial)
    (snoc : ∀ i, P (d.graphAfter i.castSucc) → P (d.earAt i).2.add)
    (i : Fin (d.length + 1)) : P (d.graphAfter i) := by
  apply d.prefix_induction (P := fun {K} _ ↦ P K)
  · simpa only [initial_eq_graphAfter] using initial
  · intro j ih
    rw [d.graphAfter_succ]
    exact snoc j ih

/-- A prefix decomposition contains exactly as many ears as its index. -/
@[simp]
theorem length_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.prefix i).length = i := (rfl)

/-- Prefixing retains the original stage graphs up to the chosen index. -/
@[simp]
theorem graphAfter_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin (i.val + 1)) :
    (d.prefix i).graphAfter
      (Fin.cast (congrArg (· + 1) (length_prefix d i).symm) j) =
        d.graphAfter (Fin.castLE (Nat.succ_le_iff.mpr i.isLt) j) := by
  -- Projection reduction exposes the `Fin.castLE` index hidden by the opaque `prefix` body.
  change d.graphAfter _ = d.graphAfter _
  congr 1

/-- Prefixing preserves the initial graph of a decomposition. -/
theorem initial_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.prefix i).initial = d.initial := by
  have h0 : (0 : Fin ((d.prefix i).length + 1)) =
      Fin.cast (congrArg (· + 1) (length_prefix d i).symm) 0 := rfl
  rw [initial_eq_graphAfter, h0, graphAfter_prefix, Fin.castLE_zero, ← initial_eq_graphAfter]

/-- Prefixing retains the original ears before the chosen index. -/
@[simp]
theorem earAt_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin i.val) :
    (d.prefix i).earAt (Fin.cast (length_prefix d i).symm j) =
      d.earAt (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  -- Projection reduction exposes the `Fin.castLE` index hidden by the opaque `prefix` body.
  change d.earAt _ = d.earAt _
  congr 1

/-- Prefixing retains the kind of every ear before the chosen index. -/
theorem kindAt_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin i.val) :
    (d.prefix i).kindAt (Fin.cast (length_prefix d i).symm j) =
      d.kindAt (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [kindAt_eq, earAt_prefix, ← kindAt_eq]

/-- Every prefix of an open ear decomposition is open. -/
theorem IsOpen.prefix {d : G.EarDecomposition H} (hd : d.IsOpen)
    (i : Fin (d.length + 1)) : (d.prefix i).IsOpen := by
  rw [isOpen_iff, start_isCycle_prefix]
  refine ⟨hd.start_isCycle, fun j ↦ ?_⟩
  have hkind : ∀ k : Fin i.val,
      (d.prefix i).kindAt (Fin.cast (length_prefix d i).symm k) = .open := by
    intro k
    exact kindAt_prefix d i k |>.trans (hd.kindAt_eq_open _)
  simpa using hkind (Fin.cast (length_prefix d i) j)

/-! ### Vertex and edge coverage -/

/-- The actual vertices of the `i`-th stage graph are those of the initial graph together with
those traced by the preceding ears. -/
theorem vertexSet_graphAfter_eq_union_biUnion (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    V(d.graphAfter i) =
      V(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), V((d.earAt j).2.toGraph) := by
  induction i using Fin.induction with
  | zero =>
      simp
  | succ k ih =>
      rw [d.graphAfter_succ, Ear.vertexSet_add, congrArg vertexSet (d.earAt_fst k), ih]
      ext x
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ((hx | ⟨j, hj, hxj⟩) | hxk)
        · exact Or.inl hx
        · exact Or.inr ⟨j, hj.trans k.castSucc_lt_succ, hxj⟩
        · exact Or.inr ⟨k, k.castSucc_lt_succ, hxk⟩
      · rintro (hx | ⟨j, hj, hxj⟩)
        · exact Or.inl (Or.inl hx)
        · have hjk : j ≤ k := not_lt.mp fun hkj ↦ hj.not_ge (Fin.succ_le_castSucc_iff.mpr hkj)
          rcases lt_or_eq_of_le hjk with hjk | rfl
          · exact Or.inl (Or.inr ⟨j, Fin.castSucc_lt_castSucc_iff.mpr hjk, hxj⟩)
          · exact Or.inr hxj

/-- An ear decomposition covers every actual vertex of its final graph by its initial graph and
displayed ears. -/
theorem vertexSet_eq_union_iUnion (d : G.EarDecomposition H) :
    V(H) = V(d.initial) ∪ ⋃ j : Fin d.length, V((d.earAt j).2.toGraph) := by
  rw [← congrArg vertexSet d.graphAfter_last, d.vertexSet_graphAfter_eq_union_biUnion]
  simp [Fin.castSucc_lt_last]

/-- The actual edges of the `i`-th stage graph are those of the initial graph together with those
traced by the preceding ears. -/
theorem edgeSet_graphAfter_eq_union_biUnion (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    E(d.graphAfter i) =
      E(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), E((d.earAt j).2.toGraph) := by
  induction i using Fin.induction with
  | zero =>
      simp
  | succ k ih =>
      rw [d.graphAfter_succ, Ear.edgeSet_add, congrArg edgeSet (d.earAt_fst k), ih]
      ext e
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ((he | ⟨j, hj, hej⟩) | hek)
        · exact Or.inl he
        · exact Or.inr ⟨j, hj.trans k.castSucc_lt_succ, hej⟩
        · exact Or.inr ⟨k, k.castSucc_lt_succ, hek⟩
      · rintro (he | ⟨j, hj, hej⟩)
        · exact Or.inl (Or.inl he)
        · have hjk : j ≤ k := not_lt.mp fun hkj ↦ hj.not_ge (Fin.succ_le_castSucc_iff.mpr hkj)
          rcases lt_or_eq_of_le hjk with hjk | rfl
          · exact Or.inl (Or.inr ⟨j, Fin.castSucc_lt_castSucc_iff.mpr hjk, hej⟩)
          · exact Or.inr hej

/-- An ear decomposition covers every actual edge of its final graph by its initial graph and
displayed ears. -/
theorem edgeSet_eq_union_iUnion (d : G.EarDecomposition H) :
    E(H) = E(d.initial) ∪ ⋃ j : Fin d.length, E((d.earAt j).2.toGraph) := by
  rw [← congrArg edgeSet d.graphAfter_last, d.edgeSet_graphAfter_eq_union_biUnion]
  simp [Fin.castSucc_lt_last]

/-- In a vertex-started ear decomposition, the displayed ears cover every actual edge of the final
graph. -/
theorem edgeSet_eq_iUnion_of_not_isCycle {d : G.EarDecomposition H} (h : ¬ d.start.IsCycle) :
    E(H) = ⋃ j : Fin d.length, E((d.earAt j).2.toGraph) := by
  rw [d.edgeSet_eq_union_iUnion, initial_eq_graphAfter, d.start.edgeSet_eq_empty_of_not_isCycle h,
    empty_union]

/-- Every ear of a decomposition is edge-disjoint from the initial graph. -/
theorem disjoint_edgeSet_initial_earAt (d : G.EarDecomposition H) (i : Fin d.length) :
    Disjoint E(d.initial) E((d.earAt i).2.toGraph) :=
  ((d.earAt i).2.disjoint_edgeSet_toGraph).mono_left
    (((d.initial_le_graphAfter i.castSucc).trans_eq (d.earAt_fst i).symm).edgeSet_mono)

/-- Distinct ears of an ear decomposition have disjoint edge sets. -/
theorem pairwise_disjoint_edgeSet_earAt (d : G.EarDecomposition H) :
    Pairwise fun i j : Fin d.length ↦
      Disjoint E((d.earAt i).2.toGraph) E((d.earAt j).2.toGraph) := by
  have hlt : ∀ {i j : Fin d.length}, i < j →
      Disjoint E((d.earAt i).2.toGraph) E((d.earAt j).2.toGraph) := by
    intro i j hij
    have hle : (d.earAt i).2.toGraph ≤ (d.earAt j).1 := by
      rw [d.earAt_fst j]
      exact (d.toGraph_earAt_le_graphAfter_succ i).trans
        (d.monotone_graphAfter (Fin.succ_le_castSucc_iff.mpr hij))
    exact (d.earAt j).2.disjoint_edgeSet_toGraph.mono_left hle.edgeSet_mono
  intro i j hij
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt h
  · exact absurd rfl hij
  · exact (hlt h).symm

/-- In a vertex-started ear decomposition, every actual edge of the final graph is traversed by a
unique displayed ear. -/
theorem existsUnique_mem_edges_walkAt_of_not_isCycle {d : G.EarDecomposition H}
    (h : ¬ d.start.IsCycle) {e : β} (he : e ∈ E(H)) :
    ∃! i : Fin d.length, e ∈ (d.walkAt i).2.2.edges := by
  rw [d.edgeSet_eq_iUnion_of_not_isCycle h, mem_iUnion] at he
  obtain ⟨i, hi⟩ := he
  have hmem : ∀ j : Fin d.length, e ∈ (d.walkAt j).2.2.edges ↔ e ∈ E((d.earAt j).2.toGraph) := by
    intro j
    rw [d.walkAt_eq j, Ear.toGraph, ← Walk.mem_edgeSet_walkGraph]
  refine ⟨i, (hmem i).mpr hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact Set.disjoint_left.mp (d.pairwise_disjoint_edgeSet_earAt hji) ((hmem j).mp hj) hi

/-! ### Replacing the initial stage and normalizing cycle starts -/

private def replaceInitialAux (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    (i : Fin (d.length + 1)) → G.EarDecomposition (d.graphAfter i) :=
  Fin.induction (d₀.copy d.initial_eq_graphAfter) fun i ih ↦
    ((ih.copy (d.earAt_fst i).symm).snoc (d.earAt i).2).copy (d.graphAfter_succ i).symm

private theorem length_replaceInitialAux (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    (d.replaceInitialAux d₀ i).length = d₀.length + i.val := by
  induction i using Fin.induction with
  | zero => simp [replaceInitialAux]
  | succ k ih =>
      unfold replaceInitialAux at ih ⊢
      rw [Fin.induction_succ, length_copy, length_snoc, length_copy, ih, Fin.val_castSucc,
        Fin.val_succ, Nat.add_assoc]

private theorem initial_replaceInitialAux (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    (d.replaceInitialAux d₀ i).initial = d₀.initial := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k ih =>
      unfold replaceInitialAux at ih ⊢
      rw [Fin.induction_succ, initial_copy, initial_snoc, initial_copy, ih]

private theorem start_isCycle_replaceInitialAux (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    (d.replaceInitialAux d₀ i).start.IsCycle ↔ d₀.start.IsCycle := by
  induction i using Fin.induction with
  | zero => exact Iff.rfl
  | succ k ih =>
      unfold replaceInitialAux at ih ⊢
      rw [Fin.induction_succ, start_isCycle_copy, start_isCycle_snoc, start_isCycle_copy, ih]

/-- Replay the ears of `d` on top of an ear decomposition of its initial graph. -/
def replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    G.EarDecomposition H :=
  (d.replaceInitialAux d₀ (Fin.last d.length)).copy d.graphAfter_last

@[simp]
theorem length_replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).length = d₀.length + d.length := by
  rw [replaceInitial, length_copy, length_replaceInitialAux, Fin.val_last]

/-- Replacing the initial stage sets the initial graph to that of `d₀`. -/
theorem initial_replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).initial = d₀.initial := by
  rw [replaceInitial, initial_copy, initial_replaceInitialAux]

@[simp]
theorem start_isCycle_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle := by
  rw [replaceInitial, start_isCycle_copy, start_isCycle_replaceInitialAux]

end EarDecomposition

namespace EarStart

variable {G H : Graph α β}

/-- Regard any allowed initial graph as an ear decomposition starting from a single vertex: a
cycle start becomes a single-vertex start followed by one closed ear. -/
def toVertexDecomposition : G.EarStart H → G.EarDecomposition H
  | .vertex v => .vertex v
  | .cycle (s := s) walk isCycle =>
      have hle : G.walkGraph walk ≤ G := walk.walkGraph_le_of_pos <|
        Nat.pos_of_ne_zero fun h ↦ isCycle.not_nil (Walk.length_eq_zero_iff.mp h)
      have hs : s ∈ V(G) :=
        hle.vertexSet_mono (by simp [Walk.vertexSet_walkGraph, walk.start_mem_support])
      have hs₀ : s ∈ V(Graph.noEdge {s} β) := by simp
      let ear : G.Ear (Graph.noEdge {s} β) :=
        .closed (Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr hs)) walk isCycle hs₀
          (fun _ _ hxs ↦ by simp [hxs]) (fun _ _ ↦ by simp)
      have hw : ear.toWalk = ⟨s, s, walk⟩ := Ear.toWalk_closed _ _ _ _ _ _
      have hadd : ear.add = G.walkGraph walk := by
        refine (Compatible.of_le_le ear.add_le hle).ext ?_ ?_
        · ext x
          rw [Ear.vertexSet_add, vertexSet_noEdge, Ear.vertexSet_toGraph, hw,
            Walk.vertexSet_walkGraph, mem_union, mem_singleton_iff, mem_ofPred_eq]
          exact ⟨fun h ↦ h.elim (fun hx ↦ hx.symm ▸ walk.start_mem_support) id, Or.inr⟩
        · ext e
          rw [Ear.edgeSet_add, edgeSet_noEdge, empty_union, Ear.edgeSet_toGraph, hw,
            Walk.edgeSet_walkGraph]
      ((EarDecomposition.vertex ⟨s, hs⟩).snoc ear).copy hadd

@[simp]
theorem not_start_isCycle_toVertexDecomposition (start : G.EarStart H) :
    ¬ start.toVertexDecomposition.start.IsCycle := by
  cases start with
  | vertex v => exact EarDecomposition.not_start_isCycle_vertex v
  | cycle walk isCycle =>
      unfold toVertexDecomposition
      rw [EarDecomposition.start_isCycle_copy, EarDecomposition.start_isCycle_snoc]
      exact EarDecomposition.not_start_isCycle_vertex _

end EarStart

namespace EarDecomposition

variable {G H : Graph α β}

/-- Normalize any ear decomposition so that it starts from a single vertex, turning an initial
cycle into a first closed ear. -/
def toVertexStart (d : G.EarDecomposition H) : G.EarDecomposition H :=
  d.replaceInitial (d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm)

@[simp]
theorem not_start_isCycle_toVertexStart (d : G.EarDecomposition H) :
    ¬ d.toVertexStart.start.IsCycle := by
  rw [toVertexStart, start_isCycle_replaceInitial, start_isCycle_copy]
  exact d.start.not_start_isCycle_toVertexDecomposition

end EarDecomposition

end Graph
