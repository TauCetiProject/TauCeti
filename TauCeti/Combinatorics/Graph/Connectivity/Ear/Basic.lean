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
@[expose] def toGraph (e : G.Ear H) : Graph α β :=
  G.walkGraph e.toWalk.2.2

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
@[expose] def add (e : G.Ear H) : Graph α β :=
  e.compatible.union

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

/-- Every edge traversed by an ear belongs to the edge set obtained by adjoining the ear. -/
theorem mem_edgeSet_add_of_mem_edges (e : G.Ear H) {f : β} (hf : f ∈ e.toWalk.2.2.edges) :
    f ∈ E(e.add) :=
  e.toGraph_le_add.edgeSet_mono ((e.toWalk.2.2.mem_edgeSet_walkGraph f).mpr hf)

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

/-- Adjoining any ear over an edgeless single-vertex base produces the ear's traced graph. -/
@[simp]
theorem add_noEdge_singleton {s : α} (e : G.Ear (Graph.noEdge {s} β)) :
    e.add = e.toGraph := by
  refine (Compatible.of_le_le e.add_le e.toGraph_le).ext ?_ (by simp)
  have hs : e.toWalk.1 = s := by simpa using e.start_mem_base
  ext x
  simp only [vertexSet_add, vertexSet_noEdge, vertexSet_toGraph, mem_union, mem_singleton_iff, ← hs,
    or_iff_right_iff_imp]
  rintro rfl
  exact Walk.start_mem_support _

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

/-- Any cycle based at `s` forms a closed ear over the edgeless single-vertex subgraph
`Graph.noEdge {s} β`. -/
def ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    G.Ear (Graph.noEdge {s} β) :=
  have hle : G.walkGraph walk ≤ G := walk.walkGraph_le_of_pos <|
    Nat.pos_of_ne_zero fun h ↦ isCycle.not_nil (Walk.length_eq_zero_iff.mp h)
  have hs : s ∈ V(G) := hle.vertexSet_mono (by simp [Walk.start_mem_support])
  .closed (Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr hs)) walk isCycle (by simp)
    (fun _ _ hxs ↦ by simp [hxs]) (fun _ _ ↦ by simp)

@[simp]
theorem kind_ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (Ear.ofIsCycle walk isCycle).kind = .closed := by
  rw [ofIsCycle, kind_closed]

@[simp]
theorem toWalk_ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (Ear.ofIsCycle walk isCycle).toWalk = ⟨s, s, walk⟩ := by
  rw [ofIsCycle, toWalk_closed]

@[simp]
theorem toGraph_ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (Ear.ofIsCycle walk isCycle).toGraph = G.walkGraph walk := by
  rw [toGraph, toWalk_ofIsCycle]

/-- Adjoining the closed ear of a cycle to its base vertex traces that cycle. -/
theorem add_ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (Ear.ofIsCycle walk isCycle).add = G.walkGraph walk := by
  simp

/-- Any ambient link outside `E(H)` whose endpoints both lie in `V(H)` yields an ear of `G` over
`H`: a closed loop ear when the endpoints coincide, and a single-link open ear otherwise. -/
theorem nonempty_of_isLink (hHG : H ≤ G) {f : β} {s t : α} (hl : G.IsLink f s t)
    (hs : s ∈ V(H)) (ht : t ∈ V(H)) (hf : f ∉ E(H)) : Nonempty (G.Ear H) := by
  by_cases hst : s = t
  · subst hst
    exact ⟨ofIsLoopAt hHG (isLink_self_iff.mp hl) hs hf⟩
  · exact ⟨ofIsLink hHG hl hs ht hst hf⟩

/-- If an ambient link `e₀` steps from `x ∈ V(H)` to `y ∉ V(H)` and `y` can reach some vertex of
`H` in `G.deleteEdges {e₀}`, then `e₀` followed by a first-return path to `V(H)` in
`G.deleteEdges {e₀}` forms an ear of `G` over `H`. -/
theorem nonempty_of_isLink_reachable_deleteEdges (hHG : H ≤ G) {e₀ : β} {x y z : α}
    (hl : G.IsLink e₀ x y) (hxH : x ∈ V(H)) (hyH : y ∉ V(H)) (hzH : z ∈ V(H))
    (hreach : (G.deleteEdges {e₀}).Reachable y z) : Nonempty (G.Ear H) := by
  have he₀H : e₀ ∉ E(H) := fun he₀ ↦ hyH (((hHG.isLink_iff he₀).mpr hl).right_mem)
  -- Extract a path in `G - {e₀}` from `y` to `z` and truncate at its first hit in `H`.
  obtain ⟨p₀, hp₀⟩ := hreach.exists_isPath
  let p : G.Walk y z := p₀.mapLe deleteEdges_le
  have hp : p.IsPath := (Walk.isPath_mapLe deleteEdges_le p₀).mpr hp₀
  have he₀p : e₀ ∉ p.edges := by
    intro hm
    rw [Walk.edges_mapLe_eq_edges] at hm
    have hm' := p₀.edges_subset_edgeSet hm
    simp at hm'
  classical
  obtain ⟨t, htH, htp, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq (S := V(H)) ⟨z, p.end_mem_support, hzH⟩
  let q : G.Walk y t := p.takeUntil t htp
  have hq : q.IsPath := hp.takeUntil htp
  -- No edge of the prefix `q` can lie in `E(H)`, since its starting endpoint precedes `t` on `q`.
  have hq_edges_notMem : ∀ f ∈ q.edges, f ∉ E(H) := by
    intro f hfq hfH
    obtain ⟨a, _, hfab, haq, -, hat, -⟩ := hq.exists_isLink_mem_support_ne hfq
    exact hat (hfirst a (((hHG.isLink_iff hfH).mpr hfab).left_mem) haq)
  have hcons_edges : ∀ f ∈ (Walk.cons e₀ hl q).edges, f ∉ E(H) := by
    intro f hf
    rw [Walk.edges_cons, List.mem_cons] at hf
    rcases hf with rfl | hfq
    · exact he₀H
    · exact hq_edges_notMem f hfq
  -- Returning to `x` closes a cycle ear; returning to `t ≠ x` gives an open path ear.
  by_cases hxt : x = t
  · subst hxt
    have he₀q : e₀ ∉ q.edges := fun hqe₀ ↦ he₀p (p.edges_takeUntil_subset_edges htp hqe₀)
    have hcyc : (Walk.cons e₀ hl q).IsCycle :=
      (Walk.cons_isCycle_iff e₀ hl q).mpr ⟨hq, he₀q⟩
    refine ⟨.closed hHG (Walk.cons e₀ hl q) hcyc hxH (fun w hw hwx hwH ↦ ?_) hcons_edges⟩
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hwq
    · exact hwx rfl
    · exact hwx (hfirst w hwH hwq)
  · have hxq : x ∉ q.support := fun hxq ↦ hxt (hfirst x hxH hxq)
    have hpath : (Walk.cons e₀ hl q).IsPath :=
      (Walk.isPath_cons e₀ hl q).mpr ⟨hq, hxq⟩
    refine ⟨.open hHG (Walk.cons e₀ hl q) hpath hxH htH hxt
      (fun w hw hwx hwt hwH ↦ ?_) hcons_edges⟩
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hwq
    · exact hwx rfl
    · exact hwt (hfirst w hwH hwq)

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
@[expose] def IsCycle : G.EarStart H → Prop
  | .vertex _ => False
  | .cycle _ _ => True

instance instDecidableIsCycle : ∀ start : G.EarStart H, Decidable start.IsCycle
  | .vertex _ => isFalse not_false
  | .cycle _ _ => isTrue trivial

@[simp]
theorem isCycle_vertex (v : V(G)) : (EarStart.vertex v).IsCycle ↔ False :=
  Iff.rfl

@[simp]
theorem isCycle_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).IsCycle ↔ True :=
  Iff.rfl

private theorem isCycle_transport {K L : Graph α β} (h : K = L) (start : G.EarStart K) :
    (h ▸ start).IsCycle ↔ start.IsCycle := by
  subst h; rfl

private theorem heq_transport {K L : Graph α β} (h : K = L) (start : G.EarStart K) :
    HEq (h ▸ start) start := by
  subst h; rfl

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
      (Fin.cast (length_snoc d ear).symm 0).castSucc := Fin.ext (by simp)
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
      Fin.cast (congrArg (· + 1) (length_prefix d i).symm) 0 := Fin.ext (by simp)
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

private theorem set_graphAfter_eq_union_biUnion {γ : Type*} (d : G.EarDecomposition H)
    (f : Graph α β → Set γ)
    (hadd : ∀ {K : Graph α β} (e : G.Ear K), f e.add = f K ∪ f e.toGraph)
    (i : Fin (d.length + 1)) :
    f (d.graphAfter i) =
      f d.initial ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), f (d.earAt j).2.toGraph := by
  induction i using Fin.induction with
  | zero =>
      simp
  | succ k ih =>
      rw [d.graphAfter_succ, hadd, congrArg f (d.earAt_fst k), ih]
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

/-- The actual vertices of the `i`-th stage graph are those of the initial graph together with
those traced by the preceding ears. -/
theorem vertexSet_graphAfter_eq_union_biUnion (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    V(d.graphAfter i) =
      V(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), V((d.earAt j).2.toGraph) :=
  d.set_graphAfter_eq_union_biUnion vertexSet (fun e ↦ e.vertexSet_add) i

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
      E(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), E((d.earAt j).2.toGraph) :=
  d.set_graphAfter_eq_union_biUnion edgeSet (fun e ↦ e.edgeSet_add) i

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

private def replaceInitialGraphAfter (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (k : Fin (d₀.length + d.length + 1)) : Graph α β :=
  if hk : k.val ≤ d₀.length then
    d₀.graphAfter ⟨k.val, Nat.lt_succ_of_le hk⟩
  else
    d.graphAfter ⟨k.val - d₀.length, by omega⟩

private theorem replaceInitialGraphAfter_left (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d₀.length + 1)) :
    replaceInitialGraphAfter d d₀ ⟨i.val, by omega⟩ = d₀.graphAfter i := by
  simp [replaceInitialGraphAfter, Nat.le_of_lt_succ i.isLt]

private theorem replaceInitialGraphAfter_right (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    replaceInitialGraphAfter d d₀ ⟨d₀.length + i.val, by omega⟩ = d.graphAfter i := by
  simp only [replaceInitialGraphAfter]
  split_ifs with hk
  · obtain rfl : i = 0 := Fin.ext (by simpa using hk)
    have hlast : (⟨d₀.length + (0 : Fin (d.length + 1)).val, Nat.lt_succ_of_le hk⟩ :
        Fin (d₀.length + 1)) = Fin.last d₀.length := Fin.ext (by simp)
    rw [hlast, d₀.graphAfter_last, d.initial_eq_graphAfter]
  · exact congrArg d.graphAfter (Fin.ext (by simp))

/-- Replay the ears of `d` on top of an ear decomposition of its initial graph. -/
def replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    G.EarDecomposition H where
  length := d₀.length + d.length
  graphAfter := replaceInitialGraphAfter d d₀
  start := (replaceInitialGraphAfter_left d d₀ 0).symm ▸ d₀.start
  earAt := Fin.addCases d₀.earAt d.earAt
  earAt_fst k := by
    refine k.addCases (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [Fin.addCases_left, d₀.earAt_fst i]
      have hk : (Fin.castAdd d.length i).castSucc =
          (⟨i.castSucc.val, by omega⟩ : Fin (d₀.length + d.length + 1)) := Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_left]
    · rw [Fin.addCases_right, d.earAt_fst i]
      have hk : (Fin.natAdd d₀.length i).castSucc =
          (⟨d₀.length + i.castSucc.val, by omega⟩ : Fin (d₀.length + d.length + 1)) :=
        Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_right]
  graphAfter_succ k := by
    refine k.addCases (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [Fin.addCases_left, ← d₀.graphAfter_succ i]
      have hk : (Fin.castAdd d.length i).succ =
          (⟨i.succ.val, by omega⟩ : Fin (d₀.length + d.length + 1)) := Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_left]
    · rw [Fin.addCases_right, ← d.graphAfter_succ i]
      have hk : (Fin.natAdd d₀.length i).succ =
          (⟨d₀.length + i.succ.val, by omega⟩ : Fin (d₀.length + d.length + 1)) :=
        Fin.ext (by simp [Nat.add_assoc])
      rw [hk, replaceInitialGraphAfter_right]
  graphAfter_last := by
    have hlast : Fin.last (d₀.length + d.length) =
        (⟨d₀.length + (Fin.last d.length).val, by omega⟩ : Fin (d₀.length + d.length + 1)) :=
      Fin.ext (by simp)
    rw [hlast, replaceInitialGraphAfter_right, d.graphAfter_last]

@[simp]
theorem length_replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).length = d₀.length + d.length := (rfl)

/-- Replacing the initial stage retains every stage graph of `d₀`. -/
@[simp]
theorem graphAfter_replaceInitial_castLE (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d₀.length + 1)) :
    (d.replaceInitial d₀).graphAfter
      (Fin.castLE (Nat.succ_le_succ ((Nat.le_add_right d₀.length d.length).trans_eq
        (d.length_replaceInitial d₀).symm)) i) = d₀.graphAfter i :=
  replaceInitialGraphAfter_left d d₀ i

/-- Replacing the initial stage shifts every stage graph of `d` by `d₀.length`. -/
@[simp]
theorem graphAfter_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    (d.replaceInitial d₀).graphAfter
      (Fin.cast ((Nat.add_assoc d₀.length d.length 1).symm.trans
        (congrArg (· + 1) (d.length_replaceInitial d₀).symm)) (Fin.natAdd d₀.length i)) =
      d.graphAfter i :=
  replaceInitialGraphAfter_right d d₀ i

/-- Replacing the initial stage sets the initial graph to that of `d₀`. -/
theorem initial_replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).initial = d₀.initial := by
  have h0 : (0 : Fin ((d.replaceInitial d₀).length + 1)) =
      Fin.castLE (Nat.succ_le_succ ((Nat.le_add_right d₀.length d.length).trans_eq
        (d.length_replaceInitial d₀).symm)) 0 := Fin.ext (by simp)
  rw [initial_eq_graphAfter, h0, graphAfter_replaceInitial_castLE, ← initial_eq_graphAfter]

private theorem heq_start_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    HEq (d.replaceInitial d₀).start d₀.start :=
  EarStart.heq_transport (replaceInitialGraphAfter_left d d₀ 0).symm d₀.start

@[simp]
theorem start_isCycle_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle :=
  EarStart.isCycle_transport (replaceInitialGraphAfter_left d d₀ 0).symm d₀.start

/-- Replacing the initial stage retains every ear of `d₀` in the prefix positions. -/
@[simp]
theorem earAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) =
      d₀.earAt i := by
  change Fin.addCases d₀.earAt d.earAt (Fin.cast rfl (Fin.castAdd d.length i)) = d₀.earAt i
  rw [Fin.cast_eq_self, Fin.addCases_left]

/-- Replacing the initial stage shifts every ear of `d` by `d₀.length`. -/
@[simp]
theorem earAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) =
      d.earAt i := by
  change Fin.addCases d₀.earAt d.earAt (Fin.cast rfl (Fin.natAdd d₀.length i)) = d.earAt i
  rw [Fin.cast_eq_self, Fin.addCases_right]

/-- Replacing the initial stage retains the kind of every ear of `d₀`. -/
theorem kindAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) =
      d₀.kindAt i := by
  rw [kindAt_eq, earAt_replaceInitial_castAdd, ← kindAt_eq]

/-- Replacing the initial stage retains the kind of every shifted ear of `d`. -/
theorem kindAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) =
      d.kindAt i := by
  rw [kindAt_eq, earAt_replaceInitial_natAdd, ← kindAt_eq]

/-- Replacing the initial stage retains the walk of every ear of `d₀`. -/
theorem walkAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) =
      d₀.walkAt i := by
  rw [walkAt_eq, earAt_replaceInitial_castAdd, ← walkAt_eq]

/-- Replacing the initial stage retains the walk of every shifted ear of `d`. -/
theorem walkAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) =
      d.walkAt i := by
  rw [walkAt_eq, earAt_replaceInitial_natAdd, ← walkAt_eq]

/-- Replacing the initial stage yields an open ear decomposition exactly when `d₀` is open and
every ear of `d` is open. -/
@[simp]
theorem isOpen_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsOpen ↔ d₀.IsOpen ∧ ∀ i, d.kindAt i = .open := by
  rw [isOpen_iff, isOpen_iff, start_isCycle_replaceInitial, and_assoc]
  refine and_congr_right fun _ ↦ ⟨fun hk ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun ⟨hk₀, hk⟩ j ↦ ?_⟩
  · simpa only [kindAt_replaceInitial_castAdd] using
      hk (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i))
  · simpa only [kindAt_replaceInitial_natAdd] using
      hk (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i))
  · have hall : ∀ k : Fin (d₀.length + d.length),
        (d.replaceInitial d₀).kindAt (Fin.cast (d.length_replaceInitial d₀).symm k) = .open :=
      fun k ↦ k.addCases
        (fun i ↦ (d.kindAt_replaceInitial_castAdd d₀ i).trans (hk₀ i))
        (fun i ↦ (d.kindAt_replaceInitial_natAdd d₀ i).trans (hk i))
    simpa using hall (Fin.cast (d.length_replaceInitial d₀) j)

end EarDecomposition

namespace EarStart

variable {G H : Graph α β}

/-- Regard any allowed initial graph as an ear decomposition starting from a single vertex: a
cycle start becomes a single-vertex start followed by one closed ear. -/
def toVertexDecomposition : G.EarStart H → G.EarDecomposition H
  | .vertex v => .vertex v
  | .cycle (s := s) walk isCycle =>
      have hs : s ∈ V(G) :=
        (Ear.ofIsCycle walk isCycle).toGraph_le.vertexSet_mono
          (by simp [Walk.start_mem_support])
      ((EarDecomposition.vertex ⟨s, hs⟩).snoc (Ear.ofIsCycle walk isCycle)).copy
        (Ear.add_ofIsCycle walk isCycle)

@[simp]
theorem toVertexDecomposition_vertex (v : V(G)) :
    (EarStart.vertex v).toVertexDecomposition = .vertex v := (rfl)

/-- A cycle start normalizes to a length-`1` vertex-started decomposition, whereas a vertex start
has length `0`. -/
theorem length_toVertexDecomposition (start : G.EarStart H) :
    start.toVertexDecomposition.length = if start.IsCycle then 1 else 0 := by
  cases start <;> rfl

@[simp]
theorem length_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.length = 1 := (rfl)

/-- Normalizing a cycle start sets the initial graph to its base vertex without edges. -/
theorem initial_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.initial = Graph.noEdge {s} β := by
  unfold toVertexDecomposition
  rw [EarDecomposition.initial_copy, EarDecomposition.initial_snoc,
    EarDecomposition.initial_vertex]

/-- The single ear of the normalized decomposition of a cycle start is `Ear.ofIsCycle`. -/
@[simp]
theorem earAt_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.earAt
      (Fin.cast (length_toVertexDecomposition_cycle walk isCycle).symm 0) =
      ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  change Fin.lastCases (⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ : Σ K, G.Ear K) Fin.elim0
    (Fin.last 0) = (⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ : Σ K, G.Ear K)
  exact Fin.lastCases_last

@[simp]
theorem not_start_isCycle_toVertexDecomposition (start : G.EarStart H) :
    ¬ start.toVertexDecomposition.start.IsCycle := by
  cases start with
  | vertex v => exact EarDecomposition.not_start_isCycle_vertex v
  | cycle walk isCycle =>
      unfold toVertexDecomposition
      rw [EarDecomposition.start_isCycle_copy, EarDecomposition.start_isCycle_snoc]
      exact EarDecomposition.not_start_isCycle_vertex _

private theorem toVertexDecomposition_of_not_isCycle {K : Graph α β} (start : G.EarStart K)
    (h : ¬ start.IsCycle) :
    start.toVertexDecomposition.length = 0 ∧
      start.toVertexDecomposition.initial = K ∧
      HEq start.toVertexDecomposition.start start := by
  cases start with
  | vertex v => exact ⟨rfl, rfl, HEq.rfl⟩
  | cycle _ _ => exact False.elim (h trivial)

/-- Every cycle-started `EarStart` is given by an underlying cycle in `G`. -/
theorem exists_cycle_of_isCycle {K : Graph α β} {start : G.EarStart K} (h : start.IsCycle) :
    ∃ (s : α) (walk : G.Walk s s) (isCycle : walk.IsCycle),
      K = G.walkGraph walk ∧ HEq start (EarStart.cycle walk isCycle) := by
  cases start with
  | vertex _ => exact False.elim h
  | cycle walk isCycle => exact ⟨_, walk, isCycle, rfl, HEq.rfl⟩

end EarStart

namespace EarDecomposition

variable {G H : Graph α β}

private theorem heq_fun_fin {n m : ℕ} {X : Sort*} {f : Fin n → X} {g : Fin m → X} (h : n = m)
    (hfg : ∀ j : Fin m, f (Fin.cast h.symm j) = g j) : HEq f g := by
  subst h; exact heq_of_eq (funext hfg)

/-- Normalize any ear decomposition so that it starts from a single vertex, turning an initial
cycle into a first closed ear. -/
def toVertexStart (d : G.EarDecomposition H) : G.EarDecomposition H :=
  d.replaceInitial (d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm)

@[simp]
theorem not_start_isCycle_toVertexStart (d : G.EarDecomposition H) :
    ¬ d.toVertexStart.start.IsCycle := by
  rw [toVertexStart, start_isCycle_replaceInitial, start_isCycle_copy]
  exact d.start.not_start_isCycle_toVertexDecomposition

/-- Normalizing to a vertex start adds one ear when `d` starts at a cycle and keeps the length
unchanged otherwise. -/
theorem length_toVertexStart (d : G.EarDecomposition H) :
    d.toVertexStart.length = (if d.start.IsCycle then 1 else 0) + d.length := by
  rw [toVertexStart, length_replaceInitial, length_copy, d.start.length_toVertexDecomposition]

/-- Normalizing a vertex-started decomposition preserves its length. -/
theorem length_toVertexStart_of_not_isCycle {d : G.EarDecomposition H} (h : ¬ d.start.IsCycle) :
    d.toVertexStart.length = d.length := by
  simp [d.length_toVertexStart, h]

/-- Normalizing a cycle-started decomposition increases its length by one. -/
theorem length_toVertexStart_of_isCycle {d : G.EarDecomposition H} (h : d.start.IsCycle) :
    d.toVertexStart.length = 1 + d.length := by
  simp [d.length_toVertexStart, h]

/-- The initial graph of `d.toVertexStart` is the single-vertex base of `d.start`. -/
theorem initial_toVertexStart (d : G.EarDecomposition H) :
    d.toVertexStart.initial = d.start.toVertexDecomposition.initial := by
  rw [toVertexStart, initial_replaceInitial, initial_copy]

/-- Normalizing a decomposition that already starts from a single vertex leaves it unchanged. -/
theorem toVertexStart_eq_self {d : G.EarDecomposition H} (h : ¬ d.start.IsCycle) :
    d.toVertexStart = d := by
  obtain ⟨hlen₀, _, hstart₀⟩ := EarStart.toVertexDecomposition_of_not_isCycle d.start h
  have hlen : d.toVertexStart.length = d.length := d.length_toVertexStart_of_not_isCycle h
  let d₀ := d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm
  refine ext d.toVertexStart d hlen
    (heq_fun_fin (congrArg (· + 1) hlen) fun i ↦ ?_)
    ((d.heq_start_replaceInitial d₀).trans hstart₀)
    (heq_fun_fin hlen fun i ↦ ?_)
  · change (d.replaceInitial d₀).graphAfter _ = d.graphAfter i
    have hi : Fin.cast (congrArg (· + 1) hlen.symm) i =
        Fin.cast ((Nat.add_assoc d₀.length d.length 1).symm.trans
          (congrArg (· + 1) (d.length_replaceInitial d₀).symm))
          (Fin.natAdd d₀.length i) := Fin.ext (by simp [d₀, hlen₀])
    rw [hi]
    exact d.graphAfter_replaceInitial_natAdd d₀ i
  · change (d.replaceInitial d₀).earAt _ = d.earAt i
    have hi : Fin.cast hlen.symm i =
        Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i) :=
      Fin.ext (by simp [d₀, hlen₀])
    rw [hi]
    exact d.earAt_replaceInitial_natAdd d₀ i

/-- Every original stage graph of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem graphAfter_toVertexStart_natAdd (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toVertexStart.graphAfter
      (Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
        (congrArg (· + 1) d.length_toVertexStart.symm))
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) = d.graphAfter i := by
  let d₀ := d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm
  change (d.replaceInitial d₀).graphAfter _ = d.graphAfter i
  have hi : Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
        (congrArg (· + 1) d.length_toVertexStart.symm))
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i) =
      Fin.cast ((Nat.add_assoc d₀.length d.length 1).symm.trans
        (congrArg (· + 1) (d.length_replaceInitial d₀).symm))
        (Fin.natAdd d₀.length i) :=
    Fin.ext (by simp [d₀, d.start.length_toVertexDecomposition])
  rw [hi]
  exact d.graphAfter_replaceInitial_natAdd d₀ i

/-- Every original ear of `d` appears at the corresponding shifted index in `d.toVertexStart`. -/
theorem earAt_toVertexStart_natAdd (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toVertexStart.earAt
      (Fin.cast d.length_toVertexStart.symm
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) = d.earAt i := by
  let d₀ := d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm
  change (d.replaceInitial d₀).earAt _ = d.earAt i
  have hi : Fin.cast d.length_toVertexStart.symm
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i) =
      Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i) :=
    Fin.ext (by simp [d₀, d.start.length_toVertexDecomposition])
  rw [hi]
  exact d.earAt_replaceInitial_natAdd d₀ i

private theorem toVertexDecomposition_of_heq_cycle {K : Graph α β} (start : G.EarStart K)
    {s : α} {walk : G.Walk s s} {isCycle : walk.IsCycle}
    (hK : K = G.walkGraph walk) (hstart : HEq start (EarStart.cycle walk isCycle)) :
    start.toVertexDecomposition.initial = Graph.noEdge {s} β ∧
      ∃ hlen : start.toVertexDecomposition.length = 1,
        start.toVertexDecomposition.earAt (Fin.cast hlen.symm 0) =
          ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  subst hK
  cases eq_of_heq hstart
  exact ⟨EarStart.initial_toVertexDecomposition_cycle walk isCycle, rfl,
    EarStart.earAt_toVertexDecomposition_cycle walk isCycle⟩

/-- When `d` starts from a cycle, `d.toVertexStart` starts at the cycle's base vertex and its first
ear is the closed ear formed by that initial cycle. -/
theorem exists_cycle_earAt_toVertexStart_zero {d : G.EarDecomposition H} (h : d.start.IsCycle) :
    ∃ (s : α) (walk : G.Walk s s) (isCycle : walk.IsCycle),
      d.initial = G.walkGraph walk ∧
      d.toVertexStart.initial = Graph.noEdge {s} β ∧
      d.toVertexStart.earAt
        (Fin.cast (d.length_toVertexStart_of_isCycle h).symm (Fin.castAdd d.length 0)) =
        ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  obtain ⟨s, walk, isCycle, hK, hheq⟩ := EarStart.exists_cycle_of_isCycle h
  obtain ⟨hinit₀, hlen₀, hear₀⟩ := toVertexDecomposition_of_heq_cycle d.start hK hheq
  let d₀ := d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm
  refine ⟨s, walk, isCycle, d.initial_eq_graphAfter.trans hK,
    d.initial_toVertexStart.trans hinit₀, ?_⟩
  change (d.replaceInitial d₀).earAt _ = _
  have hd₀ : d₀.length = 1 := hlen₀
  have hi : Fin.cast (d.length_toVertexStart_of_isCycle h).symm (Fin.castAdd d.length 0) =
      Fin.cast (d.length_replaceInitial d₀).symm
        (Fin.castAdd d.length (Fin.cast hd₀.symm 0)) := Fin.ext (by simp)
  rw [hi, d.earAt_replaceInitial_castAdd d₀]
  exact hear₀

/-- Normalizing a single-cycle decomposition sets its initial graph to the cycle's base vertex. -/
theorem initial_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).toVertexStart.initial = Graph.noEdge {s} β := by
  rw [initial_toVertexStart]
  exact EarStart.initial_toVertexDecomposition_cycle walk isCycle

@[simp]
theorem length_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).toVertexStart.length = 1 := by
  simp [length_toVertexStart]

/-- Normalizing a single-cycle decomposition yields `Ear.ofIsCycle` as its unique ear. -/
@[simp]
theorem earAt_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).toVertexStart.earAt
      (Fin.cast (length_toVertexStart_cycle walk isCycle).symm 0) =
      ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  let d₀ := (cycle walk isCycle).start.toVertexDecomposition.copy
    (cycle walk isCycle).initial_eq_graphAfter.symm
  have hd₀ : d₀.length = 1 := rfl
  change ((cycle walk isCycle).replaceInitial d₀).earAt _ = _
  have hi : Fin.cast (length_toVertexStart_cycle walk isCycle).symm (0 : Fin 1) =
      Fin.cast ((cycle walk isCycle).length_replaceInitial d₀).symm
        (Fin.castAdd (cycle walk isCycle).length (Fin.cast hd₀.symm 0)) := Fin.ext (by simp)
  rw [hi, (cycle walk isCycle).earAt_replaceInitial_castAdd d₀]
  exact EarStart.earAt_toVertexDecomposition_cycle walk isCycle

end EarDecomposition

/-- A subgraph admits an ear decomposition if and only if it admits one starting from a single
vertex. -/
theorem nonempty_earDecomposition_iff_exists_not_isCycle {G H : Graph α β} :
    Nonempty (G.EarDecomposition H) ↔ ∃ d : G.EarDecomposition H, ¬ d.start.IsCycle :=
  ⟨fun ⟨d⟩ ↦ ⟨d.toVertexStart, d.not_start_isCycle_toVertexStart⟩, fun ⟨d, _⟩ ↦ ⟨d⟩⟩

end Graph
