/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Order.Fin.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Component

import TauCeti.Data.Fin.Basic

/-!
# Ear decompositions of multigraphs

This file defines open and closed ears in an edge-labelled multigraph and packages a finite ear
decomposition as construction data.  A decomposition starts from one actual vertex or from a
cycle, then adds ears whose internal vertices and edge identities are new.  Loops and parallel
edges are retained: a loop can be a one-edge closed ear, and two parallel edges can form a
two-edge closed ear.

The prefix interface exposes the graph after every initial segment, the ear added at every step,
and a decomposition of each prefix, together with connectedness of every stage, the cycles created
by new edges, vertex and edge coverage, and pairwise edge disjointness of the added ears.
Replacing the initial stage and normalizing cycle-started decompositions to vertex-started ones are
developed in `TauCeti.Combinatorics.Graph.Connectivity.Ear.VertexStart`.

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

/-- The starting vertex of an ear belongs to its base graph. -/
theorem toWalk_fst_mem (e : G.Ear H) : e.toWalk.1 ∈ V(H) := by
  cases e with
  | «open» _ _ _ start_mem => exact start_mem
  | «closed» _ _ _ base_mem => exact base_mem

/-- The ending vertex of an ear belongs to its base graph. -/
theorem toWalk_snd_mem (e : G.Ear H) : e.toWalk.2.1 ∈ V(H) := by
  cases e with
  | «open» h walk isPath start_mem end_mem endpoints_ne internal_new edges_new =>
      rw [toWalk_open]
      exact end_mem
  | «closed» h walk isCycle base_mem internal_new edges_new =>
      rw [toWalk_closed]
      exact base_mem

/-- An open ear has distinct endpoints. -/
theorem endpoints_ne (e : G.Ear H) (he : e.kind = .open) : e.toWalk.1 ≠ e.toWalk.2.1 := by
  cases e with
  | «open» _ _ _ _ _ hst _ _ => exact hst
  | «closed» => exact EarKind.noConfusion he

/-- The base graph of an ear has at least one actual vertex. -/
theorem base_vertexSet_nonempty (e : G.Ear H) : V(H).Nonempty :=
  ⟨e.toWalk.1, e.toWalk_fst_mem⟩

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

/-- The graph traced by an ear is connected. -/
theorem connected_toGraph (e : G.Ear H) : e.toGraph.Connected :=
  e.toWalk.2.2.connected_walkGraph

@[simp]
theorem toGraph_open {s t : α} (hHG : H ≤ G) (walk : G.Walk s t) (isPath : walk.IsPath)
    (start_mem : s ∈ V(H)) (end_mem : t ∈ V(H)) (endpoints_ne : s ≠ t)
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ≠ t → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.open hHG walk isPath start_mem end_mem endpoints_ne internal_new edges_new).toGraph =
      G.walkGraph walk := by
  rw [toGraph, toWalk_open]

@[simp]
theorem toGraph_closed {s : α} (hHG : H ≤ G) (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (base_mem : s ∈ V(H)) (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(H))
    (edges_new : ∀ e ∈ walk.edges, e ∉ E(H)) :
    (Ear.closed hHG walk isCycle base_mem internal_new edges_new).toGraph = G.walkGraph walk := by
  rw [toGraph, toWalk_closed]

@[simp]
theorem vertexSet_toGraph (e : G.Ear H) :
    V(e.toGraph) = {x | x ∈ e.toWalk.2.2.support} :=
  e.toWalk.2.2.vertexSet_walkGraph

@[simp]
theorem edgeSet_toGraph (e : G.Ear H) :
    E(e.toGraph) = {f | f ∈ e.toWalk.2.2.edges} :=
  e.toWalk.2.2.edgeSet_walkGraph

/-- Every edge traversed by an ear belongs to the graph traced by that ear. -/
theorem edges_subset_edgeSet_toGraph (e : G.Ear H) :
    ∀ f ∈ e.toWalk.2.2.edges, f ∈ E(e.toGraph) := by
  intro f hf
  rw [edgeSet_toGraph]
  exact hf

/-- The links of the graph traced by an ear are the ambient links traversed by its walk. -/
@[simp]
theorem toGraph_isLink (e : G.Ear H) (f : β) (x y : α) :
    e.toGraph.IsLink f x y ↔ G.IsLink f x y ∧ f ∈ e.toWalk.2.2.edges :=
  e.toWalk.2.2.walkGraph_isLink f x y

/-- The base of an ear is a subgraph of its ambient graph. -/
theorem base_le : ∀ _e : G.Ear H, H ≤ G
  | .open hHG .. => hHG
  | .closed hHG .. => hHG

/-- The underlying walk of an ear has positive length. -/
theorem length_pos : ∀ e : G.Ear H, 0 < e.toWalk.2.2.length
  | .open _ walk _ _ _ endpoints_ne _ _ =>
      Nat.pos_of_ne_zero fun h ↦ endpoints_ne (walk.eq_of_length_eq_zero h)
  | .closed _ _walk isCycle _ _ _ => isCycle.length_pos

/-- The underlying walk of an ear is a trail. -/
theorem isTrail (e : G.Ear H) : e.toWalk.2.2.IsTrail := by
  cases e with
  | «open» h walk isPath start_mem end_mem endpoints_ne internal_new edges_new =>
      rw [toWalk_open]
      exact isPath.isTrail
  | «closed» h walk isCycle base_mem internal_new edges_new =>
      rw [toWalk_closed]
      exact isCycle.isTrail

/-- The graph traced by an ear is a subgraph of its ambient graph. -/
theorem toGraph_le (e : G.Ear H) : e.toGraph ≤ G :=
  e.toWalk.2.2.walkGraph_le_of_pos e.length_pos

/-- The base and traced graph of an ear are compatible subgraphs of the ambient graph. -/
theorem compatible (e : G.Ear H) : H.Compatible e.toGraph :=
  .of_le_le e.base_le e.toGraph_le

/-- The graph obtained by adjoining an ear to its base. -/
def add (e : G.Ear H) : Graph α β :=
  e.compatible.union

@[simp]
theorem vertexSet_add (e : G.Ear H) : V(e.add) = V(H) ∪ V(e.toGraph) :=
  e.compatible.vertexSet_union

@[simp]
theorem edgeSet_add (e : G.Ear H) : E(e.add) = E(H) ∪ E(e.toGraph) :=
  e.compatible.edgeSet_union

/-- A link of `e.add` is a link of the base graph or of the ear's traced graph. -/
@[simp]
theorem add_isLink (e : G.Ear H) (f : β) (x y : α) :
    e.add.IsLink f x y ↔ H.IsLink f x y ∨ e.toGraph.IsLink f x y :=
  e.compatible.union_isLink

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

/-- Adjoining an ear is the compatible union of its base and traced graph. -/
theorem add_eq_union (e : G.Ear H) : e.add = e.compatible.union :=
  (rfl)

/-- Every edge traversed by an ear belongs to the graph obtained by adjoining the ear. -/
theorem edges_toWalk_subset_edgeSet_add (e : G.Ear H) {f : β}
    (hf : f ∈ e.toWalk.2.2.edges) : f ∈ E(e.add) := by
  rw [edgeSet_add, edgeSet_toGraph]
  exact Or.inr hf

/-- The interiors of an open ear and an oppositely directed path in its base are disjoint. -/
theorem open_support_tail_disjoint {s t : α} (hHG : H ≤ G) {p : G.Walk s t}
    (hp : p.IsPath) (ht : t ∈ V(H))
    (hinter : ∀ z ∈ p.support, z ≠ s → z ≠ t → z ∉ V(H))
    {q : H.Walk t s} (hq : q.IsPath) :
    p.support.tail.Disjoint (q.mapLe hHG).support.tail := by
  rw [List.disjoint_left]
  intro z hzp hzq
  have hzq' : z ∈ q.support.tail := by
    simpa only [Walk.support_mapLe_eq_support] using hzq
  have hpNodup := hp.support_nodup
  rw [← p.cons_tail_support] at hpNodup
  have hqNodup := hq.support_nodup
  rw [← q.cons_tail_support] at hqNodup
  have hzs : z ≠ s := fun hzs ↦ (List.nodup_cons.mp hpNodup).1 (hzs ▸ hzp)
  have hzt : z ≠ t := fun hzt ↦ (List.nodup_cons.mp hqNodup).1 (hzt ▸ hzq')
  exact hinter z (List.mem_of_mem_tail hzp) hzs hzt
    (q.support_subset_vertexSet ht z (List.mem_of_mem_tail hzq'))

/-- Adjoining an ear still gives a subgraph of the ambient graph. -/
theorem add_le (e : G.Ear H) : e.add ≤ G :=
  IsSubgraph.union_le e.base_le e.toGraph_le

/-- Adjoining any ear over an edgeless single-vertex base produces the ear's traced graph. -/
@[simp]
theorem add_noEdge_singleton {s : α} (e : G.Ear (Graph.noEdge {s} β)) :
    e.add = e.toGraph := by
  refine (Compatible.of_le_le e.add_le e.toGraph_le).ext ?_ (by simp)
  have hs : e.toWalk.1 = s := by simpa using e.toWalk_fst_mem
  ext x
  simp only [vertexSet_add, vertexSet_noEdge, vertexSet_toGraph, mem_union, mem_singleton_iff, ← hs,
    or_iff_right_iff_imp]
  rintro rfl
  exact Walk.start_mem_support _

/-- Every edge of an ear is absent from its base graph. -/
theorem edge_notMem_base (e : G.Ear H) {f : β} (hf : f ∈ e.toWalk.2.2.edges) :
    f ∉ E(H) := by
  cases e with
  | «open» _ _ _ _ _ _ _ edges_new => exact edges_new f hf
  | «closed» _ _ _ _ _ edges_new => exact edges_new f hf

/-- The edge set traced by an ear is disjoint from the edge set of its base graph. -/
theorem disjoint_edgeSet_toGraph (e : G.Ear H) : Disjoint E(H) E(e.toGraph) := by
  rw [Set.disjoint_left]
  intro f hfH hfEar
  rw [e.edgeSet_toGraph] at hfEar
  exact e.edge_notMem_base hfEar hfH

/-- The edges of an ear are disjoint from those of a walk in its base graph. -/
theorem edges_disjoint_of_le_base (e : G.Ear H) {x y : α} (q : H.Walk x y) :
    e.toWalk.2.2.edges.Disjoint (q.mapLe e.base_le).edges := by
  rw [List.disjoint_left]
  intro f hfe hfq
  exact e.edge_notMem_base hfe
    (q.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using hfq))

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

/-- Adjoining an ear to a connected graph preserves connectedness. -/
theorem connected_add (ear : G.Ear H) (hH : H.Connected) : ear.add.Connected :=
  ear.compatible.connected_union hH ear.connected_toGraph
    ⟨ear.toWalk.1, ear.toWalk_fst_mem, by
      simpa only [vertexSet_toGraph, mem_ofPred_eq] using ear.toWalk.2.2.start_mem_support⟩

/-- Every edge in the graph traced by an ear lies on a cycle after adjoining the ear to a
connected base graph. -/
theorem exists_isCycle_add_of_mem_edgeSet_toGraph (ear : G.Ear H) (hH : H.Connected) {e : β}
    (he : e ∈ E(ear.toGraph)) :
    ∃ x, ∃ p : ear.add.Walk x x, p.IsCycle ∧ e ∈ p.edges := by
  cases ear with
  | @«open» hHG s t p hp hs ht hst hinter hedges =>
      rw [Ear.toGraph_open] at he
      obtain ⟨q, hq⟩ := (hH.reachable ht hs).exists_isPath
      let qG := q.mapLe hHG
      have hqG : qG.IsPath := (Walk.isPath_mapLe hHG q).mpr hq
      have hv : p.support.tail.Disjoint qG.support.tail :=
        open_support_tail_disjoint hHG hp ht hinter hq
      have hedisj : p.edges.Disjoint qG.edges := by
        have h := edges_disjoint_of_le_base
          (Ear.open hHG p hp hs ht hst hinter hedges) q
        rw [Ear.toWalk_open] at h
        exact h
      have hcycle : (p.append qG).IsCycle := hp.isCycle_append hqG hv hedisj
        (Or.inl (Nat.pos_of_ne_zero fun h ↦ hst (p.eq_of_length_eq_zero h)))
      let c := (p.append qG).transfer
        (Ear.open hHG p hp hs ht hst hinter hedges).add_le fun f hf ↦ by
          rw [Walk.edges_append] at hf
          rcases List.mem_append.mp hf with hfp | hfq
          · exact edges_toWalk_subset_edgeSet_add
              (Ear.open hHG p hp hs ht hst hinter hedges)
              (by rw [Ear.toWalk_open]; exact hfp)
          · rw [edgeSet_add]
            exact Or.inl (q.edges_subset_edgeSet (by
              simpa only [qG, Walk.edges_mapLe_eq_edges] using hfq))
      have hc : c.IsCycle := (Walk.isCycle_transfer
        (Ear.open hHG p hp hs ht hst hinter hedges).add_le (p.append qG) _).mpr hcycle
      have heP : e ∈ p.edges := (p.mem_edgeSet_walkGraph e).mp he
      exact ⟨s, c, hc, by
        simp only [c, Walk.edges_transfer, Walk.edges_append, List.mem_append]
        exact Or.inl heP⟩
  | @«closed» hHG s p hp hs hinter hedges =>
      rw [Ear.toGraph_closed] at he
      let c := p.transfer (Ear.closed hHG p hp hs hinter hedges).add_le fun _ hf ↦
        edges_toWalk_subset_edgeSet_add (Ear.closed hHG p hp hs hinter hedges)
          (by rw [Ear.toWalk_closed]; exact hf)
      have hc : c.IsCycle := (Walk.isCycle_transfer
        (Ear.closed hHG p hp hs hinter hedges).add_le p _).mpr hp
      exact ⟨s, c, hc, by
        simpa only [c, Walk.edges_transfer] using (p.mem_edgeSet_walkGraph e).mp he⟩

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

/-- Any cycle based at `s` forms a closed ear over the edgeless single-vertex subgraph
`Graph.noEdge {s} β`. -/
def ofIsCycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    G.Ear (Graph.noEdge {s} β) :=
  .closed (Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr isCycle.start_mem)) walk isCycle
    (by simp) (fun _ _ hxs ↦ by simp [hxs]) (fun _ _ ↦ by simp)

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

instance instDecidableIsCycle : ∀ start : G.EarStart H, Decidable start.IsCycle
  | .vertex v => decidable_of_iff False (isCycle_vertex v).symm
  | .cycle walk isCycle => decidable_of_iff True (isCycle_cycle walk isCycle).symm

/-- Heterogeneously equal initial stages agree on whether they are cycles. -/
theorem isCycle_iff_of_heq {K L : Graph α β} {s₁ : G.EarStart K} {s₂ : G.EarStart L}
    (hKL : K = L) (hs : HEq s₁ s₂) : s₁.IsCycle ↔ s₂.IsCycle := by
  subst hKL
  cases eq_of_heq hs
  rfl

/-- Every allowed initial graph is a subgraph of its ambient graph. -/
theorem le : ∀ _start : G.EarStart H, H ≤ G
  | .vertex v => Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr v.property)
  | .cycle _ isCycle => isCycle.walkGraph_le

/-- Every permitted initial graph of an ear decomposition has an actual vertex. -/
theorem vertexSet_nonempty (start : G.EarStart H) : V(H).Nonempty := by
  cases start with
  | vertex x => exact ⟨x, by simp⟩
  | @cycle x p _ => exact ⟨x, by rw [p.vertexSet_walkGraph]; exact p.start_mem_support⟩

/-- Every allowed initial graph of an ear decomposition is connected. -/
theorem connected : ∀ _start : G.EarStart H, H.Connected
  | .vertex v => connected_of_vertexSet_eq_singleton (vertexSet_noEdge {v.1} β)
  | .cycle walk _ => walk.connected_walkGraph

/-- A vertex-started initial graph is an edgeless single-vertex graph. -/
theorem exists_noEdge_of_not_isCycle :
    ∀ {start : G.EarStart H}, ¬ start.IsCycle → ∃ v : V(G), H = Graph.noEdge {v.1} β
  | .vertex v, _ => ⟨v, rfl⟩
  | .cycle walk isCycle, h => False.elim (h ((isCycle_cycle walk isCycle).mpr trivial))

/-- A vertex-started initial graph has no edges. -/
theorem edgeSet_eq_empty_of_not_isCycle : ∀ {start : G.EarStart H}, ¬ start.IsCycle → E(H) = ∅
  | .vertex _, _ => by simp
  | .cycle walk isCycle, h => False.elim (h ((isCycle_cycle walk isCycle).mpr trivial))

/-- A cycle-started initial graph has at least one edge. -/
theorem edgeSet_nonempty_of_isCycle : ∀ {start : G.EarStart H}, start.IsCycle → E(H).Nonempty
  | .vertex v, h => False.elim ((isCycle_vertex v).mp h)
  | .cycle walk isCycle, _ => by
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil walk.edges
        (by intro h; simpa [← walk.length_edges, h] using isCycle.length_pos)
      exact ⟨e, (walk.mem_edgeSet_walkGraph e).mpr he⟩

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
theorem initial_eq_graphAfter (d : G.EarDecomposition H) : d.initial = d.graphAfter 0 := by
  rw [initial]

/-- The kind of the ear added at a specified step. -/
def kindAt (d : G.EarDecomposition H) (i : Fin d.length) : EarKind :=
  (d.earAt i).2.kind

@[simp]
theorem kindAt_eq (d : G.EarDecomposition H) (i : Fin d.length) :
    d.kindAt i = (d.earAt i).2.kind := by
  rw [kindAt]

/-- The underlying walk of the ear added at a specified step. -/
def walkAt (d : G.EarDecomposition H) (i : Fin d.length) :
    Σ s t : α, G.Walk s t :=
  (d.earAt i).2.toWalk

@[simp]
theorem walkAt_eq (d : G.EarDecomposition H) (i : Fin d.length) :
    d.walkAt i = (d.earAt i).2.toWalk := by
  rw [walkAt]

/-- An open ear decomposition starts from a cycle and adds only open ears. -/
def IsOpen (d : G.EarDecomposition H) : Prop :=
  d.start.IsCycle ∧ ∀ i, d.kindAt i = .open

/-- An ear decomposition starts from a single actual vertex rather than from a cycle. -/
def IsVertexStart (d : G.EarDecomposition H) : Prop :=
  ∃ v : V(G), d.initial = Graph.noEdge {v.1} β

/-- Characterization of a vertex-starting ear decomposition by its initial graph. -/
theorem isVertexStart_iff (d : G.EarDecomposition H) :
    d.IsVertexStart ↔ ∃ v : V(G), d.initial = Graph.noEdge {v.1} β :=
  Iff.rfl

/-- An ear decomposition starts from a single actual vertex if and only if its initial stage is
not a cycle. -/
theorem isVertexStart_iff_not_start_isCycle (d : G.EarDecomposition H) :
    d.IsVertexStart ↔ ¬ d.start.IsCycle := by
  constructor
  · rintro ⟨v, hv⟩ hc
    obtain ⟨e, he⟩ := d.start.edgeSet_nonempty_of_isCycle hc
    rw [← d.initial_eq_graphAfter, hv] at he
    simp at he
  · intro hnc
    obtain ⟨v, hv⟩ := d.start.exists_noEdge_of_not_isCycle hnc
    exact ⟨v, d.initial_eq_graphAfter.trans hv⟩

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
theorem graphAfter_vertex_zero (v : V(G)) :
    (vertex v).graphAfter 0 = Graph.noEdge {v.1} β := by
  rw [vertex]

/-- The initial stage data of `vertex v` is `EarStart.vertex v`. -/
theorem heq_start_vertex (v : V(G)) : HEq (vertex v).start (EarStart.vertex v) :=
  HEq.rfl

/-- A decomposition consisting only of one vertex starts from a vertex. -/
@[simp]
theorem isVertexStart_vertex (v : V(G)) : (vertex v).IsVertexStart :=
  ⟨v, rfl⟩

@[simp]
theorem not_start_isCycle_vertex (v : V(G)) : ¬ (vertex v).start.IsCycle :=
  fun h ↦ (EarStart.isCycle_vertex v).mp h

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
theorem graphAfter_cycle_zero {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).graphAfter 0 = G.walkGraph walk := by
  rw [cycle]

/-- The initial stage data of `cycle walk isCycle` is `EarStart.cycle walk isCycle`. -/
theorem heq_start_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    HEq (cycle walk isCycle).start (EarStart.cycle walk isCycle) :=
  HEq.rfl

@[simp]
theorem start_isCycle_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).start.IsCycle :=
  (EarStart.isCycle_cycle walk isCycle).mpr trivial

@[simp]
theorem not_isVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    ¬ (cycle walk isCycle).IsVertexStart := by
  rw [isVertexStart_iff_not_start_isCycle]
  exact not_not_intro (start_isCycle_cycle walk isCycle)

/-- A decomposition containing just its initial cycle is open. -/
theorem isOpen_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).IsOpen :=
  ⟨start_isCycle_cycle walk isCycle, fun i ↦ Fin.elim0 i⟩

/-- Reindex the final graph of an ear decomposition along an equality of graphs. -/
@[expose]
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
    (i : Fin ((d.copy h).length + 1)) :
    (d.copy h).graphAfter i =
      d.graphAfter (Fin.cast (congrArg (· + 1) (length_copy d h)) i) := (rfl)

/-- Reindexing the final graph preserves the initial graph. -/
theorem initial_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).initial = d.initial := (rfl)

/-- Reindexing the final graph preserves the initial stage data. -/
theorem heq_start_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    HEq (d.copy h).start d.start := HEq.rfl

@[simp]
theorem start_isCycle_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).start.IsCycle ↔ d.start.IsCycle := Iff.rfl

@[simp]
theorem isVertexStart_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).IsVertexStart ↔ d.IsVertexStart := Iff.rfl

@[simp]
theorem earAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin (d.copy h).length) :
    (d.copy h).earAt i = d.earAt (Fin.cast (length_copy d h) i) := (rfl)

/-- Reindexing the final graph preserves the kind of each ear. -/
theorem kindAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin (d.copy h).length) :
    (d.copy h).kindAt i = d.kindAt (Fin.cast (length_copy d h) i) := (rfl)

/-- Reindexing the final graph preserves the walk of each ear. -/
theorem walkAt_copy {H' : Graph α β} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin (d.copy h).length) :
    (d.copy h).walkAt i = d.walkAt (Fin.cast (length_copy d h) i) := (rfl)

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
  earAt i := Fin.lastCases ⟨H, ear⟩ d.earAt i
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
      (Fin.cast (length_snoc d ear).symm i).castSucc = d.graphAfter i := by
  -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
  change Fin.lastCases ear.add d.graphAfter (Fin.cast rfl i).castSucc = d.graphAfter i
  rw [Fin.cast_eq_self, Fin.lastCases_castSucc]

/-- Adjoining an ear does not change the initial graph of a decomposition. -/
@[simp]
theorem graphAfter_snoc_zero (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).graphAfter 0 = d.graphAfter 0 :=
  snoc_graphAfter_zero d ear

/-- Adjoining an ear preserves the initial graph of a decomposition. -/
theorem initial_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).initial = d.initial := by
  simp only [initial_eq_graphAfter, graphAfter_snoc_zero]

/-- Adjoining an ear preserves the property of starting from a single vertex. -/
@[simp]
theorem isVertexStart_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).IsVertexStart ↔ d.IsVertexStart := by
  simp only [isVertexStart_iff, initial_eq_graphAfter, graphAfter_snoc_zero]

@[simp]
theorem earAt_snoc_castSucc (d : G.EarDecomposition H) (ear : G.Ear H)
    (i : Fin d.length) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm i.castSucc) = d.earAt i := by
  -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
  change Fin.lastCases ⟨H, ear⟩ d.earAt (Fin.cast rfl i.castSucc) = d.earAt i
  rw [Fin.cast_eq_self, Fin.lastCases_castSucc]

@[simp]
theorem earAt_snoc_last (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm (Fin.last d.length)) =
      ⟨H, ear⟩ := by
  -- Projection reduction exposes `Fin.lastCases`; rewriting cannot unfold the opaque `snoc` body.
  change Fin.lastCases (⟨H, ear⟩ : Σ K, G.Ear K) d.earAt
    (Fin.cast rfl (Fin.last d.length)) =
    (⟨H, ear⟩ : Σ K, G.Ear K)
  rw [Fin.cast_eq_self, Fin.lastCases_last]

/-- Adjoining an ear preserves the initial stage data. -/
theorem heq_start_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    HEq (d.snoc ear).start d.start :=
  eqRec_heq (snoc_graphAfter_zero d ear).symm d.start

/-- Adjoining an ear preserves whether the decomposition starts from a cycle. -/
@[simp]
theorem start_isCycle_snoc (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).start.IsCycle ↔ d.start.IsCycle :=
  EarStart.isCycle_iff_of_heq (graphAfter_snoc_zero d ear) (heq_start_snoc d ear)

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

/-- A length-`1` vertex-started ear decomposition formed by adjoining a single ear over an edgeless
single-vertex base `Graph.noEdge {s} β`. -/
def ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β)) : G.EarDecomposition ear.add :=
  (vertex ⟨s, singleton_subset_iff.mp (Graph.noEdge_le_iff.mp ear.base_le)⟩).snoc ear

@[simp]
theorem length_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β)) :
    (ofEar ear).length = 1 := (rfl)

@[simp]
theorem graphAfter_ofEar_zero {s : α} (ear : G.Ear (Graph.noEdge {s} β)) :
    (ofEar ear).graphAfter 0 = Graph.noEdge {s} β := by
  rw [ofEar, graphAfter_snoc_zero, graphAfter_vertex_zero]

/-- The initial graph of `ofEar ear` is the single-vertex base `Graph.noEdge {s} β`. -/
theorem initial_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β)) :
    (ofEar ear).initial = Graph.noEdge {s} β := by
  rw [initial_eq_graphAfter, graphAfter_ofEar_zero]

@[simp]
theorem isVertexStart_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β)) :
    (ofEar ear).IsVertexStart := by
  rw [ofEar, isVertexStart_snoc]
  exact isVertexStart_vertex _

@[simp]
theorem not_start_isCycle_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β)) :
    ¬ (ofEar ear).start.IsCycle := by
  rw [ofEar, start_isCycle_snoc]
  exact not_start_isCycle_vertex _

@[simp]
theorem earAt_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β))
    (i : Fin (ofEar ear).length) :
    (ofEar ear).earAt i = ⟨Graph.noEdge {s} β, ear⟩ := by
  let v : V(G) := ⟨s, singleton_subset_iff.mp (Graph.noEdge_le_iff.mp ear.base_le)⟩
  have hi : i = Fin.cast (length_snoc (vertex v) ear).symm (Fin.last (vertex v).length) :=
    Fin.ext (Nat.lt_one_iff.mp i.isLt)
  rw [hi]
  exact earAt_snoc_last (vertex v) ear

/-- The unique ear of `ofEar ear` has kind `ear.kind`. -/
theorem kindAt_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β))
    (i : Fin (ofEar ear).length) :
    (ofEar ear).kindAt i = ear.kind := by
  rw [kindAt_eq, earAt_ofEar]

/-- The unique ear of `ofEar ear` has walk `ear.toWalk`. -/
theorem walkAt_ofEar {s : α} (ear : G.Ear (Graph.noEdge {s} β))
    (i : Fin (ofEar ear).length) :
    (ofEar ear).walkAt i = ear.toWalk := by
  rw [walkAt_eq, earAt_ofEar]

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
  rw [d.graphAfter_succ, ← d.earAt_fst i]
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
theorem vertexSet_graphAfter_nonempty (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    V(d.graphAfter i).Nonempty :=
  d.start.vertexSet_nonempty.mono (d.initial_le_graphAfter i).vertexSet_mono

/-- The final graph of every ear decomposition has an actual vertex. -/
theorem vertexSet_nonempty (d : G.EarDecomposition H) : V(H).Nonempty := by
  rw [← congrArg vertexSet d.graphAfter_last]
  exact d.vertexSet_graphAfter_nonempty (Fin.last d.length)

/-- Every stage graph of an ear decomposition is connected. -/
theorem connected_graphAfter (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.graphAfter i).Connected := by
  induction i using Fin.induction with
  | zero => exact d.start.connected
  | succ k ih =>
      rw [d.graphAfter_succ]
      exact (d.earAt k).2.connected_add ((d.earAt_fst k).symm ▸ ih)

/-- The final graph of any ear decomposition is connected. -/
theorem connected (d : G.EarDecomposition H) : H.Connected :=
  d.graphAfter_last ▸ d.connected_graphAfter (Fin.last d.length)

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

/-- Prefixing preserves the initial stage data. -/
theorem heq_start_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    HEq (d.prefix i).start d.start :=
  eqRec_heq
    (congrArg d.graphAfter (Fin.castLE_zero (Nat.succ_le_iff.mpr i.isLt))).symm d.start

/-- Prefixing preserves whether the decomposition starts from a cycle. -/
@[simp]
theorem start_isCycle_prefix (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    (d.prefix i).start.IsCycle ↔ d.start.IsCycle :=
  EarStart.isCycle_iff_of_heq
    (congrArg d.graphAfter (Fin.castLE_zero (Nat.succ_le_iff.mpr i.isLt))) (heq_start_prefix d i)

/-- Prefixing preserves whether the decomposition starts from a single vertex. -/
@[simp]
theorem isVertexStart_prefix (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    (d.prefix i).IsVertexStart ↔ d.IsVertexStart := by
  rw [isVertexStart_iff_not_start_isCycle, isVertexStart_iff_not_start_isCycle,
    start_isCycle_prefix]

/-- Induction over prefix decompositions in construction order. The zero prefix carries the
initial vertex or cycle, and the successor case adds the next displayed ear. -/
theorem prefix_induction (d : G.EarDecomposition H)
    {P : ∀ {K : Graph α β}, G.EarDecomposition K → Prop}
    (initial : P (d.prefix 0))
    (snoc : ∀ i : Fin d.length, P (d.prefix i.castSucc) → P (d.prefix i.succ))
    (i : Fin (d.length + 1)) : P (d.prefix i) :=
  Fin.induction initial snoc i

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

/-- Prefixing retains the initial graph. -/
@[simp]
theorem graphAfter_prefix_zero (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.prefix i).graphAfter 0 = d.graphAfter 0 :=
  congrArg d.graphAfter (Fin.castLE_zero _)

/-- Prefixing retains the walks of the original ears before the chosen index. -/
theorem walkAt_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1)) (j : Fin i.val) :
    (d.prefix i).walkAt (Fin.cast (length_prefix d i).symm j) =
      d.walkAt (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [walkAt_eq, walkAt_eq, earAt_prefix]

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
theorem edgeSet_eq_iUnion_of_isVertexStart {d : G.EarDecomposition H} (h : d.IsVertexStart) :
    E(H) = ⋃ j : Fin d.length, E((d.earAt j).2.toGraph) := by
  obtain ⟨v, hv⟩ := h
  rw [d.edgeSet_eq_union_iUnion, hv]
  simp

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
theorem existsUnique_mem_edges_walkAt_of_isVertexStart {d : G.EarDecomposition H}
    (h : d.IsVertexStart) {e : β} (he : e ∈ E(H)) :
    ∃! i : Fin d.length, e ∈ (d.walkAt i).2.2.edges := by
  rw [d.edgeSet_eq_iUnion_of_isVertexStart h, mem_iUnion] at he
  obtain ⟨i, hi⟩ := he
  have hmem : ∀ j : Fin d.length, e ∈ (d.walkAt j).2.2.edges ↔ e ∈ E((d.earAt j).2.toGraph) :=
    fun j ↦ by rw [Ear.edgeSet_toGraph, mem_ofPred_eq, d.walkAt_eq j]
  refine ⟨i, (hmem i).mpr hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact Set.disjoint_left.mp (d.pairwise_disjoint_edgeSet_earAt hji) ((hmem j).mp hj) hi

end EarDecomposition

end Graph
