/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Trace

/-!
# Ear decompositions of multigraphs

This file defines open and closed ears in an edge-labelled multigraph and packages a finite ear
decomposition as construction data.  A decomposition starts from one actual vertex or from a
cycle, then adds ears whose internal vertices and edge identities are new.  Loops and parallel
edges are retained: a loop can be a one-edge closed ear, and two parallel edges can form a
two-edge closed ear.

The prefix interface exposes the graph after every initial segment, the ear added at every step,
and a decomposition of each prefix.  It is intended as the common data layer for ear
characterizations of edge connectivity and for constructing strong orientations.

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

/-- The underlying walk of an ear, including its endpoints. -/
def toWalk : G.Ear H → Σ s t : α, G.Walk s t
  | .open _ walk .. => ⟨_, _, walk⟩
  | .closed _ walk .. => ⟨_, _, walk⟩

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

@[simp]
theorem vertexSet_add (e : G.Ear H) : V(e.add) = V(H) ∪ V(e.toGraph) :=
  e.compatible.vertexSet_union

@[simp]
theorem edgeSet_add (e : G.Ear H) : E(e.add) = E(H) ∪ E(e.toGraph) :=
  e.compatible.edgeSet_union

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

/-- Every allowed initial graph is a subgraph of its ambient graph. -/
theorem le : ∀ _start : G.EarStart H, H ≤ G
  | .vertex v => Graph.noEdge_le_iff.mpr (by simp [v.property])
  | .cycle walk isCycle => walk.walkGraph_le_of_pos <|
      Nat.pos_of_ne_zero fun h ↦ isCycle.not_nil (Walk.length_eq_zero_iff.mp h)

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

/-- The kind of the ear added at a specified step. -/
def kindAt (d : G.EarDecomposition H) (i : Fin d.length) : EarKind :=
  (d.earAt i).2.kind

/-- The underlying walk of the ear added at a specified step. -/
def walkAt (d : G.EarDecomposition H) (i : Fin d.length) :
    Σ s t : α, G.Walk s t :=
  (d.earAt i).2.toWalk

/-- An open ear decomposition starts from a cycle and adds only open ears. -/
def IsOpen (d : G.EarDecomposition H) : Prop :=
  d.start.IsCycle ∧ ∀ i, d.kindAt i = .open

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

/-- A decomposition containing just its initial cycle is open. -/
theorem isOpen_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).IsOpen :=
  ⟨trivial, fun i ↦ Fin.elim0 i⟩

/-- Adjoin one ear at the end of a decomposition. -/
def snoc (d : G.EarDecomposition H) (ear : G.Ear H) : G.EarDecomposition ear.add where
  length := d.length + 1
  graphAfter i := Fin.lastCases ear.add d.graphAfter i
  start := by
    rw [show (0 : Fin (d.length + 2)) = (0 : Fin (d.length + 1)).castSucc by rfl,
      Fin.lastCases_castSucc]
    exact d.start
  earAt i := by
    exact Fin.lastCases ⟨H, ear⟩ d.earAt i
  earAt_fst i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using d.graphAfter_last.symm
    · simpa only [Fin.lastCases_castSucc] using d.earAt_fst j
  graphAfter_succ i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_last]
    · rw [show j.castSucc.succ = j.succ.castSucc by rfl, Fin.lastCases_castSucc,
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
    change Fin.lastCases ear.add d.graphAfter _ = d.graphAfter i
    rw [show (Fin.cast (length_snoc d ear).symm i).castSucc = i.castSucc by
      apply Fin.ext; rfl]
    exact Fin.lastCases_castSucc i

@[simp]
theorem earAt_snoc_castSucc (d : G.EarDecomposition H) (ear : G.Ear H)
    (i : Fin d.length) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm i.castSucc) = d.earAt i :=
  by
    change Fin.lastCases ⟨H, ear⟩ d.earAt _ = d.earAt i
    rw [show Fin.cast (length_snoc d ear).symm i.castSucc = i.castSucc by apply Fin.ext; rfl]
    exact Fin.lastCases_castSucc i

@[simp]
theorem earAt_snoc_last (d : G.EarDecomposition H) (ear : G.Ear H) :
    (d.snoc ear).earAt (Fin.cast (length_snoc d ear).symm (Fin.last d.length)) =
      ⟨H, ear⟩ :=
  by
    change Fin.lastCases (⟨H, ear⟩ : Σ K, G.Ear K) d.earAt _ =
      (⟨H, ear⟩ : Σ K, G.Ear K)
    rw [show Fin.cast (length_snoc d ear).symm (Fin.last d.length) = Fin.last d.length by
      apply Fin.ext; rfl]
    exact Fin.lastCases_last

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

private def prefixStageIndex (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin (i.val + 1)) : Fin (d.length + 1) :=
  ⟨j, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) i.isLt⟩

private def prefixEarIndex (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin i.val) : Fin d.length :=
  ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩

/-- The decomposition formed by the first `i` ears. -/
def «prefix» (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    G.EarDecomposition (d.graphAfter i) where
  length := i.val
  graphAfter j := d.graphAfter (prefixStageIndex d i j)
  start := by
    rw [show prefixStageIndex d i 0 = (0 : Fin (d.length + 1)) by apply Fin.ext; rfl]
    exact d.start
  earAt j := d.earAt (prefixEarIndex d i j)
  earAt_fst j := by
    rw [d.earAt_fst (prefixEarIndex d i j)]
    congr 1
  graphAfter_succ j := by
    rw [show prefixStageIndex d i j.succ = (prefixEarIndex d i j).succ by
      apply Fin.ext; rfl]
    exact d.graphAfter_succ (prefixEarIndex d i j)
  graphAfter_last := by
    rw [show prefixStageIndex d i (Fin.last i.val) = i by apply Fin.ext; rfl]

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
  change d.graphAfter _ = d.graphAfter _
  congr 1

/-- Prefixing retains the original ears before the chosen index. -/
@[simp]
theorem earAt_prefix (d : G.EarDecomposition H) (i : Fin (d.length + 1))
    (j : Fin i.val) :
    (d.prefix i).earAt (Fin.cast (length_prefix d i).symm j) =
      d.earAt (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  change d.earAt _ = d.earAt _
  congr 1

/-- The final prefix graph is the final graph of the decomposition. -/
@[simp]
theorem graphAfter_final (d : G.EarDecomposition H) :
    d.graphAfter (Fin.last d.length) = H :=
  d.graphAfter_last

end EarDecomposition

end Graph
