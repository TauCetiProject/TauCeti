/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic

import Mathlib.Data.Fin.Tuple.Basic

/-!
# Replacing the initial stage and normalizing ear decompositions to vertex starts

This file shows that any ear decomposition `d : G.EarDecomposition H` can have its initial stage
replaced by an ear decomposition `d₀ : G.EarDecomposition d.initial` by replaying the displayed
ears of `d` on top of `d₀` (`Graph.EarDecomposition.replaceInitial`).  Specializing `d₀` to the
single-vertex normalization of `d.start` (`Graph.EarStart.toVertexDecomposition`) turns an initial
cycle into a single-vertex start followed by one closed ear
(`Graph.EarDecomposition.toVertexStart`), showing that unrestricted ear decompositions and
vertex-started ear decompositions exist for simultaneously the same subgraphs
(`Graph.nonempty_earDecomposition_iff_exists_isVertexStart`).

The normalization follows R. Diestel, *Graph Theory*, Chapter 3, adapted to multigraphs by
retaining loop and parallel-edge identities.

## Main declarations

* `Graph.EarDecomposition.replaceInitial`: replay the displayed ears of `d` on top of an ear
  decomposition of `d.initial`.
* `Graph.EarStart.toVertexDecomposition`: view any permitted initial stage as a vertex-started ear
  decomposition of length `0` or `1`.
* `Graph.EarDecomposition.toVertexStart`: normalize any ear decomposition to start at a single
  actual vertex.
* `Graph.nonempty_earDecomposition_iff_exists_isVertexStart`: a subgraph admits an ear
  decomposition if and only if it admits a vertex-started one.
-/

public section

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

namespace EarDecomposition

private def replaceInitialGraphAfter (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (k : Fin (d₀.length + d.length + 1)) : Graph α β :=
  if hk : k.val ≤ d₀.length then d₀.graphAfter ⟨k.val, Nat.lt_succ_of_le hk⟩
  else d.graphAfter ⟨k.val - d₀.length, by omega⟩

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
  earAt_fst k := k.addCases
    (fun i ↦ by
      rw [Fin.addCases_left, d₀.earAt_fst i]
      have hk : (Fin.castAdd d.length i).castSucc =
          (⟨i.castSucc.val, by omega⟩ : Fin (d₀.length + d.length + 1)) := Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_left])
    (fun i ↦ by
      rw [Fin.addCases_right, d.earAt_fst i]
      have hk : (Fin.natAdd d₀.length i).castSucc =
          (⟨d₀.length + i.castSucc.val, by omega⟩ : Fin (d₀.length + d.length + 1)) :=
        Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_right])
  graphAfter_succ k := k.addCases
    (fun i ↦ by
      rw [Fin.addCases_left, ← d₀.graphAfter_succ i]
      have hk : (Fin.castAdd d.length i).succ =
          (⟨i.succ.val, by omega⟩ : Fin (d₀.length + d.length + 1)) := Fin.ext (by simp)
      rw [hk, replaceInitialGraphAfter_left])
    (fun i ↦ by
      rw [Fin.addCases_right, ← d.graphAfter_succ i]
      have hk : (Fin.natAdd d₀.length i).succ =
          (⟨d₀.length + i.succ.val, by omega⟩ : Fin (d₀.length + d.length + 1)) :=
        Fin.ext (by simp [Nat.add_assoc])
      rw [hk, replaceInitialGraphAfter_right])
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

/-- Replacing the initial stage sets the initial stage data to that of `d₀`. -/
theorem heq_start_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) : HEq (d.replaceInitial d₀).start d₀.start :=
  eqRec_heq (replaceInitialGraphAfter_left d d₀ 0).symm d₀.start

@[simp]
theorem start_isCycle_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle :=
  EarStart.isCycle_iff_of_heq (replaceInitialGraphAfter_left d d₀ 0)
    (heq_start_replaceInitial d d₀)

@[simp]
theorem isVertexStart_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsVertexStart ↔ d₀.IsVertexStart := by
  simp only [isVertexStart_iff, initial_replaceInitial]

private theorem earAt_replaceInitial (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (k : Fin (d₀.length + d.length)) :
    (d.replaceInitial d₀).earAt (Fin.cast (d.length_replaceInitial d₀).symm k) =
      Fin.addCases d₀.earAt d.earAt k := (rfl)

/-- Replacing the initial stage retains every ear of `d₀` in the prefix positions. -/
@[simp]
theorem earAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) = d₀.earAt i :=
  (earAt_replaceInitial d d₀ _).trans (Fin.addCases_left i)

/-- Replacing the initial stage shifts every ear of `d` by `d₀.length`. -/
@[simp]
theorem earAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) = d.earAt i :=
  (earAt_replaceInitial d d₀ _).trans (Fin.addCases_right i)

/-- Replacing the initial stage retains the kind of every ear of `d₀`. -/
theorem kindAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) = d₀.kindAt i :=
  by rw [kindAt_eq, earAt_replaceInitial_castAdd, ← kindAt_eq]

/-- Replacing the initial stage retains the kind of every shifted ear of `d`. -/
theorem kindAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) = d.kindAt i :=
  by rw [kindAt_eq, earAt_replaceInitial_natAdd, ← kindAt_eq]

/-- Replacing the initial stage retains the walk of every ear of `d₀`. -/
theorem walkAt_replaceInitial_castAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) = d₀.walkAt i :=
  by rw [walkAt_eq, earAt_replaceInitial_castAdd, ← walkAt_eq]

/-- Replacing the initial stage retains the walk of every shifted ear of `d`. -/
theorem walkAt_replaceInitial_natAdd (d : G.EarDecomposition H)
    (d₀ : G.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) = d.walkAt i :=
  by rw [walkAt_eq, earAt_replaceInitial_natAdd, ← walkAt_eq]

/-- Replacing the initial stage yields an open ear decomposition exactly when `d₀` is open and
every ear of `d` is open. -/
@[simp]
theorem isOpen_replaceInitial (d : G.EarDecomposition H) (d₀ : G.EarDecomposition d.initial) :
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
  | .cycle walk isCycle =>
      (EarDecomposition.ofEar (Ear.ofIsCycle walk isCycle)).copy (Ear.add_ofIsCycle walk isCycle)

@[simp]
theorem toVertexDecomposition_vertex (v : V(G)) :
    (EarStart.vertex v).toVertexDecomposition = .vertex v := (rfl)

/-- Normalizing a cycle start wraps `Ear.ofIsCycle` in a single-ear decomposition. -/
theorem toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition =
      (EarDecomposition.ofEar (Ear.ofIsCycle walk isCycle)).copy
        (Ear.add_ofIsCycle walk isCycle) := (rfl)

@[simp]
theorem length_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.length = 1 := by
  rw [toVertexDecomposition_cycle, EarDecomposition.length_copy, EarDecomposition.length_ofEar]

/-- A cycle start normalizes to a length-`1` vertex-started decomposition, whereas a vertex start
has length `0`. -/
theorem length_toVertexDecomposition :
    ∀ start : G.EarStart H, start.toVertexDecomposition.length = if start.IsCycle then 1 else 0
  | .vertex v => by simp
  | .cycle walk isCycle => by simp

/-- Normalizing a cycle start sets the initial graph to its base vertex without edges. -/
theorem initial_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.initial = Graph.noEdge {s} β := by
  rw [toVertexDecomposition_cycle, EarDecomposition.initial_copy, EarDecomposition.initial_ofEar]

/-- The single ear of the normalized decomposition of a cycle start is `Ear.ofIsCycle`. -/
@[simp]
theorem earAt_toVertexDecomposition_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (i : Fin (EarStart.cycle walk isCycle).toVertexDecomposition.length) :
    (EarStart.cycle walk isCycle).toVertexDecomposition.earAt i =
      ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ :=
  ((EarDecomposition.ofEar (Ear.ofIsCycle walk isCycle)).earAt_copy
    (Ear.add_ofIsCycle walk isCycle) i).trans (EarDecomposition.earAt_ofEar _ _)

@[simp]
theorem isVertexStart_toVertexDecomposition :
    ∀ start : G.EarStart H, start.toVertexDecomposition.IsVertexStart
  | .vertex v => EarDecomposition.isVertexStart_vertex v
  | .cycle walk isCycle => by
      rw [toVertexDecomposition_cycle, EarDecomposition.isVertexStart_copy]
      exact EarDecomposition.isVertexStart_ofEar _

@[simp]
theorem not_start_isCycle_toVertexDecomposition (start : G.EarStart H) :
    ¬ start.toVertexDecomposition.start.IsCycle :=
  (EarDecomposition.isVertexStart_iff_not_start_isCycle _).mp
    start.isVertexStart_toVertexDecomposition

private theorem toVertexDecomposition_of_not_isCycle {K : Graph α β} :
    ∀ (start : G.EarStart K), ¬ start.IsCycle →
      start.toVertexDecomposition.length = 0 ∧
        start.toVertexDecomposition.initial = K ∧ HEq start.toVertexDecomposition.start start
  | .vertex v, _ =>
      ⟨by simp, by rw [toVertexDecomposition_vertex, EarDecomposition.initial_vertex],
        by rw [toVertexDecomposition_vertex]; exact EarDecomposition.heq_start_vertex v⟩
  | .cycle walk isCycle, h => False.elim (h ((isCycle_cycle walk isCycle).mpr trivial))

/-- Every cycle-started `EarStart` is given by an underlying cycle in `G`. -/
theorem exists_cycle_of_isCycle {K : Graph α β} :
    ∀ {start : G.EarStart K}, start.IsCycle →
      ∃ (s : α) (walk : G.Walk s s) (isCycle : walk.IsCycle),
        K = G.walkGraph walk ∧ HEq start (EarStart.cycle walk isCycle)
  | .vertex v, h => False.elim ((isCycle_vertex v).mp h)
  | .cycle walk isCycle, _ => ⟨_, walk, isCycle, rfl, HEq.rfl⟩

end EarStart

namespace EarDecomposition

variable {G H : Graph α β}

private def normalizedStart (d : G.EarDecomposition H) : G.EarDecomposition d.initial :=
  d.start.toVertexDecomposition.copy d.initial_eq_graphAfter.symm

private theorem length_normalizedStart (d : G.EarDecomposition H) :
    d.normalizedStart.length = if d.start.IsCycle then 1 else 0 :=
  (d.start.toVertexDecomposition.length_copy _).trans d.start.length_toVertexDecomposition

private theorem earAt_normalizedStart (d : G.EarDecomposition H)
    (j : Fin d.normalizedStart.length) :
    d.normalizedStart.earAt j =
      d.start.toVertexDecomposition.earAt
        (Fin.cast (d.start.toVertexDecomposition.length_copy _) j) :=
  d.start.toVertexDecomposition.earAt_copy d.initial_eq_graphAfter.symm j

/-- Normalize any ear decomposition so that it starts from a single vertex, turning an initial
cycle into a first closed ear. -/
def toVertexStart (d : G.EarDecomposition H) : G.EarDecomposition H :=
  d.replaceInitial d.normalizedStart

private theorem length_toVertexStart_eq (d : G.EarDecomposition H) :
    d.toVertexStart.length = (d.replaceInitial d.normalizedStart).length := rfl

private theorem graphAfter_toVertexStart (d : G.EarDecomposition H)
    (i : Fin (d.toVertexStart.length + 1)) :
    d.toVertexStart.graphAfter i =
      (d.replaceInitial d.normalizedStart).graphAfter
        (Fin.cast (congrArg (· + 1) d.length_toVertexStart_eq) i) := (rfl)

private theorem earAt_toVertexStart (d : G.EarDecomposition H) (i : Fin d.toVertexStart.length) :
    d.toVertexStart.earAt i =
      (d.replaceInitial d.normalizedStart).earAt (Fin.cast d.length_toVertexStart_eq i) := (rfl)

@[simp]
theorem isVertexStart_toVertexStart (d : G.EarDecomposition H) :
    d.toVertexStart.IsVertexStart := by
  rw [toVertexStart, isVertexStart_replaceInitial, normalizedStart, isVertexStart_copy]
  exact d.start.isVertexStart_toVertexDecomposition

@[simp]
theorem not_start_isCycle_toVertexStart (d : G.EarDecomposition H) :
    ¬ d.toVertexStart.start.IsCycle :=
  (d.toVertexStart.isVertexStart_iff_not_start_isCycle).mp d.isVertexStart_toVertexStart

/-- Normalizing to a vertex start adds one ear when `d` starts at a cycle and keeps the length
unchanged otherwise. -/
theorem length_toVertexStart (d : G.EarDecomposition H) :
    d.toVertexStart.length = (if d.start.IsCycle then 1 else 0) + d.length := by
  rw [toVertexStart, length_replaceInitial, d.length_normalizedStart]

/-- Normalizing a vertex-started decomposition preserves its length. -/
theorem length_toVertexStart_of_isVertexStart {d : G.EarDecomposition H} (h : d.IsVertexStart) :
    d.toVertexStart.length = d.length := by
  simp [d.length_toVertexStart, (d.isVertexStart_iff_not_start_isCycle).mp h]

/-- Normalizing a cycle-started decomposition increases its length by one. -/
theorem length_toVertexStart_of_isCycle {d : G.EarDecomposition H} (h : d.start.IsCycle) :
    d.toVertexStart.length = 1 + d.length := by
  simp [d.length_toVertexStart, h]

/-- The initial graph of `d.toVertexStart` is the single-vertex base of `d.start`. -/
theorem initial_toVertexStart (d : G.EarDecomposition H) :
    d.toVertexStart.initial = d.start.toVertexDecomposition.initial := by
  rw [toVertexStart, initial_replaceInitial, normalizedStart, initial_copy]

/-- Every original stage graph of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem graphAfter_toVertexStart_natAdd (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toVertexStart.graphAfter
      (Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
        (congrArg (· + 1) d.length_toVertexStart.symm))
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) = d.graphAfter i := by
  rw [d.graphAfter_toVertexStart]
  have hi : Fin.cast (congrArg (· + 1) d.length_toVertexStart_eq)
        (Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
          (congrArg (· + 1) d.length_toVertexStart.symm))
          (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      Fin.cast ((Nat.add_assoc d.normalizedStart.length d.length 1).symm.trans
        (congrArg (· + 1) (d.length_replaceInitial d.normalizedStart).symm))
        (Fin.natAdd d.normalizedStart.length i) :=
    Fin.ext (by simp [d.length_normalizedStart])
  rw [hi, d.graphAfter_replaceInitial_natAdd d.normalizedStart i]

/-- Every original ear of `d` appears at the corresponding shifted index in `d.toVertexStart`. -/
theorem earAt_toVertexStart_natAdd (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toVertexStart.earAt
      (Fin.cast d.length_toVertexStart.symm
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) = d.earAt i := by
  rw [d.earAt_toVertexStart]
  have hi : Fin.cast d.length_toVertexStart_eq
        (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      Fin.cast (d.length_replaceInitial d.normalizedStart).symm
        (Fin.natAdd d.normalizedStart.length i) :=
    Fin.ext (by simp [d.length_normalizedStart])
  rw [hi, d.earAt_replaceInitial_natAdd d.normalizedStart i]

/-- Normalizing a decomposition that already starts from a single vertex leaves it unchanged. -/
theorem toVertexStart_eq_self {d : G.EarDecomposition H} (h : d.IsVertexStart) :
    d.toVertexStart = d := by
  have hnc : ¬ d.start.IsCycle := (d.isVertexStart_iff_not_start_isCycle).mp h
  obtain ⟨_, _, hstart₀⟩ := EarStart.toVertexDecomposition_of_not_isCycle d.start hnc
  have hlen : d.toVertexStart.length = d.length := d.length_toVertexStart_of_isVertexStart h
  refine (ext d d.toVertexStart hlen.symm
    ((Fin.heq_fun_iff (congrArg (· + 1) hlen.symm)).mpr fun i ↦ ?_)
    (((d.heq_start_replaceInitial d.normalizedStart).trans
      (d.start.toVertexDecomposition.heq_start_copy _)).trans hstart₀).symm
    ((Fin.heq_fun_iff hlen.symm).mpr fun i ↦ ?_)).symm
  · have hi : (⟨i, congrArg (· + 1) hlen.symm ▸ i.2⟩ : Fin (d.toVertexStart.length + 1)) =
        Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
          (congrArg (· + 1) d.length_toVertexStart.symm))
          (Fin.natAdd (if d.start.IsCycle then 1 else 0) i) := Fin.ext (by simp [hnc])
    rw [hi, d.graphAfter_toVertexStart_natAdd i]
  · have hi : (⟨i, hlen.symm ▸ i.2⟩ : Fin d.toVertexStart.length) =
        Fin.cast d.length_toVertexStart.symm
          (Fin.natAdd (if d.start.IsCycle then 1 else 0) i) := Fin.ext (by simp [hnc])
    rw [hi, d.earAt_toVertexStart_natAdd i]

private theorem toVertexDecomposition_of_heq_cycle {K : Graph α β} (start : G.EarStart K)
    {s : α} {walk : G.Walk s s} {isCycle : walk.IsCycle}
    (hK : K = G.walkGraph walk) (hstart : HEq start (EarStart.cycle walk isCycle)) :
    start.toVertexDecomposition.initial = Graph.noEdge {s} β ∧
      ∀ j : Fin start.toVertexDecomposition.length,
        start.toVertexDecomposition.earAt j =
          ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  subst hK
  cases eq_of_heq hstart
  exact ⟨EarStart.initial_toVertexDecomposition_cycle walk isCycle,
    EarStart.earAt_toVertexDecomposition_cycle walk isCycle⟩

private theorem earAt_toVertexStart_zero_of_heq_cycle (d : G.EarDecomposition H)
    {s : α} {walk : G.Walk s s} {isCycle : walk.IsCycle}
    (hK : d.graphAfter 0 = G.walkGraph walk)
    (hstart : HEq d.start (EarStart.cycle walk isCycle))
    (i : Fin d.toVertexStart.length) (hi : i.val = 0) :
    d.toVertexStart.earAt i = ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  obtain ⟨_, hear₀⟩ := toVertexDecomposition_of_heq_cycle d.start hK hstart
  have hc : d.start.IsCycle :=
    (EarStart.isCycle_iff_of_heq hK hstart).mpr ((EarStart.isCycle_cycle walk isCycle).mpr trivial)
  let j₀ : Fin d.normalizedStart.length := ⟨0, by simp [d.length_normalizedStart, hc]⟩
  have hi' : Fin.cast d.length_toVertexStart_eq i =
      Fin.cast (d.length_replaceInitial d.normalizedStart).symm (Fin.castAdd d.length j₀) :=
    Fin.ext hi
  rw [d.earAt_toVertexStart, hi', d.earAt_replaceInitial_castAdd, d.earAt_normalizedStart]
  exact hear₀ _

/-- When `d` starts from a cycle, `d.toVertexStart` starts at the cycle's base vertex and its first
ear is the closed ear formed by that initial cycle. -/
theorem exists_cycle_earAt_toVertexStart_zero {d : G.EarDecomposition H} (h : d.start.IsCycle) :
    ∃ (s : α) (walk : G.Walk s s) (isCycle : walk.IsCycle),
      d.initial = G.walkGraph walk ∧ d.toVertexStart.initial = Graph.noEdge {s} β ∧
      d.toVertexStart.earAt
        (Fin.cast (d.length_toVertexStart_of_isCycle h).symm (Fin.castAdd d.length 0)) =
        ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ := by
  obtain ⟨s, walk, isCycle, hK, hheq⟩ := EarStart.exists_cycle_of_isCycle h
  obtain ⟨hinit₀, _⟩ := toVertexDecomposition_of_heq_cycle d.start hK hheq
  exact ⟨s, walk, isCycle, d.initial_eq_graphAfter.trans hK, d.initial_toVertexStart.trans hinit₀,
    d.earAt_toVertexStart_zero_of_heq_cycle hK hheq _ (by simp)⟩

/-- Normalizing a single-cycle decomposition sets its initial graph to the cycle's base vertex. -/
theorem initial_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).toVertexStart.initial = Graph.noEdge {s} β :=
  (cycle walk isCycle).initial_toVertexStart.trans
    (toVertexDecomposition_of_heq_cycle (cycle walk isCycle).start
      (graphAfter_cycle_zero walk isCycle) (heq_start_cycle walk isCycle)).1

@[simp]
theorem length_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (cycle walk isCycle).toVertexStart.length = 1 := by
  simp [length_toVertexStart]

/-- Normalizing a single-cycle decomposition yields `Ear.ofIsCycle` as its unique ear. -/
@[simp]
theorem earAt_toVertexStart_cycle {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle)
    (i : Fin (cycle walk isCycle).toVertexStart.length) :
    (cycle walk isCycle).toVertexStart.earAt i =
      ⟨Graph.noEdge {s} β, Ear.ofIsCycle walk isCycle⟩ :=
  (cycle walk isCycle).earAt_toVertexStart_zero_of_heq_cycle
    (graphAfter_cycle_zero walk isCycle) (heq_start_cycle walk isCycle) i
    (Nat.lt_one_iff.mp (i.isLt.trans_eq (length_toVertexStart_cycle walk isCycle)))

end EarDecomposition

/-- A subgraph admits an ear decomposition if and only if it admits one starting from a single
vertex. -/
theorem nonempty_earDecomposition_iff_exists_isVertexStart {G H : Graph α β} :
    Nonempty (G.EarDecomposition H) ↔ ∃ d : G.EarDecomposition H, d.IsVertexStart :=
  ⟨fun ⟨d⟩ ↦ ⟨d.toVertexStart, d.isVertexStart_toVertexStart⟩, fun ⟨d, _⟩ ↦ ⟨d⟩⟩

end Graph
