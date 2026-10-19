/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk
public import Mathlib.Data.List.Sublists

/-!
# Splitting multigraph walks and extracting paths

This file decomposes an edge-labelled multigraph walk at the first occurrence of a chosen
vertex. The two pieces recover the original walk, and their vertex and edge lists are respectively
a prefix and a suffix of the original lists. In particular, taking either piece of a path again
gives a path.

Repeated vertices can then be bypassed without changing the endpoints. The resulting walk is a
path whose vertices and edge identities are sublists of those of the original walk. Consequently,
multigraph reachability always has a path witness, while parallel edges remain distinguished.

The interface and proofs follow Mathlib's `SimpleGraph.Walk.takeUntil`, `dropUntil`, and `bypass`
API in `Mathlib.Combinatorics.SimpleGraph.Walk.Decomp` and
`Mathlib.Combinatorics.SimpleGraph.Paths`, adapted to edge-labelled walks.

## Main definitions

* `Graph.Walk.takeUntil` and `Graph.Walk.dropUntil` split a walk at the first occurrence of a
  vertex.
* `Graph.Walk.bypass` removes closed subwalks between repeated vertices.

## Main results

* `Graph.Walk.take_spec` reconstructs the original walk from the two pieces.
* `Graph.Walk.bypass_isPath` proves that bypassing repeated vertices gives a path.
* `Graph.Reachable.exists_isPath` extracts a path witness from reachability.
-/

public section

open scoped List

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β} {a x y z : α}

section Decomposition

variable [DecidableEq α]

/-- The initial part of a walk, ending at the first occurrence of a specified vertex. -/
def takeUntil {x y : α} : ∀ (p : G.Walk x y) (a : α), a ∈ p.support → G.Walk x a
  | .nil, a, ha => by
      have hax : a = x := by simpa only [support_nil, List.mem_singleton] using ha
      subst a
      exact .nil
  | .cons e h p, a, ha =>
      if hxa : x = a then
        hxa ▸ .nil
      else
        .cons e h (takeUntil p a <| by
          have ha' : a = x ∨ a ∈ p.support := by
            simpa only [support_cons, List.mem_cons] using ha
          exact ha'.resolve_left fun hax => hxa hax.symm)

/-- The terminal part of a walk, starting at the first occurrence of a specified vertex. -/
def dropUntil {x y : α} : ∀ (p : G.Walk x y) (a : α), a ∈ p.support → G.Walk a y
  | .nil, a, ha => by
      have hax : a = x := by simpa only [support_nil, List.mem_singleton] using ha
      subst a
      exact .nil
  | .cons e h p, a, ha =>
      if hxa : x = a then by
        subst a
        exact .cons e h p
      else
        dropUntil p a <| by
          have ha' : a = x ∨ a ∈ p.support := by
            simpa only [support_cons, List.mem_cons] using ha
          exact ha'.resolve_left fun hax => hxa hax.symm

@[simp]
theorem takeUntil_nil (ha : x ∈ (nil : G.Walk x x).support) :
    (nil : G.Walk x x).takeUntil x ha = .nil :=
  (rfl)

theorem takeUntil_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (ha : a ∈ p.support) (hxa : x ≠ a) :
    (cons e h p).takeUntil a (by simp [ha]) = cons e h (p.takeUntil a ha) := by
  simp [takeUntil, hxa]

theorem dropUntil_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (ha : a ∈ p.support) (hxa : x ≠ a) :
    (cons e h p).dropUntil a (by simp [ha]) = p.dropUntil a ha := by
  simp [dropUntil, hxa]

@[simp]
theorem takeUntil_first (p : G.Walk x y) :
    p.takeUntil x p.start_mem_support = .nil := by
  cases p <;> simp [takeUntil]

@[simp]
theorem dropUntil_first (p : G.Walk x y) (hx : x ∈ p.support) :
    p.dropUntil x hx = p := by
  cases p <;> simp [dropUntil]

/-- Splitting a walk at a visited vertex and concatenating the pieces recovers the walk. -/
@[simp]
theorem take_spec (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).append (p.dropUntil a ha) = p := by
  induction p with
  | nil =>
      simp only [support_nil, List.mem_singleton] at ha
      subst a
      simp only [takeUntil, dropUntil, nil_append]
  | @cons x y z e h p ih =>
      simp only [support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [takeUntil, dropUntil]
      · by_cases hxa : x = a
        · subst a
          simp [takeUntil, dropUntil]
        · simp [takeUntil, dropUntil, hxa, ih ha]

/-- The vertices of the initial piece form a prefix of the original vertex list. -/
theorem support_takeUntil_prefix_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).support <+: p.support := by
  calc
    (p.takeUntil a ha).support <+:
        ((p.takeUntil a ha).append (p.dropUntil a ha)).support := by
      rw [support_append]
      exact List.prefix_append _ _
    _ = p.support := congrArg support (p.take_spec ha)

/-- The vertices of the terminal piece form a suffix of the original vertex list. -/
theorem support_dropUntil_suffix_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).support <:+ p.support := by
  calc
    (p.dropUntil a ha).support <:+
        ((p.takeUntil a ha).append (p.dropUntil a ha)).support := by
      rw [support_append_eq_support_dropLast_append]
      exact List.suffix_append _ _
    _ = p.support := congrArg support (p.take_spec ha)

/-- The edges of the initial piece form a prefix of the original edge list. -/
theorem edges_takeUntil_prefix_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).edges <+: p.edges := by
  calc
    (p.takeUntil a ha).edges <+:
        ((p.takeUntil a ha).append (p.dropUntil a ha)).edges := by
      rw [edges_append]
      exact List.prefix_append _ _
    _ = p.edges := congrArg edges (p.take_spec ha)

/-- The edges of the terminal piece form a suffix of the original edge list. -/
theorem edges_dropUntil_suffix_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).edges <:+ p.edges := by
  calc
    (p.dropUntil a ha).edges <:+
        ((p.takeUntil a ha).append (p.dropUntil a ha)).edges := by
      rw [edges_append]
      exact List.suffix_append _ _
    _ = p.edges := congrArg edges (p.take_spec ha)

/-- Every vertex of the initial piece occurs in the original walk. -/
theorem support_takeUntil_subset_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).support ⊆ p.support :=
  (p.support_takeUntil_prefix_support ha).subset

/-- Every vertex of the terminal piece occurs in the original walk. -/
theorem support_dropUntil_subset_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).support ⊆ p.support :=
  (p.support_dropUntil_suffix_support ha).subset

/-- Every edge of the initial piece occurs in the original walk. -/
theorem edges_takeUntil_subset_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).edges ⊆ p.edges :=
  (p.edges_takeUntil_prefix_edges ha).subset

/-- Every edge of the terminal piece occurs in the original walk. -/
theorem edges_dropUntil_subset_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).edges ⊆ p.edges :=
  (p.edges_dropUntil_suffix_edges ha).subset

/-- An initial segment of a path is a path. -/
theorem IsPath.takeUntil {p : G.Walk x y} (hp : p.IsPath) (ha : a ∈ p.support) :
    (p.takeUntil a ha).IsPath := by
  rw [isPath_def] at hp ⊢
  exact (p.support_takeUntil_prefix_support ha).nodup hp

/-- A terminal segment of a path is a path. -/
theorem IsPath.dropUntil {p : G.Walk x y} (hp : p.IsPath) (ha : a ∈ p.support) :
    (p.dropUntil a ha).IsPath := by
  rw [isPath_def] at hp ⊢
  exact (p.support_dropUntil_suffix_support ha).nodup hp

end Decomposition

/-- A vertex occurs in a walk exactly when the walk can be split there. -/
theorem mem_support_iff_exists_append {p : G.Walk x y} :
    a ∈ p.support ↔ ∃ (q : G.Walk x a) (r : G.Walk a y), p = q.append r := by
  classical
  constructor
  · exact fun ha => ⟨p.takeUntil a ha, p.dropUntil a ha, (p.take_spec ha).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [support_append, List.mem_append, end_mem_support, true_or]

section PathExtraction

variable [DecidableEq α]

/-- Remove closed subwalks between repeated vertices. The result has the same endpoints; it is a
path by `Graph.Walk.bypass_isPath`. -/
def bypass {x y : α} : G.Walk x y → G.Walk x y
  | .nil => .nil
  | .cons e h p =>
      let p' := p.bypass
      if hx : x ∈ p'.support then
        p'.dropUntil x hx
      else
        .cons e h p'

/-- Bypassing repeated vertices always produces a path. -/
theorem bypass_isPath (p : G.Walk x y) : p.bypass.IsPath := by
  induction p with
  | nil => simp [bypass]
  | @cons x y z e h p ih =>
      simp only [bypass]
      split_ifs with hx
      · exact ih.dropUntil hx
      · simpa [isPath_cons, hx] using ih

/-- Bypassing only removes vertices from the walk, preserving their order. -/
theorem support_bypass_sublist_support (p : G.Walk x y) :
    p.bypass.support <+ p.support := by
  induction p with
  | nil => simp [bypass]
  | @cons x y z e h p ih =>
      simp only [bypass]
      split_ifs with hx
      · simpa only [support_cons] using
          ((p.bypass.support_dropUntil_suffix_support hx).sublist.trans ih).cons x
      · simpa only [support_cons] using ih.cons_cons x

/-- Bypassing only removes edge traversals from the walk, preserving their order and identities. -/
theorem edges_bypass_sublist_edges (p : G.Walk x y) :
    p.bypass.edges <+ p.edges := by
  induction p with
  | nil => simp [bypass]
  | @cons x y z e h p ih =>
      simp only [bypass]
      split_ifs with hx
      · simpa only [edges_cons] using
          ((p.bypass.edges_dropUntil_suffix_edges hx).sublist.trans ih).cons e
      · simpa only [edges_cons] using ih.cons_cons e

/-- Every vertex left after bypassing occurs in the original walk. -/
theorem support_bypass_subset_support (p : G.Walk x y) :
    p.bypass.support ⊆ p.support :=
  p.support_bypass_sublist_support.subset

/-- Every edge left after bypassing occurs in the original walk. -/
theorem edges_bypass_subset_edges (p : G.Walk x y) :
    p.bypass.edges ⊆ p.edges :=
  p.edges_bypass_sublist_edges.subset

/-- Bypassing repeated vertices cannot increase the length of a walk. -/
theorem length_bypass_le_length (p : G.Walk x y) : p.bypass.length ≤ p.length := by
  have h := p.support_bypass_sublist_support.length_le
  simpa only [length_support, Nat.add_le_add_iff_right] using h

/-- Bypassing a path changes nothing. -/
@[grind →]
theorem IsPath.bypass_eq_self {p : G.Walk x y} (hp : p.IsPath) : p.bypass = p := by
  induction p with
  | nil => rfl
  | @cons x y z e h p ih =>
      rw [isPath_cons] at hp
      simp [bypass, ih hp.1, hp.2]

/-- A walk is fixed by bypassing exactly when it is already a path. -/
@[simp]
theorem bypass_eq_self_iff_isPath {p : G.Walk x y} : p.bypass = p ↔ p.IsPath :=
  ⟨fun h => h ▸ p.bypass_isPath, IsPath.bypass_eq_self⟩

end PathExtraction

end Graph.Walk

namespace Graph.Reachable

variable {α : Type u} {β : Type v} {G : Graph α β} {x y : α}

/-- Every pair of reachable vertices is joined by a path retaining actual multigraph edge
identities. -/
theorem exists_isPath (h : G.Reachable x y) :
    ∃ p : G.Walk x y, p.IsPath := by
  classical
  exact h.elim fun p => ⟨p.bypass, p.bypass_isPath⟩

end Graph.Reachable
