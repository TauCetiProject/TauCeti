/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic
public import TauCeti.Combinatorics.Network.Walk

/-!
# Multigraph walks and bidirected paths

The bidirected arrow family of a multigraph has one arrow from `s` to `t` for each edge
linking them. Its vertices are the actual vertices of the graph. In particular, distinct
parallel edges remain distinct arrows, and a loop gives just one arrow at its vertex.

`Graph.walkEquivBidirected` identifies edge-labelled graph walks with directed walks in this
family, using the existing `TauCeti.ArrowWalk` interface to Mathlib's `Quiver.Path`. It preserves
length, vertex and underlying edge sequences, concatenation, and paths. A directed cycle
corresponds to an undirected cycle precisely when its underlying edge sequence has no
repetitions: the two opposite arrows of a single nonloop edge do not form an undirected cycle.

The constructions follow Mathlib's `Quiver.Path` and the edge-labelled `Graph.Walk` API.
-/

public section

universe u v

namespace Graph

open TauCeti

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The bidirected arrows between actual vertices retain exactly their linking edge identities.
A loop contributes one arrow, with no additional direction tag. -/
abbrev BidirectedHom (G : Graph α β) (s t : V(G)) : Type v :=
  {e : β // G.IsLink e s t}

namespace Walk

variable {x y z : α}

/-- View a graph walk with actual endpoints as a directed walk in the bidirected family. -/
def toBidirected : {x y : α} → (p : G.Walk x y) →
    (hx : x ∈ V(G)) → (hy : y ∈ V(G)) →
    ArrowWalk G.BidirectedHom ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _ => .nil _
  | _, _, .cons e h p, hx, hy =>
      ((ArrowWalk.nil ⟨_, hx⟩).cons
        (⟨e, h⟩ : G.BidirectedHom ⟨_, hx⟩ ⟨_, h.right_mem⟩)).comp
          (p.toBidirected h.right_mem hy)

@[simp]
theorem toBidirected_nil (hx hy : x ∈ V(G)) :
    (nil : G.Walk x x).toBidirected hx hy = ArrowWalk.nil (⟨x, hx⟩ : V(G)) := (rfl)

@[simp]
theorem toBidirected_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toBidirected hx hz =
      ((ArrowWalk.nil ⟨x, hx⟩).cons (⟨e, h⟩ : G.BidirectedHom ⟨x, hx⟩ ⟨y, h.right_mem⟩)).comp
        (p.toBidirected h.right_mem hz) := (rfl)

/-- Recover the underlying graph walk from a bidirected walk. -/
def ofBidirected {s : V(G)} : {t : V(G)} → ArrowWalk G.BidirectedHom s t → G.Walk s t
  | _, @Quiver.Path.nil _ .(_) _ => .nil
  | _, @Quiver.Path.cons _ .(_) _ _ _ p e => (ofBidirected p).append e.property.toWalk

@[simp]
theorem ofBidirected_nil (s : V(G)) :
    ofBidirected (ArrowWalk.nil s : ArrowWalk G.BidirectedHom s s) = nil := (rfl)

@[simp]
theorem ofBidirected_cons {s t r : V(G)} (p : ArrowWalk G.BidirectedHom s t)
    (e : G.BidirectedHom t r) :
    ofBidirected (p.cons e) = (ofBidirected p).append e.property.toWalk := (rfl)

@[simp]
theorem ofBidirected_comp {s t r : V(G)} (p : ArrowWalk G.BidirectedHom s t)
    (q : ArrowWalk G.BidirectedHom t r) :
    ofBidirected (p.comp q) = (ofBidirected p).append (ofBidirected q) := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, append_assoc]

@[simp]
theorem toBidirected_append (p : G.Walk x y) (q : G.Walk y z)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hz : z ∈ V(G)) :
    (p.append q).toBidirected hx hz =
      (p.toBidirected hx hy).comp (q.toBidirected hy hz) := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih q h.right_mem hy, Quiver.Path.comp_assoc]

@[simp]
theorem ofBidirected_toBidirected (p : G.Walk x y) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : ofBidirected (p.toBidirected hx hy) = p := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, IsLink.toWalk_eq_cons]

@[simp]
theorem toBidirected_ofBidirected {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (ofBidirected p).toBidirected s.property t.property = p := by
  induction p with
  | nil => simp
  | cons p e ih => simp [IsLink.toWalk_eq_cons, ih]

@[simp]
theorem length_ofBidirected {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (ofBidirected p).length = p.length := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

/-- Forgetting the actual-vertex subtype gives precisely the graph walk's support. -/
@[simp]
theorem support_ofBidirected {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (ofBidirected p).support = p.vertices.unattach := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, ArrowWalk.vertices]

/-- Projecting the arrows to their underlying identities gives precisely the graph edge list. -/
@[simp]
theorem edges_ofBidirected {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (ofBidirected p).edges = p.arrows.map (fun a ↦ a.2.2.val) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

@[simp]
theorem length_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBidirected hx hy).length = p.length := by
  simpa only [ofBidirected_toBidirected] using (length_ofBidirected (p.toBidirected hx hy)).symm

@[simp]
theorem unattach_vertices_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBidirected hx hy).vertices.unattach = p.support := by
  simpa only [ofBidirected_toBidirected] using (support_ofBidirected (p.toBidirected hx hy)).symm

@[simp]
theorem map_arrows_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBidirected hx hy).arrows.map (fun a ↦ a.2.2.val) = p.edges := by
  simpa only [ofBidirected_toBidirected] using (edges_ofBidirected (p.toBidirected hx hy)).symm

/-- The walk correspondence preserves and reflects simple paths. -/
@[simp]
theorem isPath_ofBidirected_iff {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (ofBidirected p).IsPath ↔ p.IsPath := by
  rw [isPath_def, ArrowWalk.isPath_def, support_ofBidirected, List.unattach,
    List.nodup_map_iff Subtype.val_injective]

@[simp]
theorem isPath_toBidirected_iff (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBidirected hx hy).IsPath ↔ p.IsPath := by
  simpa only [ofBidirected_toBidirected] using
    (isPath_ofBidirected_iff (p.toBidirected hx hy)).symm

/-- A directed bidirected cycle is an undirected cycle exactly when no underlying edge repeats.
The additional condition excludes going out and back along one undirected edge. -/
theorem isCycle_ofBidirected_iff {s : V(G)} (p : ArrowWalk G.BidirectedHom s s) :
    (ofBidirected p).IsCycle ↔ p.IsCycle ∧ (p.arrows.map (fun a ↦ a.2.2.val)).Nodup := by
  have hpos : ofBidirected p ≠ nil ↔ 0 < p.length := by
    rw [ne_eq, eq_nil_iff_nil, ← length_eq_zero_iff, length_ofBidirected,
      Nat.pos_iff_ne_zero]
  rw [isCycle_def, hpos, edges_ofBidirected, support_ofBidirected, List.unattach, ← List.map_tail,
    List.nodup_map_iff Subtype.val_injective, ArrowWalk.isCycle_def]
  tauto

/-- Directed cycles must additionally have distinct underlying undirected edge identities. -/
theorem isCycle_toBidirected_iff (p : G.Walk x x) (hx : x ∈ V(G)) :
    p.IsCycle ↔ (p.toBidirected hx hx).IsCycle ∧ p.edges.Nodup := by
  simpa only [ofBidirected_toBidirected, map_arrows_toBidirected] using
    isCycle_ofBidirected_iff (p.toBidirected hx hx)

end Walk

/-- Edge-labelled walks between actual vertices are exactly directed walks in the bidirected
quiver. -/
def walkEquivBidirected (G : Graph α β) (s t : V(G)) :
    G.Walk s t ≃ ArrowWalk G.BidirectedHom s t where
  toFun p := p.toBidirected s.property t.property
  invFun := Walk.ofBidirected
  left_inv p := p.ofBidirected_toBidirected s.property t.property
  right_inv := Walk.toBidirected_ofBidirected

@[simp]
theorem walkEquivBidirected_apply {s t : V(G)} (p : G.Walk s t) :
    G.walkEquivBidirected s t p = p.toBidirected s.property t.property := (rfl)

@[simp]
theorem walkEquivBidirected_symm_apply {s t : V(G)} (p : ArrowWalk G.BidirectedHom s t) :
    (G.walkEquivBidirected s t).symm p = Walk.ofBidirected p := (rfl)

/-- Graph reachability between actual vertices agrees with bidirected reachability. -/
theorem reachable_iff_nonempty_bidirectedWalk {s t : V(G)} :
    G.Reachable s t ↔ Nonempty (ArrowWalk G.BidirectedHom s t) := by
  rw [reachable_def, and_iff_right s.property]
  exact (G.walkEquivBidirected s t).nonempty_congr

end Graph
