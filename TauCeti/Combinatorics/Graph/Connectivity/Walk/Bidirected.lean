/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic
public import TauCeti.Combinatorics.Network.Walk
public import Mathlib.Data.Fintype.EquivFin

/-!
# Multigraph walks as directed walks of the bidirected arrow family

The *bidirected arrow family* `Graph.BidirectedHom G` of a multigraph `G : Graph α β` lives on its
actual vertices `V(G)`: the arrows from `x` to `y` are the edges `e` with `G.IsLink e x y`. A
nonloop edge therefore gives one arrow in each direction, a loop gives a single loop arrow, and
parallel edges give distinct parallel arrows. Directed walks along this family
(`TauCeti.ArrowWalk`) are the objects on which the network theory runs: flows, residual
reachability, and the directed forms of Menger's theorem.

This file identifies the edge-labelled walks of `G` between actual vertices with the directed
walks of its bidirected arrow family (`Graph.Walk.bidirectedEquiv`). The identification preserves
the length, the vertex sequence, and the edge sequence, hence paths. A directed cycle of the
bidirected family corresponds to an undirected cycle exactly when it traverses no edge twice: the
directed cycle `x → y → x` using the two opposite arrows of a single edge is not an undirected
cycle. In particular, reachability in `G` is reachability along the bidirected arrow family.

## Main definitions

* `Graph.BidirectedHom G`: the bidirected arrow family of `G`, on its actual vertices.
* `Graph.Walk.toBidirected`: a walk of `G` from an actual vertex as a directed walk.
* `TauCeti.ArrowWalk.toGraphWalk`: a directed walk of the bidirected family as a walk of `G`.
* `Graph.Walk.bidirectedEquiv`: these maps are inverse equivalences.

## Main results

* `Graph.Walk.vertices_toBidirected` and `Graph.Walk.edges_toBidirected`: the identification
  preserves vertex and edge sequences.
* `Graph.Walk.isPath_toBidirected_iff`: it preserves and reflects paths.
* `Graph.Walk.isCycle_iff_isCycle_toBidirected_and_isTrail`: an undirected cycle is a directed
  cycle that is a trail.
* `Graph.reachable_iff_nonempty_arrowWalk`: reachability between actual vertices is reachability
  along the bidirected arrow family.
-/

public section

open TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} (G : Graph α β)

/-- The bidirected arrow family of a multigraph on its actual vertices: the arrows from `x` to `y`
are the edges linking `x` to `y`. A nonloop edge gives one arrow in each direction and a loop gives
a single loop arrow. -/
abbrev BidirectedHom (x y : V(G)) : Type v :=
  {e : β // G.IsLink e x y}

/-- A multigraph with finitely many actual edges has finitely many arrows between any two
vertices of its bidirected arrow family. -/
instance [Finite E(G)] (x y : V(G)) : Finite (G.BidirectedHom x y) :=
  Finite.of_injective (fun e ↦ (⟨e.1, e.2.edge_mem⟩ : E(G))) fun _ _ h ↦
    Subtype.ext (Subtype.mk.inj h)

variable {G}

/-- The arrow of the bidirected arrow family given by an edge linking `x` to `y`. -/
abbrev IsLink.toBidirectedHom {e : β} {x y : α} (h : G.IsLink e x y) :
    G.BidirectedHom ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
  ⟨e, h⟩

namespace Walk

/-- A walk of `G` from an actual vertex, as a directed walk of the bidirected arrow family that
traverses the arrows given by the same edges in the same order. -/
def toBidirected : {x y : α} → (p : G.Walk x y) → (hx : x ∈ V(G)) →
    ArrowWalk G.BidirectedHom ⟨x, hx⟩ ⟨y, p.end_mem_vertexSet hx⟩
  | _, _, .nil, _ => ArrowWalk.nil _
  | _, _, .cons _ h p, _ =>
    ((ArrowWalk.nil _).cons h.toBidirectedHom).comp (p.toBidirected h.right_mem)

variable {x y z : α}

@[simp]
theorem toBidirected_nil (hx : x ∈ V(G)) :
    (nil : G.Walk x x).toBidirected hx = ArrowWalk.nil (Q := G.BidirectedHom) ⟨x, hx⟩ :=
  (rfl)

@[simp]
theorem toBidirected_cons {e : β} (h : G.IsLink e x y) (p : G.Walk y z) (hx : x ∈ V(G)) :
    (cons e h p).toBidirected hx =
      ((ArrowWalk.nil _).cons h.toBidirectedHom).comp (p.toBidirected h.right_mem) :=
  (rfl)

/-- The directed walk of a concatenation is the composite of the directed walks. -/
@[simp]
theorem toBidirected_append (p : G.Walk x y) (q : G.Walk y z) (hx : x ∈ V(G)) :
    (p.append q).toBidirected hx =
      (p.toBidirected hx).comp (q.toBidirected (p.end_mem_vertexSet hx)) := by
  induction p with
  | nil => rw [nil_append, toBidirected_nil]; exact (@Quiver.Path.nil_comp _ ⟨_⟩ _ _ _).symm
  | cons e h p ih =>
    rw [cons_append, toBidirected_cons, toBidirected_cons, ih]
    exact (@Quiver.Path.comp_assoc _ ⟨_⟩ _ _ _ _ _ _ _).symm

/-- The directed walk of a single edge is the single arrow given by that edge. -/
@[simp]
theorem _root_.Graph.IsLink.toBidirected_toWalk {e : β} (h : G.IsLink e x y) (hx : x ∈ V(G)) :
    h.toWalk.toBidirected hx = (ArrowWalk.nil _).cons h.toBidirectedHom := by
  rw [IsLink.toWalk_eq_cons]
  rfl

end Walk

end Graph

namespace TauCeti.ArrowWalk

open Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- A directed walk of the bidirected arrow family of `G`, as a walk of `G` traversing the edges
of its arrows in the same order. -/
def toGraphWalk {x : V(G)} : {y : V(G)} → ArrowWalk G.BidirectedHom x y → G.Walk x y
  | _, @Quiver.Path.nil _ .(_) _ => .nil
  | _, @Quiver.Path.cons _ .(_) _ _ _ q a => (toGraphWalk q).append a.2.toWalk

variable {x y z : V(G)}

@[simp]
theorem toGraphWalk_nil (x : V(G)) : (nil x : ArrowWalk G.BidirectedHom x x).toGraphWalk = .nil :=
  (rfl)

@[simp]
theorem toGraphWalk_cons (q : ArrowWalk G.BidirectedHom x y) (a : G.BidirectedHom y z) :
    (q.cons a).toGraphWalk = q.toGraphWalk.append a.2.toWalk :=
  (rfl)

/-- The walk of a composite directed walk is the concatenation of the walks. -/
@[simp]
theorem toGraphWalk_comp (q : ArrowWalk G.BidirectedHom x y) (r : ArrowWalk G.BidirectedHom y z) :
    (q.comp r).toGraphWalk = q.toGraphWalk.append r.toGraphWalk := by
  induction r with
  | nil => exact (Walk.append_nil _).symm
  | cons r a ih => simp [ih, Walk.append_assoc]

end TauCeti.ArrowWalk

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

namespace Walk

variable {x y z : α}

/-- Returning a walk from the bidirected arrow family recovers it. -/
@[simp]
theorem toGraphWalk_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) :
    (p.toBidirected hx).toGraphWalk = p := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih, IsLink.toWalk_eq_cons]

/-- Every directed walk of the bidirected arrow family is the directed walk of its walk in `G`. -/
@[simp]
theorem toBidirected_toGraphWalk {x y : V(G)} (q : ArrowWalk G.BidirectedHom x y) :
    q.toGraphWalk.toBidirected x.2 = q := by
  induction q with
  | nil => rfl
  | cons q a ih =>
    rw [ArrowWalk.toGraphWalk_cons]
    simp [ih]

variable (G) in
/-- The walks of `G` between two actual vertices are the directed walks of the bidirected arrow
family between them, with the same vertex and edge sequences. -/
def bidirectedEquiv (x y : V(G)) : G.Walk x y ≃ ArrowWalk G.BidirectedHom x y where
  toFun p := p.toBidirected x.2
  invFun q := q.toGraphWalk
  left_inv p := toGraphWalk_toBidirected p x.2
  right_inv := toBidirected_toGraphWalk

@[simp]
theorem bidirectedEquiv_apply {x y : V(G)} (p : G.Walk x y) :
    bidirectedEquiv G x y p = p.toBidirected x.2 :=
  (rfl)

@[simp]
theorem bidirectedEquiv_symm_apply {x y : V(G)} (q : ArrowWalk G.BidirectedHom x y) :
    (bidirectedEquiv G x y).symm q = q.toGraphWalk :=
  (rfl)

/-! ### Transport of lengths, vertices, edges, paths, and cycles -/

/-- The directed walk has the same length as the walk. -/
@[simp]
theorem length_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) :
    (p.toBidirected hx).length = p.length := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, add_comm]

/-- The directed walk visits the vertices of the walk in the same order. -/
@[simp]
theorem vertices_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) :
    (p.toBidirected hx).vertices.unattach = p.support := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih]

/-- The arrows of the directed walk are the edges of the walk, in the same order. -/
@[simp]
theorem edges_toBidirected (p : G.Walk x y) (hx : x ∈ V(G)) :
    (p.toBidirected hx).arrows.map (fun a ↦ a.2.2.1) = p.edges := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih]

/-- The directed walk is a directed path exactly when the walk is a path. -/
@[simp]
theorem isPath_toBidirected_iff (p : G.Walk x y) (hx : x ∈ V(G)) :
    (p.toBidirected hx).IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, isPath_def, ← vertices_toBidirected p hx, List.unattach,
    List.nodup_map_iff Subtype.val_injective]

/-- A closed walk is an undirected cycle exactly when its directed walk is a directed cycle and it
traverses no edge twice. -/
theorem isCycle_iff_isCycle_toBidirected_and_isTrail (p : G.Walk x x) (hx : x ∈ V(G)) :
    p.IsCycle ↔ (p.toBidirected hx).IsCycle ∧ p.IsTrail := by
  have htail : (p.toBidirected hx).vertices.tail.Nodup ↔ p.support.tail.Nodup := by
    rw [← vertices_toBidirected p hx, List.unattach, ← List.map_tail,
      List.nodup_map_iff Subtype.val_injective]
  simp only [isCycle_def, ArrowWalk.isCycle_def, htail, length_toBidirected, Nat.pos_iff_ne_zero,
    ne_eq, length_eq_zero_iff, ← eq_nil_iff_nil, isTrail_def]
  tauto

end Walk

end Graph

namespace TauCeti.ArrowWalk

open Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {x y : V(G)}

/-- The walk of a directed walk has the same length as the directed walk. -/
@[simp]
theorem length_toGraphWalk (q : ArrowWalk G.BidirectedHom x y) :
    q.toGraphWalk.length = q.length := by
  conv_rhs => rw [← Walk.toBidirected_toGraphWalk q]
  rw [Walk.length_toBidirected]

/-- The walk of a directed walk visits its vertices in the same order. -/
@[simp]
theorem support_toGraphWalk (q : ArrowWalk G.BidirectedHom x y) :
    q.toGraphWalk.support = q.vertices.unattach := by
  conv_rhs => rw [← Walk.toBidirected_toGraphWalk q]
  rw [Walk.vertices_toBidirected]

/-- The edges of the walk of a directed walk are the edges of its arrows, in the same order. -/
@[simp]
theorem edges_toGraphWalk (q : ArrowWalk G.BidirectedHom x y) :
    q.toGraphWalk.edges = q.arrows.map (fun a ↦ a.2.2.1) := by
  conv_rhs => rw [← Walk.toBidirected_toGraphWalk q]
  rw [Walk.edges_toBidirected]

/-- The walk of a directed walk is a path exactly when the directed walk is a directed path. -/
@[simp]
theorem isPath_toGraphWalk_iff (q : ArrowWalk G.BidirectedHom x y) :
    q.toGraphWalk.IsPath ↔ q.IsPath := by
  conv_rhs => rw [← Walk.toBidirected_toGraphWalk q]
  rw [Walk.isPath_toBidirected_iff]

/-- A directed cycle of the bidirected arrow family is an undirected cycle exactly when no two of
its arrows come from the same edge. -/
theorem isCycle_toGraphWalk_iff {x : V(G)} (q : ArrowWalk G.BidirectedHom x x) :
    q.toGraphWalk.IsCycle ↔ q.IsCycle ∧ (q.arrows.map fun a ↦ a.2.2.1).Nodup := by
  rw [Walk.isCycle_iff_isCycle_toBidirected_and_isTrail _ x.2, Walk.toBidirected_toGraphWalk,
    Walk.isTrail_def, edges_toGraphWalk]

end TauCeti.ArrowWalk

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Two actual vertices are reachable in `G` exactly when a directed walk of the bidirected arrow
family joins them. -/
theorem reachable_iff_nonempty_arrowWalk (x y : V(G)) :
    G.Reachable x y ↔ Nonempty (ArrowWalk G.BidirectedHom x y) := by
  rw [reachable_def, (Walk.bidirectedEquiv G x y).nonempty_congr]
  exact and_iff_right x.2

end Graph
