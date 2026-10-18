/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Walks in multigraphs

This file defines edge-labelled walks in Mathlib's `Graph`.  Unlike walks in a simple graph, a
walk records the identity of each edge it traverses.  Thus parallel edges give distinct walks,
while a loop has one length-one traversal.  The basic API includes vertex and edge lists,
concatenation, reversal, paths, cycles, and the induced reachability relation.

The interface follows Mathlib's `SimpleGraph.Walk`, adapted so that walks retain actual multigraph
edge identities.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- An edge-labelled walk in a multigraph.  Its endpoints are actual vertices of the graph and
each step records an actual edge together with its incidence. -/
inductive Walk (G : Graph α β) : V(G) → V(G) → Type (max u v)
  | nil {x : V(G)} : Walk G x x
  | cons {x y z : V(G)} (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : Walk G y z) :
      Walk G x z

attribute [refl] Walk.nil

namespace Walk

variable {x y z w : V(G)}

/-- Pattern for a length-zero walk with its vertex explicit. -/
@[match_pattern]
abbrev nil' (x : V(G)) : G.Walk x x := .nil

/-- Pattern for a nonempty walk with all three vertices explicit. -/
@[match_pattern]
abbrev cons' (x y z : V(G)) (e : E(G)) (h : G.IsLink e.1 x.1 y.1)
    (p : G.Walk y z) : G.Walk x z := .cons e h p

instance (x : V(G)) : Inhabited (G.Walk x x) := ⟨.nil⟩

/-- The one-edge walk associated to an edge linking two actual vertices. -/
def IsLink.toWalk {e : E(G)} (h : G.IsLink e.1 x.1 y.1) : G.Walk x y :=
  .cons e h .nil

/-- The number of edge traversals in a walk. -/
def length {x y : V(G)} : G.Walk x y → ℕ
  | .nil => 0
  | .cons _ _ p => p.length + 1

/-- The actual vertices visited by a walk, in order and including both endpoints. -/
def support {x y : V(G)} : G.Walk x y → List V(G)
  | .nil => [x]
  | .cons _ _ p => x :: p.support

/-- The actual edges traversed by a walk, in order and with repetitions. -/
def edges {x y : V(G)} : G.Walk x y → List E(G)
  | .nil => []
  | .cons e _ p => e :: p.edges

@[simp]
theorem length_nil : (nil : G.Walk x x).length = 0 := (rfl)

@[simp]
theorem length_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    (cons e h p).length = p.length + 1 := (rfl)

@[simp]
theorem support_nil : (nil : G.Walk x x).support = [x] := (rfl)

@[simp]
theorem support_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    (cons e h p).support = x :: p.support := (rfl)

@[simp]
theorem edges_nil : (nil : G.Walk x x).edges = [] := (rfl)

@[simp]
theorem edges_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    (cons e h p).edges = e :: p.edges := (rfl)

@[simp]
theorem _root_.Graph.IsLink.length_toWalk {e : E(G)} (h : G.IsLink e.1 x.1 y.1) :
    (IsLink.toWalk h).length = 1 := (rfl)

@[simp]
theorem _root_.Graph.IsLink.support_toWalk {e : E(G)} (h : G.IsLink e.1 x.1 y.1) :
    (IsLink.toWalk h).support = [x, y] := (rfl)

@[simp]
theorem _root_.Graph.IsLink.edges_toWalk {e : E(G)} (h : G.IsLink e.1 x.1 y.1) :
    (IsLink.toWalk h).edges = [e] := (rfl)

@[simp]
theorem support_ne_nil (p : G.Walk x y) : p.support ≠ [] := by
  cases p <;> simp

@[simp]
theorem head_support (p : G.Walk x y) : p.support.head (by simp) = x := by
  cases p <;> rfl

@[simp]
theorem getLast_support (p : G.Walk x y) : p.support.getLast (by simp) = y := by
  induction p with
  | nil => rfl
  | cons e h p ih => simpa using ih

@[simp]
theorem cons_tail_support (p : G.Walk x y) : x :: p.support.tail = p.support := by
  cases p <;> simp

@[simp]
theorem start_mem_support (p : G.Walk x y) : x ∈ p.support := by
  cases p <;> simp

@[simp]
theorem end_mem_support (p : G.Walk x y) : y ∈ p.support := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih]

@[simp]
theorem length_edges (p : G.Walk x y) : p.edges.length = p.length := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp]
theorem length_support (p : G.Walk x y) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih, Nat.add_assoc]

/-- An endpoint of an edge traversed by a walk occurs in the walk's support. -/
theorem mem_support_of_isLink_of_mem_edges (p : G.Walk x y) {a b : V(G)} {e : E(G)}
    (h : G.IsLink e.1 a.1 b.1) (he : e ∈ p.edges) : a ∈ p.support := by
  induction p with
  | nil => simp at he
  | @cons x' y' z' f hf p ih =>
      simp only [edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rcases h.left_eq_or_eq hf with ha | ha
        · have hax : a = x' := Subtype.ext ha
          simp [hax]
        · have hay : a = y' := Subtype.ext ha
          simp [hay]
      · simp [ih he]

/-- A walk with no repeated vertices also has no repeated edge identities. -/
theorem edges_nodup_of_support_nodup (p : G.Walk x y) (hp : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      rw [support_cons, List.nodup_cons] at hp
      rw [edges_cons, List.nodup_cons]
      exact ⟨fun he => hp.1 (p.mem_support_of_isLink_of_mem_edges h he), ih hp.2⟩

/-- Concatenation of two walks whose adjacent endpoints agree. -/
def append {x y z : V(G)} : G.Walk x y → G.Walk y z → G.Walk x z
  | .nil, q => q
  | .cons e h p, q => .cons e h (p.append q)

@[simp]
theorem nil_append (p : G.Walk x y) : (nil : G.Walk x x).append p = p := (rfl)

@[simp]
theorem cons_append (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z)
    (q : G.Walk z w) : (cons e h p).append q = cons e h (p.append q) := (rfl)

@[simp]
theorem append_nil (p : G.Walk x y) : p.append (.nil : G.Walk y y) = p := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

theorem append_assoc (p : G.Walk x y) (q : G.Walk y z) (r : G.Walk z w) :
    p.append (q.append r) = (p.append q).append r := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp]
theorem length_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, Nat.add_assoc, Nat.add_comm]

@[simp]
theorem edges_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp]
theorem support_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p <;> cases q <;> simp_all

theorem support_append_eq_dropLast_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

/-- Auxiliary tail-recursive operation used to reverse a walk. -/
protected def reverseAux {x y z : V(G)} : G.Walk x y → G.Walk x z → G.Walk y z
  | .nil, q => q
  | .cons e h p, q => p.reverseAux (.cons e h.symm q)

/-- A walk traversed backwards, retaining the same edge identities. -/
def reverse (p : G.Walk x y) : G.Walk y x := p.reverseAux .nil

@[simp]
theorem reverse_nil : (nil : G.Walk x x).reverse = nil := (rfl)

@[simp]
theorem _root_.Graph.IsLink.reverse_toWalk {e : E(G)} (h : G.IsLink e.1 x.1 y.1) :
    (IsLink.toWalk h).reverse = IsLink.toWalk h.symm := (rfl)

@[simp]
theorem reverseAux_append (p : G.Walk x y) (q : G.Walk x z) (r : G.Walk z w) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [Walk.reverseAux, ih]

@[simp]
theorem append_reverseAux (p : G.Walk x y) (q : G.Walk y z) (r : G.Walk x w) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [Walk.reverseAux, ih]

theorem reverseAux_eq_reverse_append (p : G.Walk x y) (q : G.Walk x z) :
    p.reverseAux q = p.reverse.append q := by
  simp [reverse]

@[simp]
theorem reverse_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    (cons e h p).reverse = p.reverse.append (IsLink.toWalk h.symm) := by
  simp [reverse, Walk.reverseAux, IsLink.toWalk]

@[simp]
theorem reverse_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  simp [reverse]

@[simp]
theorem reverse_reverse (p : G.Walk x y) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih, IsLink.toWalk]

@[simp]
theorem length_reverse (p : G.Walk x y) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp]
theorem edges_reverse (p : G.Walk x y) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp]
theorem support_reverse (p : G.Walk x y) : p.reverse.support = p.support.reverse := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

theorem tail_support_perm_dropLast_support (p : G.Walk x x) :
    p.support.tail.Perm p.support.dropLast := by
  cases p with
  | nil => rfl
  | @cons _ y _ e h p =>
      rw [support_cons, List.tail_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]
      have heq : p.support.dropLast ++ [x] = p.support := by
        simpa only [getLast_support] using List.dropLast_append_getLast p.support_ne_nil
      have hperm : (p.support.dropLast ++ [x]).Perm ([x] ++ p.support.dropLast) :=
        List.perm_append_comm
      exact (List.Perm.of_eq heq.symm).trans hperm

/-- A trail is a walk that traverses no edge identity more than once. -/
def IsTrail (p : G.Walk x y) : Prop := p.edges.Nodup

/-- A path is a walk that visits no vertex more than once. -/
def IsPath (p : G.Walk x y) : Prop := p.support.Nodup

/-- A cycle is a nonempty closed trail whose only repeated vertex is its base vertex. -/
def IsCycle (p : G.Walk x x) : Prop :=
  p ≠ .nil ∧ p.edges.Nodup ∧ p.support.tail.Nodup

theorem isTrail_def (p : G.Walk x y) : p.IsTrail ↔ p.edges.Nodup := (Iff.rfl)

theorem isPath_def (p : G.Walk x y) : p.IsPath ↔ p.support.Nodup := (Iff.rfl)

theorem isCycle_def (p : G.Walk x x) :
    p.IsCycle ↔ p ≠ .nil ∧ p.edges.Nodup ∧ p.support.tail.Nodup := (Iff.rfl)

@[simp]
theorem isTrail_nil : IsTrail (nil : G.Walk x x) := by
  simp [IsTrail]

@[simp]
theorem isTrail_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    IsTrail (cons e h p) ↔ IsTrail p ∧ e ∉ p.edges := by
  simp [IsTrail, and_comm]

@[simp]
theorem isPath_nil : IsPath (nil : G.Walk x x) := by
  simp [IsPath]

@[simp]
theorem isPath_cons (e : E(G)) (h : G.IsLink e.1 x.1 y.1) (p : G.Walk y z) :
    IsPath (cons e h p) ↔ IsPath p ∧ x ∉ p.support := by
  simp [IsPath, and_comm]

/-- Every path is a trail. -/
theorem IsPath.isTrail {p : G.Walk x y} (hp : p.IsPath) : p.IsTrail :=
  edges_nodup_of_support_nodup p hp

theorem IsPath.support_nodup {p : G.Walk x y} (hp : p.IsPath) : p.support.Nodup :=
  hp

@[simp]
theorem _root_.Graph.IsLink.isPath_toWalk_iff {e : E(G)} (h : G.IsLink e.1 x.1 y.1) :
    (IsLink.toWalk h).IsPath ↔ x ≠ y := by
  simp [IsPath]

@[simp]
theorem isTrail_reverse (p : G.Walk x y) : IsTrail p.reverse ↔ IsTrail p := by
  simp [IsTrail]

@[simp]
theorem isPath_reverse (p : G.Walk x y) : IsPath p.reverse ↔ IsPath p := by
  simp [IsPath]

@[simp]
theorem not_isCycle_nil : ¬ IsCycle (nil : G.Walk x x) := by
  simp [IsCycle]

theorem IsCycle.isTrail {p : G.Walk x x} (hp : p.IsCycle) : p.IsTrail := hp.2.1

theorem IsCycle.ne_nil {p : G.Walk x x} (hp : p.IsCycle) : p ≠ .nil := hp.1

theorem IsCycle.support_tail_nodup {p : G.Walk x x} (hp : p.IsCycle) :
    p.support.tail.Nodup := hp.2.2

@[simp]
theorem _root_.Graph.IsLink.isCycle_toWalk {e : E(G)} (h : G.IsLink e.1 x.1 x.1) :
    (IsLink.toWalk h).IsCycle := by
  simp [IsCycle, IsLink.toWalk]

@[simp]
theorem isCycle_reverse (p : G.Walk x x) : p.reverse.IsCycle ↔ p.IsCycle := by
  have reverse_imp (q : G.Walk x x) (hq : q.IsCycle) : q.reverse.IsCycle := by
    refine ⟨fun hr => hq.ne_nil (by simpa using congrArg reverse hr), ?_, ?_⟩
    · simpa [IsTrail] using hq.isTrail
    · have hd : q.support.dropLast.Nodup :=
        (q.tail_support_perm_dropLast_support.nodup_iff).mp hq.2.2
      simpa only [support_reverse, List.tail_reverse, List.nodup_reverse] using hd
  exact ⟨fun hp => by simpa using reverse_imp p.reverse hp, reverse_imp p⟩

end Walk

/-- Two actual vertices are reachable when an edge-labelled walk joins them. -/
def Reachable (G : Graph α β) (x y : V(G)) : Prop := Nonempty (G.Walk x y)

theorem reachable_iff_nonempty_walk {x y : V(G)} :
    G.Reachable x y ↔ Nonempty (G.Walk x y) := (Iff.rfl)

namespace Reachable

variable {x y z : V(G)}

/-- Every actual vertex is reachable from itself. -/
@[refl]
theorem refl (x : V(G)) : G.Reachable x x := ⟨.nil⟩

/-- Multigraph reachability is symmetric. -/
@[symm]
theorem symm (h : G.Reachable x y) : G.Reachable y x :=
  h.map Walk.reverse

/-- Multigraph reachability is transitive. -/
@[trans]
theorem trans (hxy : G.Reachable x y) (hyz : G.Reachable y z) : G.Reachable x z :=
  Nonempty.map2 Walk.append hxy hyz

end Reachable

end Graph
