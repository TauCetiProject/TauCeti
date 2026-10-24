/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

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

/-- An edge-labelled walk in a multigraph. Each step records an edge together with its
incidence; a zero-length walk may be based at any ambient point. -/
inductive Walk (G : Graph α β) : α → α → Type (max u v)
  | nil {x : α} : Walk G x x
  | cons {x y z : α} (e : β) (h : G.IsLink e x y) (p : Walk G y z) :
      Walk G x z

attribute [refl] Walk.nil

namespace Walk

variable {x y z w : α}

/-- Pattern for a length-zero walk with its vertex explicit. -/
@[match_pattern]
abbrev nil' (x : α) : G.Walk x x := .nil

/-- Pattern for a nonempty walk with all three vertices explicit. -/
@[match_pattern]
abbrev cons' (x y z : α) (e : β) (h : G.IsLink e x y)
    (p : G.Walk y z) : G.Walk x z := .cons e h p

instance (x : α) : Inhabited (G.Walk x x) := ⟨.nil⟩

/-- The one-edge walk associated to an edge linking two vertices. -/
def _root_.Graph.IsLink.toWalk {e : β} (h : G.IsLink e x y) : G.Walk x y :=
  .cons e h .nil

/-- A one-edge walk is the corresponding `cons` followed by the empty walk. -/
theorem _root_.Graph.IsLink.toWalk_eq_cons {e : β} (h : G.IsLink e x y) :
    h.toWalk = .cons e h .nil :=
  (rfl)

/-- The number of edge traversals in a walk. -/
def length {x y : α} : G.Walk x y → ℕ
  | .nil => 0
  | .cons _ _ p => p.length + 1

/-- The vertices visited by a walk, in order and including both endpoints. -/
def support {x y : α} : G.Walk x y → List α
  | .nil => [x]
  | .cons _ _ p => x :: p.support

/-- The edges traversed by a walk, in order and with repetitions. -/
def edges {x y : α} : G.Walk x y → List β
  | .nil => []
  | .cons e _ p => e :: p.edges

@[simp, grind =]
theorem length_nil : (nil : G.Walk x x).length = 0 := (rfl)

@[simp, grind =]
theorem length_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons e h p).length = p.length + 1 := (rfl)

@[simp, grind =]
theorem support_nil : (nil : G.Walk x x).support = [x] := (rfl)

@[simp, grind =]
theorem support_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons e h p).support = x :: p.support := (rfl)

@[simp, grind =]
theorem edges_nil : (nil : G.Walk x x).edges = [] := (rfl)

@[simp, grind =]
theorem edges_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons e h p).edges = e :: p.edges := (rfl)

@[simp]
theorem _root_.Graph.IsLink.length_toWalk {e : β} (h : G.IsLink e x y) :
    (IsLink.toWalk h).length = 1 := (rfl)

@[simp]
theorem _root_.Graph.IsLink.support_toWalk {e : β} (h : G.IsLink e x y) :
    (IsLink.toWalk h).support = [x, y] := (rfl)

@[simp]
theorem _root_.Graph.IsLink.edges_toWalk {e : β} (h : G.IsLink e x y) :
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

theorem mem_support_iff {a : α} (p : G.Walk x y) :
    a ∈ p.support ↔ a = x ∨ a ∈ p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support (p : G.Walk x y) : x ∈ p.support := by
  cases p <;> simp

@[simp]
theorem end_mem_support (p : G.Walk x y) : y ∈ p.support := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih]

@[simp, grind =]
theorem length_edges (p : G.Walk x y) : p.edges.length = p.length := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp, grind =]
theorem length_support (p : G.Walk x y) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih, Nat.add_assoc]

theorem eq_of_length_eq_zero {p : G.Walk x y} (hp : p.length = 0) : x = y := by
  cases p with
  | nil => rfl
  | cons e h p => simp at hp

/-- A walk is nil when it consists of no steps. -/
inductive Nil : {x y : α} → G.Walk x y → Prop
  | nil {x : α} : Nil (.nil : G.Walk x x)

@[simp, grind .]
theorem nil_nil : (nil : G.Walk x x).Nil := Nil.nil

@[simp]
theorem not_nil_cons {e : β} {h : G.IsLink e x y} {p : G.Walk y z} :
    ¬ (cons e h p).Nil := nofun

@[simp, grind .]
theorem length_eq_zero_iff {p : G.Walk x y} : p.length = 0 ↔ p.Nil := by
  cases p <;> simp

@[simp]
theorem edges_eq_nil {p : G.Walk x y} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

@[grind .]
protected theorem Nil.eq {p : G.Walk x y} : p.Nil → x = y
  | .nil => rfl

theorem nil_iff_support_eq {p : G.Walk x y} : p.Nil ↔ p.support = [x] := by
  cases p <;> simp

/-- A walk with definitionally equal endpoints is nil exactly when it equals `nil`. -/
@[simp]
theorem eq_nil_iff_nil {p : G.Walk x x} : p = nil ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

/-- Every edge traversed by a walk is an actual edge of the ambient graph. -/
theorem edges_subset_edgeSet (p : G.Walk x y) :
    ∀ ⦃e : β⦄, e ∈ p.edges → e ∈ E(G) := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      intro f hf
      simp only [edges_cons, List.mem_cons] at hf
      exact hf.elim (fun hfe => hfe ▸ h.edge_mem) (fun hfp => ih hfp)

/-- Every vertex on a walk starting at an actual vertex is an actual vertex of the ambient graph. -/
theorem support_subset_vertexSet (p : G.Walk x y) (hx : x ∈ V(G)) :
    ∀ a ∈ p.support, a ∈ V(G) := by
  induction p with
  | nil => simpa
  | @cons x y z e h p ih =>
      intro a ha
      simp only [support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hx
      · exact ih h.right_mem a ha

/-- Every vertex on a positive-length walk is an actual vertex of the ambient graph. -/
theorem support_subset_vertexSet_of_pos (p : G.Walk x y) (hp : 0 < p.length) :
    ∀ a ∈ p.support, a ∈ V(G) := by
  cases p with
  | nil => simp at hp
  | cons e h p => exact (cons e h p).support_subset_vertexSet h.left_mem

/-- An endpoint of an edge traversed by a walk occurs in the walk's support. -/
theorem mem_support_of_isLink_of_mem_edges (p : G.Walk x y) {a b : α} {e : β}
    (h : G.IsLink e a b) (he : e ∈ p.edges) : a ∈ p.support := by
  induction p with
  | nil => simp at he
  | @cons x' y' z' f hf p ih =>
      simp only [edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rcases h.left_eq_or_eq hf with ha | ha
        · simp [ha]
        · simp [ha]
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
def append {x y z : α} : G.Walk x y → G.Walk y z → G.Walk x z
  | .nil, q => q
  | .cons e h p, q => .cons e h (p.append q)

@[simp]
theorem nil_append (p : G.Walk x y) : (nil : G.Walk x x).append p = p := (rfl)

@[simp]
theorem cons_append (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
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

@[simp, grind =]
theorem length_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, Nat.add_assoc, Nat.add_comm]

@[simp, grind =]
theorem edges_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp, grind =]
theorem support_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p <;> cases q <;> simp_all

theorem support_append_eq_support_dropLast_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

/-- Auxiliary tail-recursive operation used to reverse a walk. -/
protected def reverseAux {x y z : α} : G.Walk x y → G.Walk x z → G.Walk y z
  | .nil, q => q
  | .cons e h p, q => p.reverseAux (.cons e h.symm q)

/-- A walk traversed backwards, retaining the same edge identities. -/
def reverse (p : G.Walk x y) : G.Walk y x := p.reverseAux .nil

@[simp]
theorem reverse_nil : (nil : G.Walk x x).reverse = nil := (rfl)

@[simp]
theorem _root_.Graph.IsLink.reverse_toWalk {e : β} (h : G.IsLink e x y) :
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
theorem reverse_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
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

@[simp, grind =]
theorem length_reverse (p : G.Walk x y) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp, grind =]
theorem edges_reverse (p : G.Walk x y) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [ih]

@[simp, grind =]
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

@[simp, grind =]
theorem isTrail_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    IsTrail (cons e h p) ↔ IsTrail p ∧ e ∉ p.edges := by
  simp [IsTrail, and_comm]

@[simp]
theorem isPath_nil : IsPath (nil : G.Walk x x) := by
  simp [IsPath]

@[simp, grind =]
theorem isPath_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    IsPath (cons e h p) ↔ IsPath p ∧ x ∉ p.support := by
  simp [IsPath, and_comm]

@[simp]
theorem cons_isCycle_iff (e : β) (h : G.IsLink e x y) (p : G.Walk y x) :
    IsCycle (cons e h p) ↔ p.IsPath ∧ e ∉ p.edges := by
  simp only [IsCycle, IsPath, edges_cons, List.nodup_cons, support_cons, List.tail_cons]
  have hp : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup p
  tauto

/-- Every path is a trail. -/
theorem IsPath.isTrail {p : G.Walk x y} (hp : p.IsPath) : p.IsTrail :=
  edges_nodup_of_support_nodup p hp

theorem IsPath.support_nodup {p : G.Walk x y} (hp : p.IsPath) : p.support.Nodup :=
  hp

@[simp]
theorem _root_.Graph.IsLink.isPath_toWalk_iff {e : β} (h : G.IsLink e x y) :
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

theorem IsCycle.not_nil {p : G.Walk x x} (hp : p.IsCycle) : ¬ p.Nil :=
  fun h => hp.ne_nil h.eq_nil

theorem IsCycle.support_tail_nodup {p : G.Walk x x} (hp : p.IsCycle) :
    p.support.tail.Nodup := hp.2.2

@[simp]
theorem _root_.Graph.IsLink.isCycle_toWalk {e : β} (h : G.IsLink e x x) :
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

/-- Two ambient points are reachable when the first is an actual vertex and an edge-labelled
walk joins them. The endpoint is then automatically an actual vertex as well. -/
def Reachable (G : Graph α β) (x y : α) : Prop := x ∈ V(G) ∧ Nonempty (G.Walk x y)

theorem reachable_def {x y : α} :
    G.Reachable x y ↔ x ∈ V(G) ∧ Nonempty (G.Walk x y) := (Iff.rfl)

namespace Walk

theorem end_mem_vertexSet {x y : α} (p : G.Walk x y) (hx : x ∈ V(G)) : y ∈ V(G) := by
  induction p with
  | nil => exact hx
  | cons e h p ih => exact ih h.right_mem

/-- A walk starting at an actual vertex witnesses reachability. -/
theorem reachable {x y : α} (p : G.Walk x y) (hx : x ∈ V(G)) : G.Reachable x y :=
  ⟨hx, ⟨p⟩⟩

end Walk

/-- The endpoints of a link are reachable. -/
theorem IsLink.reachable {x y : α} {e : β} (h : G.IsLink e x y) : G.Reachable x y :=
  h.toWalk.reachable h.left_mem

namespace Reachable

variable {x y z : α}

theorem left_mem (h : G.Reachable x y) : x ∈ V(G) := h.1

theorem right_mem (h : G.Reachable x y) : y ∈ V(G) := by
  rcases h with ⟨hx, ⟨p⟩⟩
  exact p.end_mem_vertexSet hx

protected theorem elim {p : Prop} (h : G.Reachable x y) (hp : G.Walk x y → p) : p :=
  Nonempty.elim h.2 hp

/-- Every actual vertex is reachable from itself. -/
@[refl]
theorem refl (hx : x ∈ V(G)) : G.Reachable x x := ⟨hx, ⟨.nil⟩⟩

/-- Multigraph reachability is symmetric. -/
@[symm]
theorem symm (h : G.Reachable x y) : G.Reachable y x := by
  rcases h with ⟨hx, ⟨p⟩⟩
  exact ⟨p.end_mem_vertexSet hx, ⟨p.reverse⟩⟩

/-- Multigraph reachability is transitive. -/
@[trans]
theorem trans (hxy : G.Reachable x y) (hyz : G.Reachable y z) : G.Reachable x z := by
  rcases hxy with ⟨hx, ⟨p⟩⟩
  rcases hyz with ⟨_, ⟨q⟩⟩
  exact ⟨hx, ⟨p.append q⟩⟩

end Reachable

/-- A point is reachable from itself exactly when it is an actual vertex. -/
@[simp]
theorem reachable_self_iff {x : α} : G.Reachable x x ↔ x ∈ V(G) :=
  ⟨Reachable.left_mem, Reachable.refl⟩

/-- Reachability is an equivalence relation on the actual vertices of a graph. -/
theorem reachable_is_equivalence (G : Graph α β) :
    Equivalence (fun x y : V(G) => G.Reachable x y) :=
  ⟨fun x => Reachable.refl x.property, Reachable.symm, Reachable.trans⟩

/-- Membership in a closed subgraph propagates along reachability. -/
theorem IsClosedSubgraph.mem_vertexSet_of_reachable {H : Graph α β} (hHG : H ≤c G) {x y : α}
    (hx : x ∈ V(H)) (hxy : G.Reachable x y) : y ∈ V(H) := by
  obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp hxy
  clear hxy
  induction p with
  | nil => exact hx
  | cons e hxy p ih => exact ih ((hHG.mem_iff_of_isLink hxy).mp hx)

end Graph
