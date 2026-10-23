/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.List.Chain

/-!
# Graphs with edge reversal

A Serre graph has directed edges paired by a fixed-point-free reversal. In particular, a loop
has two distinct orientations, and parallel edges remain distinct. `Path` records a list of
incident darts, `Path.IsReduced` excludes immediate reversal, and `Reachable` and `Connected`
describe path connectivity. `IsTree` excludes nonempty reduced closed paths. The point graph
and roses give basic examples. This is the combinatorial carrier for labelled subgroup graphs
and graphs of groups.

The definition follows Serre, *Trees*, Chapter I, §2.1.

-/

public section

namespace TauCeti

/-- A graph in the sense of Serre, with a fixed-point-free reversal of its directed edges. -/
structure SerreGraph where
  /-- Vertices. -/
  V : Type*
  /-- Directed edges, also called darts. -/
  E : Type*
  /-- Origin of a directed edge. -/
  src : E → V
  /-- Reversal of a directed edge. -/
  rev : E → E
  /-- Reversing twice fixes every edge. -/
  rev_rev : ∀ e, rev (rev e) = e
  /-- An edge is distinct from its reversal, even when it is a loop. -/
  rev_ne : ∀ e, rev e ≠ e

attribute [simp] SerreGraph.rev_rev
attribute [simp] SerreGraph.rev_ne

namespace SerreGraph

variable (Γ : SerreGraph)

/-- The terminus of an edge is the origin of its reverse. -/
def tgt (e : Γ.E) : Γ.V := Γ.src (Γ.rev e)

/-- The reverse dart starts at the original target. -/
@[simp] theorem src_rev (e : Γ.E) : Γ.src (Γ.rev e) = Γ.tgt e := (rfl)

/-- Reversing darts is an involution. -/
theorem rev_involutive : Function.Involutive Γ.rev := Γ.rev_rev

/-- Reversing darts is injective. -/
theorem rev_injective : Function.Injective Γ.rev := Γ.rev_involutive.injective

/-- Reversing two darts gives the same dart exactly when they were equal. -/
@[simp] theorem rev_inj {e f : Γ.E} : Γ.rev e = Γ.rev f ↔ e = f :=
  Γ.rev_injective.eq_iff

@[simp] theorem tgt_rev (e : Γ.E) : Γ.tgt (Γ.rev e) = Γ.src e := by
  simp only [tgt, Γ.rev_rev]

/-- A list of darts is a path from `u` to `v` when it can be traversed from `u` and ends at
`v`. The empty list is a path precisely when its endpoints agree. -/
def Valid (Γ : SerreGraph) : Γ.V → List Γ.E → Γ.V → Prop
  | u, [], v => u = v
  | u, e :: es, v => Γ.src e = u ∧ Γ.Valid (Γ.tgt e) es v

@[simp] theorem valid_nil (u v : Γ.V) : Γ.Valid u [] v ↔ u = v := Iff.rfl

@[simp] theorem valid_cons (u v : Γ.V) (e : Γ.E) (es : List Γ.E) :
    Γ.Valid u (e :: es) v ↔ Γ.src e = u ∧ Γ.Valid (Γ.tgt e) es v := Iff.rfl

/-- A concatenated edge list is valid exactly when both halves meet at some vertex. -/
theorem valid_append_iff (u w : Γ.V) (es fs : List Γ.E) :
    Γ.Valid u (es ++ fs) w ↔ ∃ v, Γ.Valid u es v ∧ Γ.Valid v fs w := by
  induction es generalizing u with
  | nil =>
      simp only [List.nil_append, valid_nil]
      constructor
      · intro h
        exact ⟨u, rfl, h⟩
      · rintro ⟨v, rfl, h⟩
        exact h
  | cons e es ih =>
      simp only [List.cons_append, valid_cons]
      constructor
      · rintro ⟨rfl, h⟩
        obtain ⟨v, h₁, h₂⟩ := (ih (Γ.tgt e)).mp h
        exact ⟨v, ⟨rfl, h₁⟩, h₂⟩
      · rintro ⟨v, ⟨rfl, h₁⟩, h₂⟩
        exact ⟨rfl, (ih (Γ.tgt e)).mpr ⟨v, h₁, h₂⟩⟩

/-- A directed edge path with specified endpoints. -/
structure Path (u v : Γ.V) where
  /-- The traversed darts. -/
  edges : List Γ.E
  /-- Incidence and endpoint conditions. -/
  valid : Γ.Valid u edges v

namespace Path

variable {Γ} {u v w : Γ.V}

@[ext] theorem ext {p q : Γ.Path u v} (h : p.edges = q.edges) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The empty path at a vertex. -/
def nil (u : Γ.V) : Γ.Path u u :=
  ⟨[], (Γ.valid_nil u u).mpr rfl⟩

@[simp] theorem edges_nil (u : Γ.V) : (nil u).edges = [] := (rfl)

/-- Prefix a path by a dart ending at its initial vertex. -/
def cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) : Γ.Path (Γ.src e) v :=
  ⟨e :: p.edges, (Γ.valid_cons (Γ.src e) v e p.edges).mpr ⟨rfl, p.valid⟩⟩

@[simp] theorem edges_cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    (cons e p).edges = e :: p.edges := (rfl)

/-- Induction on the edge list of a path, preserving the endpoints in each case. -/
@[elab_as_elim] theorem induction_on {motive : ∀ {u v}, Γ.Path u v → Prop}
    (p : Γ.Path u v) (hnil : ∀ u, motive (nil u))
    (hcons : ∀ (e : Γ.E) {v} (q : Γ.Path (Γ.tgt e) v),
      motive q → motive (cons e q)) : motive p := by
  obtain ⟨es, h⟩ := p
  induction es generalizing u with
  | nil =>
      have huv := (Γ.valid_nil u v).mp h
      subst v
      exact hnil u
  | cons e es ih =>
      obtain ⟨rfl, ht⟩ := (Γ.valid_cons u v e es).mp h
      exact hcons e ⟨es, ht⟩ (ih ht)

/-- The edge list of a concatenation satisfies the path incidence conditions. -/
theorem valid_append (p : Γ.Path u v) (q : Γ.Path v w) :
    Γ.Valid u (p.edges ++ q.edges) w :=
  (Γ.valid_append_iff u w p.edges q.edges).mpr ⟨v, p.valid, q.valid⟩

/-- Concatenation of directed paths. -/
def append (p : Γ.Path u v) (q : Γ.Path v w) : Γ.Path u w :=
  ⟨p.edges ++ q.edges, valid_append p q⟩

@[simp] theorem edges_append (p : Γ.Path u v) (q : Γ.Path v w) :
    (append p q).edges = p.edges ++ q.edges := (rfl)

@[simp] theorem nil_append (p : Γ.Path u v) : append (nil u) p = p := by
  ext
  simp

@[simp] theorem append_nil (p : Γ.Path u v) : append p (nil v) = p := by
  ext
  simp

/-- Path concatenation is associative. -/
@[simp]
theorem append_assoc (p : Γ.Path u v) (q : Γ.Path v w) {z : Γ.V}
    (r : Γ.Path w z) : append (append p q) r = append p (append q r) := by
  ext
  simp [List.append_assoc]

/-- Prefixing a concatenation is the same as prefixing its first path. -/
@[simp] theorem cons_append (e : Γ.E) (p : Γ.Path (Γ.tgt e) v)
    (q : Γ.Path v w) : (cons e p).append q = cons e (p.append q) := by
  ext
  simp

/-- Reversing and flipping every dart preserves the path incidence conditions. -/
theorem valid_reverse {es : List Γ.E} (h : Γ.Valid u es v) :
    Γ.Valid v (es.reverse.map Γ.rev) u := by
  induction es generalizing u with
  | nil =>
      simp only [valid_nil] at h ⊢
      exact h.symm
  | cons e es ih =>
      obtain ⟨rfl, ht⟩ := (Γ.valid_cons u v e es).mp h
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      have hstep : Γ.Valid (Γ.tgt e) [Γ.rev e] (Γ.src e) := by
        simp only [valid_cons, valid_nil, src_rev, tgt_rev, true_and]
      exact valid_append ⟨_, ih ht⟩ ⟨_, hstep⟩

/-- Reverse a path, reversing both the order and the orientation of its darts. -/
def reverse (p : Γ.Path u v) : Γ.Path v u :=
  ⟨p.edges.reverse.map Γ.rev, valid_reverse p.valid⟩

@[simp] theorem edges_reverse (p : Γ.Path u v) :
    p.reverse.edges = p.edges.reverse.map Γ.rev := (rfl)

/-- Reversing a path twice returns the original path. -/
@[simp] theorem reverse_reverse (p : Γ.Path u v) : p.reverse.reverse = p := by
  ext
  simp [List.map_map, Γ.rev_rev]

@[simp] theorem reverse_nil (u : Γ.V) : (nil u).reverse = nil u := by
  ext
  rfl

/-- Reversing a prefixed path moves its dart to the end with opposite orientation. -/
theorem edges_reverse_cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    (cons e p).reverse.edges = p.reverse.edges ++ [Γ.rev e] := by
  simp [List.reverse_cons, List.map_append]

/-- Reversal exchanges the order of concatenated paths. -/
@[simp] theorem reverse_append (p : Γ.Path u v) (q : Γ.Path v w) :
    (append p q).reverse = append q.reverse p.reverse := by
  ext
  simp [List.reverse_append, List.map_append]

/-- A path is reduced when no dart is immediately followed by its reverse. -/
def IsReduced (p : Γ.Path u v) : Prop :=
  p.edges.IsChain fun e f => f ≠ Γ.rev e

/-- Reducedness means that consecutive darts in the edge list do not cancel. -/
theorem isReduced_iff (p : Γ.Path u v) :
    p.IsReduced ↔ p.edges.IsChain (fun e f => f ≠ Γ.rev e) := Iff.rfl

/-- A prefixed path is reduced exactly when its tail is reduced and the first dart of the tail,
if any, is not the reverse of the prefix dart. -/
@[simp] theorem isReduced_cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    IsReduced (cons e p) ↔ p.IsReduced ∧ ∀ f ∈ p.edges.head?, f ≠ Γ.rev e := by
  simp only [IsReduced, edges_cons, List.isChain_cons, and_comm]

/-- Reversing a path preserves and reflects reducedness. -/
@[simp] theorem isReduced_reverse (p : Γ.Path u v) :
    p.reverse.IsReduced ↔ p.IsReduced := by
  simp only [IsReduced, edges_reverse, List.isChain_map, List.isChain_reverse]
  apply List.IsChain.iff
  intro e f
  simp only [Γ.rev_rev]
  exact ne_comm

/-- A concatenation is reduced when both paths are reduced and their junction does not cancel. -/
theorem isReduced_append (p : Γ.Path u v) (q : Γ.Path v w) :
    (p.append q).IsReduced ↔ p.IsReduced ∧ q.IsReduced ∧
      ∀ e ∈ p.edges.getLast?, ∀ f ∈ q.edges.head?, f ≠ Γ.rev e := by
  simp only [IsReduced, edges_append, List.isChain_append]

@[simp] theorem isReduced_nil (u : Γ.V) : IsReduced (nil u) := by
  simp [IsReduced]

theorem isReduced_single (e : Γ.E) :
    IsReduced (cons e (nil (Γ.tgt e))) := by
  simp [IsReduced]

end Path

/-- Two vertices are path-connected when a directed path joins them. -/
def Reachable (u v : Γ.V) : Prop := Nonempty (Γ.Path u v)

namespace Path

/-- A path witnesses reachability of its endpoints. -/
theorem reachable {u v : Γ.V} (p : Γ.Path u v) : Γ.Reachable u v := ⟨p⟩

end Path

/-- Two vertices are reachable exactly when a path joins them. -/
theorem reachable_iff_nonempty_path (u v : Γ.V) :
    Γ.Reachable u v ↔ Nonempty (Γ.Path u v) := Iff.rfl

namespace Reachable

/-- Every vertex is reachable from itself. -/
@[refl] protected theorem refl (u : Γ.V) : Γ.Reachable u u := ⟨Path.nil u⟩

/-- Reversing a path reverses reachability. -/
@[symm] protected theorem symm {u v : Γ.V} (h : Γ.Reachable u v) : Γ.Reachable v u :=
  h.elim fun p => ⟨p.reverse⟩

/-- Composing paths composes reachability. -/
@[trans] protected theorem trans {u v w : Γ.V} (huv : Γ.Reachable u v)
    (hvw : Γ.Reachable v w) : Γ.Reachable u w :=
  huv.elim fun p => hvw.elim fun q => ⟨p.append q⟩

end Reachable

/-- Path reachability is an equivalence relation on vertices. -/
theorem reachable_equivalence : Equivalence Γ.Reachable :=
  ⟨Reachable.refl Γ, Reachable.symm Γ, Reachable.trans Γ⟩

/-- The setoid whose classes are the path components. -/
def reachableSetoid : Setoid Γ.V := Setoid.mk Γ.Reachable Γ.reachable_equivalence

/-- The relation of the path component setoid is path reachability. -/
@[simp] theorem reachableSetoid_r (u v : Γ.V) :
    Γ.reachableSetoid.r u v ↔ Γ.Reachable u v := Iff.rfl

/-- Every pair of vertices is joined by a path. This holds vacuously for the empty graph. -/
def Preconnected : Prop := ∀ u v : Γ.V, Γ.Reachable u v

/-- Preconnectedness means reachability between every pair of vertices. -/
theorem preconnected_iff : Γ.Preconnected ↔ ∀ u v : Γ.V, Γ.Reachable u v := Iff.rfl

namespace Preconnected

/-- Any two vertices of a preconnected graph are reachable. -/
theorem reachable (h : Γ.Preconnected) (u v : Γ.V) : Γ.Reachable u v :=
  (Γ.preconnected_iff.mp h) u v

end Preconnected

/-- A Serre graph is connected when it has a vertex and any two vertices are joined. -/
def Connected : Prop := Nonempty Γ.V ∧ Γ.Preconnected

/-- Connectedness is nonemptiness together with preconnectedness. -/
theorem connected_iff : Γ.Connected ↔ Nonempty Γ.V ∧ Γ.Preconnected :=
  Iff.rfl

namespace Connected

/-- A connected graph has a vertex. -/
theorem nonempty (h : Γ.Connected) : Nonempty Γ.V := (Γ.connected_iff.mp h).1

/-- Any two vertices of a connected graph are reachable. -/
theorem preconnected (h : Γ.Connected) : Γ.Preconnected := (Γ.connected_iff.mp h).2

/-- A nonempty preconnected graph is connected. -/
theorem mk (hV : Nonempty Γ.V) (hconn : Γ.Preconnected) : Γ.Connected :=
  Γ.connected_iff.mpr ⟨hV, hconn⟩

end Connected

/-- A tree is a nonempty connected Serre graph with no nonempty reduced closed path.
This uses the reduced-closed-path formulation in place of Serre's no-circuits definition
in *Trees*, Chapter I, §2.2. -/
def IsTree : Prop :=
  Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), p.IsReduced → p.edges = []

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every reduced closed path in a tree is empty. -/
theorem edges_eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : p.IsReduced) : p.edges = [] := h.2 u p hp

end IsTree

/-- Unfolds `IsTree`. -/
theorem isTree_iff : Γ.IsTree ↔
    Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), p.IsReduced → p.edges = [] := Iff.rfl

/-- The Serre graph with one vertex and no edges. -/
abbrev point : SerreGraph where
  V := PUnit
  E := PEmpty
  src := PEmpty.elim
  rev := PEmpty.elim
  rev_rev := by intro e; exact e.elim
  rev_ne := by intro e; exact e.elim

/-- The graph with one vertex and no edges is a tree. -/
theorem single_vertex_isTree : point.IsTree := by
  refine ⟨⟨⟨PUnit.unit⟩, ?_⟩, ?_⟩
  · intro u v
    cases u
    cases v
    exact Reachable.refl _ _
  · intro u p _
    cases p with
    | mk es _ =>
      cases es with
      | nil => rfl
      | cons e _ => exact PEmpty.elim e

/-- The rose with petals indexed by `α`. Each petal has two distinct orientations. -/
@[expose] def rose (α : Type*) : SerreGraph where
  V := PUnit
  E := α × Bool
  src := fun _ => PUnit.unit
  rev := fun e => (e.1, !e.2)
  rev_rev := by
    intro e
    cases e with
    | mk a b => cases b <;> rfl
  rev_ne := by
    intro e
    cases e with
    | mk a b => cases b <;> simp

/-- Every dart of a rose starts at its sole vertex. -/
@[simp] theorem rose_src {α : Type*} (a : α) (b : Bool) :
    (rose α).src (a, b) = PUnit.unit := rfl

/-- Reversal switches the orientation of a rose petal. -/
@[simp] theorem rose_rev {α : Type*} (a : α) (b : Bool) :
    (rose α).rev (a, b) = (a, !b) := rfl

/-- Every dart of a rose ends at its sole vertex. -/
@[simp] theorem rose_tgt {α : Type*} (a : α) (b : Bool) :
    (rose α).tgt (a, b) = PUnit.unit := rfl

/-- Every rose is connected, including the rose with no petals. -/
theorem rose_connected (α : Type*) : (rose α).Connected := by
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  intro u v
  cases u
  cases v
  exact Reachable.refl _ _

/-- A petal is a nonempty reduced loop in the rose. -/
def rosePetal {α : Type*} (a : α) : (rose α).Path PUnit.unit PUnit.unit :=
  Path.cons (a, true) (Path.nil ((rose α).tgt (a, true)))

@[simp] theorem edges_rosePetal {α : Type*} (a : α) :
    (rosePetal a).edges = [(a, true)] := (rfl)

theorem rosePetal_isReduced {α : Type*} (a : α) :
    (rosePetal a).IsReduced := Path.isReduced_single _

/-- A rose with a petal is not a tree: the petal gives a nonempty reduced loop. -/
theorem rose_not_isTree {α : Type*} (a : α) : ¬(rose α).IsTree := by
  intro ht
  have h := ht.2 PUnit.unit (rosePetal a) (rosePetal_isReduced a)
  simp at h

/-- The one petal rose has a nonempty reduced loop, so it is not a tree. -/
theorem rose_one_not_tree : ¬(rose PUnit).IsTree :=
  rose_not_isTree PUnit.unit

end SerreGraph
end TauCeti
