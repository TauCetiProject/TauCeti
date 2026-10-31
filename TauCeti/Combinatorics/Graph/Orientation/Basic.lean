/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.EdgeEnds
public import Mathlib.Data.Fintype.EquivFin

/-!
# Orientations of multigraphs

An orientation of a multigraph orders the two ends of every actual edge. The edge identity is
retained, so parallel edges can be oriented independently. A loop has equal tail and head and
therefore gives one directed loop, without an additional choice of direction.

The explicit arrow family `Graph.Orientation.Hom` has one arrow for each actual edge, from its
chosen tail to its chosen head. It can be supplied directly to quiver and network constructions
without installing a `Quiver` instance on the graph's vertex type. Reversing an orientation
reverses every arrow while preserving its edge identity.

## Main declarations

* `Graph.Orientation`: an ordering of the ends of every actual edge.
* `Graph.Orientation.ofEdgeEnds`: an arbitrary orientation available for every multigraph.
* `Graph.Orientation.ofHead`: the orientation with prescribed heads.
* `Graph.Orientation.reverse`: reversal of every chosen edge direction.
* `Graph.Orientation.Hom`: the associated explicit arrow family.
* `Graph.Orientation.totalHomEquiv`: the total arrows are equivalent to the actual edges.
-/

public section

namespace Graph

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- An orientation of a multigraph chooses a tail and head for every actual edge, compatible
with that edge's incidence. Parallel edges retain separate choices, while a loop necessarily
has the same tail and head. -/
structure Orientation (G : Graph V E) where
  /-- The chosen tail of an actual edge. -/
  tail : G.edgeSet → G.vertexSet
  /-- The chosen head of an actual edge. -/
  head : G.edgeSet → G.vertexSet
  /-- The chosen tail and head are the two ends of the edge. -/
  isLink (e : G.edgeSet) : G.IsLink e.1 (tail e).1 (head e).1

namespace Orientation

/-- Two orientations are equal when they choose the same tail and head for every edge. -/
@[ext]
theorem ext {o₁ o₂ : Orientation G} (htail : ∀ e, o₁.tail e = o₂.tail e)
    (hhead : ∀ e, o₁.head e = o₂.head e) : o₁ = o₂ := by
  cases o₁ with
  | mk tail₁ head₁ hlink₁ =>
    cases o₂ with
    | mk tail₂ head₂ hlink₂ =>
      have htail' : tail₁ = tail₂ := funext htail
      have hhead' : head₁ = head₂ := funext hhead
      subst tail₂ head₂
      rfl

/-- The unordered pair formed by the chosen tail and head is the edge's pair of ends. -/
theorem edgeEnds_eq (o : Orientation G) (e : G.edgeSet) :
    G.edgeEnds e = s(o.tail e, o.head e) :=
  G.edgeEnds_eq_iff_isLink e (o.tail e) (o.head e) |>.2 (o.isLink e)

/-- The chosen tail is incident to its edge. -/
theorem tail_inc (o : Orientation G) (e : G.edgeSet) : G.Inc e.1 (o.tail e).1 :=
  (o.isLink e).inc_left

/-- The chosen head is incident to its edge. -/
theorem head_inc (o : Orientation G) (e : G.edgeSet) : G.Inc e.1 (o.head e).1 :=
  (o.isLink e).inc_right

/-- Two orientations choosing the same tail for an edge also choose the same head. -/
theorem head_eq_of_tail_eq {o₁ o₂ : Orientation G} {e : G.edgeSet}
    (h : o₁.tail e = o₂.tail e) : o₁.head e = o₂.head e :=
  Subtype.ext <| (o₁.isLink e).right_unique <| h ▸ o₂.isLink e

/-- Two orientations are equal when they choose the same tail for every edge. -/
theorem ext_of_tail {o₁ o₂ : Orientation G} (h : ∀ e, o₁.tail e = o₂.tail e) : o₁ = o₂ :=
  ext h fun _ ↦ head_eq_of_tail_eq (h _)

/-- Two orientations choosing the same head for an edge also choose the same tail. -/
theorem tail_eq_of_head_eq {o₁ o₂ : Orientation G} {e : G.edgeSet}
    (h : o₁.head e = o₂.head e) : o₁.tail e = o₂.tail e :=
  Subtype.ext <| (o₁.isLink e).symm.right_unique <| h ▸ (o₂.isLink e).symm

/-- Two orientations are equal when they choose the same head for every edge. -/
theorem ext_of_head {o₁ o₂ : Orientation G} (h : ∀ e, o₁.head e = o₂.head e) : o₁ = o₂ :=
  ext (fun _ ↦ tail_eq_of_head_eq (h _)) h

/-- The orientation choosing a prescribed incident vertex as the head of every edge; the tail is
the other end, which is the head itself for a loop. -/
noncomputable def ofHead (head : G.edgeSet → G.vertexSet) (h : ∀ e, G.Inc e.1 (head e).1) :
    Orientation G where
  tail e := ⟨(h e).other, (h e).isLink_other.right_mem⟩
  head := head
  isLink e := (h e).isLink_other.symm

@[simp]
theorem ofHead_head (head : G.edgeSet → G.vertexSet) (h : ∀ e, G.Inc e.1 (head e).1)
    (e : G.edgeSet) : (ofHead head h).head e = head e :=
  (rfl)

@[simp]
theorem ofHead_self (o : Orientation G) : ofHead o.head o.head_inc = o :=
  ext_of_head fun _ ↦ rfl

/-- Two orientations either agree on an edge or orient it in opposite directions. -/
theorem tail_eq_and_head_eq_or_tail_eq_and_head_eq (o₁ o₂ : Orientation G) (e : G.edgeSet) :
    o₁.tail e = o₂.tail e ∧ o₁.head e = o₂.head e ∨
      o₁.tail e = o₂.head e ∧ o₁.head e = o₂.tail e := by
  simpa only [Subtype.ext_iff] using (o₁.isLink e).eq_and_eq_or_eq_and_eq (o₂.isLink e)

/-- Every multigraph admits an orientation, obtained from a representative of each unordered
pair of edge ends. -/
noncomputable def ofEdgeEnds (G : Graph V E) : Orientation G where
  tail e := (G.edgeEnds e).out.1
  head e := (G.edgeEnds e).out.2
  isLink e := G.edgeEnds_eq_iff_isLink e _ _ |>.1
    (Sym2.mk_fst_out_snd_out (G.edgeEnds e)).symm

@[simp]
theorem ofEdgeEnds_tail (G : Graph V E) (e : G.edgeSet) :
    (ofEdgeEnds G).tail e = (G.edgeEnds e).out.1 :=
  (rfl)

@[simp]
theorem ofEdgeEnds_head (G : Graph V E) (e : G.edgeSet) :
    (ofEdgeEnds G).head e = (G.edgeEnds e).out.2 :=
  (rfl)

/-- Reverse every edge of an orientation. -/
def reverse (o : Orientation G) : Orientation G where
  tail := o.head
  head := o.tail
  isLink e := (o.isLink e).symm

@[simp]
theorem reverse_tail (o : Orientation G) (e : G.edgeSet) :
    o.reverse.tail e = o.head e :=
  (rfl)

@[simp]
theorem reverse_head (o : Orientation G) (e : G.edgeSet) :
    o.reverse.head e = o.tail e :=
  (rfl)

@[simp]
theorem reverse_reverse (o : Orientation G) : o.reverse.reverse = o := by
  ext <;> rfl

theorem reverse_involutive : Function.Involutive (reverse (G := G)) :=
  reverse_reverse

theorem reverse_injective : Function.Injective (reverse (G := G)) :=
  reverse_involutive.injective

@[simp]
theorem reverse_inj {o₁ o₂ : Orientation G} : o₁.reverse = o₂.reverse ↔ o₁ = o₂ :=
  reverse_injective.eq_iff

/-- Reversing every edge is an involutive equivalence on orientations. -/
def reverseEquiv (G : Graph V E) : Equiv.Perm (Orientation G) :=
  reverse_involutive.toPerm reverse

@[simp]
theorem reverseEquiv_apply (G : Graph V E) (o : Orientation G) :
    reverseEquiv G o = o.reverse := by
  exact congrFun (Function.Involutive.coe_toPerm (reverse_involutive (G := G))) o

/-- An edge is a loop at its chosen tail exactly when its chosen tail and head coincide. -/
theorem tail_eq_head_iff_isLoopAt (o : Orientation G) (e : G.edgeSet) :
    o.tail e = o.head e ↔ G.IsLoopAt e.1 (o.tail e).1 := by
  rw [← isLink_self_iff]
  constructor
  · intro h
    simpa only [h] using o.isLink e
  · intro h
    exact Subtype.ext ((o.isLink e).right_unique h).symm

/-- The unordered ends of an edge are diagonal exactly when the orientation makes it a loop
arrow. -/
theorem edgeEnds_isDiag_iff (o : Orientation G) (e : G.edgeSet) :
    (G.edgeEnds e).IsDiag ↔ o.tail e = o.head e := by
  rw [o.edgeEnds_eq e, Sym2.mk_isDiag_iff]

/-- The explicit family of arrows selected by an orientation. An arrow from `x` to `y` is an
actual edge whose chosen tail is `x` and whose chosen head is `y`. -/
@[ext]
structure Hom (o : Orientation G) (x y : G.vertexSet) where
  /-- The actual edge underlying the arrow. -/
  edge : G.edgeSet
  /-- The arrow's source is the chosen tail of its edge. -/
  tail_eq : o.tail edge = x
  /-- The arrow's target is the chosen head of its edge. -/
  head_eq : o.head edge = y

/-- The underlying edge of an oriented arrow links its source and target. -/
theorem Hom.isLink {o : Orientation G} {x y : G.vertexSet} (a : o.Hom x y) :
    G.IsLink a.edge.1 x.1 y.1 := by
  simpa only [a.tail_eq, a.head_eq] using o.isLink a.edge

/-- Regard an actual edge as the arrow from its chosen tail to its chosen head. -/
def arrow (o : Orientation G) (e : G.edgeSet) : o.Hom (o.tail e) (o.head e) :=
  ⟨e, rfl, rfl⟩

@[simp]
theorem arrow_edge (o : Orientation G) (e : G.edgeSet) : (o.arrow e).edge = e :=
  (rfl)

/-- All arrows of an orientation, with their source and target vertices. -/
abbrev TotalHom (o : Orientation G) := Σ x, Σ y, o.Hom x y

/-- The total arrows of an orientation are exactly the actual edges of the multigraph. This
equivalence retains parallel edge identities and sends a loop to one arrow. -/
def totalHomEquiv (o : Orientation G) : o.TotalHom ≃ G.edgeSet where
  toFun a := a.2.2.edge
  invFun e := ⟨o.tail e, o.head e, o.arrow e⟩
  left_inv := by
    rintro ⟨x, y, a⟩
    obtain ⟨e, htail, hhead⟩ := a
    subst x y
    rfl
  right_inv _ := rfl

@[simp]
theorem totalHomEquiv_apply (o : Orientation G) (a : o.TotalHom) :
    o.totalHomEquiv a = a.2.2.edge :=
  (rfl)

@[simp]
theorem totalHomEquiv_symm_apply (o : Orientation G) (e : G.edgeSet) :
    o.totalHomEquiv.symm e = ⟨o.tail e, o.head e, o.arrow e⟩ :=
  (rfl)

/-- The edge identity determines an oriented arrow, including its endpoints. -/
theorem totalHom_edge_val_injective (o : Orientation G) :
    Function.Injective (fun a : o.TotalHom ↦ a.2.2.edge.1) :=
  Subtype.val_injective.comp o.totalHomEquiv.injective

/-- Reversing an orientation reverses an arrow while retaining its edge identity. -/
def reverseHomEquiv (o : Orientation G) (x y : G.vertexSet) :
    o.Hom x y ≃ o.reverse.Hom y x where
  toFun a := ⟨a.edge, a.head_eq, a.tail_eq⟩
  invFun a := ⟨a.edge, a.head_eq, a.tail_eq⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem reverseHomEquiv_edge (o : Orientation G) {x y : G.vertexSet} (a : o.Hom x y) :
    (o.reverseHomEquiv x y a).edge = a.edge :=
  (rfl)

@[simp]
theorem reverseHomEquiv_symm_edge (o : Orientation G) {x y : G.vertexSet}
    (a : o.reverse.Hom y x) : ((o.reverseHomEquiv x y).symm a).edge = a.edge :=
  (rfl)

/-- An orientation has finitely many arrows between any two vertices when its actual edge set is
finite. -/
instance (o : Orientation G) (x y : G.vertexSet) [Finite G.edgeSet] : Finite (o.Hom x y) :=
  Finite.of_injective Hom.edge fun _ _ ↦ Hom.ext

end Orientation

end Graph
