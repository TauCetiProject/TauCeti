/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The underlying graph of a quiver

The underlying graph of a quiver joins two distinct vertices when an arrow runs between them in
either direction (`TauCeti.Quiver.underlyingGraph`). It forgets loops, the direction of the arrows
and their multiplicity, so it records what orientation-free statements about a quiver, such as
Gabriel's theorem, are phrased in terms of; it depends only on the arrows joining each pair of
vertices, whatever their direction (`TauCeti.Quiver.underlyingGraph_congr`).

## Main definitions

* `TauCeti.Quiver.underlyingGraph`: the simple graph underlying a quiver.

## Main results

* `TauCeti.Quiver.underlyingGraph_adj`: two vertices are adjacent when they are distinct and
  joined by an arrow in one direction or the other.
* `TauCeti.Quiver.underlyingGraph_congr`: two quiver structures joining the same pairs of
  vertices by an arrow, in either direction, have the same underlying graph.
* `TauCeti.Quiver.isAcyclic_underlyingGraph_of_lt`: a quiver in which the arrows out of each vertex
  all share their target, and every arrow strictly lowers a height function, has a forest as its
  underlying graph.
* `TauCeti.Quiver.subsingleton_hom_sum_of_lt`: a quiver with at most one arrow from any vertex to
  any other, all of which strictly lower a height function, joins any two vertices by at most one
  arrow, counted in both directions.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u}

namespace Quiver

section UnderlyingGraph

variable [_root_.Quiver.{v} V]

variable (V) in
/-- The simple graph underlying a quiver: two distinct vertices are adjacent when an arrow runs
between them in either direction. Loops, the direction of the arrows and their multiplicity are
forgotten. -/
def underlyingGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun a b ↦ Nonempty (a ⟶ b)

/-- Two vertices are adjacent in the underlying graph when they are distinct and joined by an
arrow in one direction or the other. -/
@[simp]
theorem underlyingGraph_adj {a b : V} :
    (underlyingGraph V).Adj a b ↔ a ≠ b ∧ (Nonempty (a ⟶ b) ∨ Nonempty (b ⟶ a)) :=
  SimpleGraph.fromRel_adj ..

/-- The two ends of an arrow which is not a loop are adjacent in the underlying graph. -/
theorem underlyingGraph_adj_of_hom {a b : V} (e : a ⟶ b) (hab : a ≠ b) :
    (underlyingGraph V).Adj a b :=
  underlyingGraph_adj.mpr ⟨hab, .inl ⟨e⟩⟩

/-- If every arrow strictly lowers a height function, then two vertices adjacent in the underlying
graph are joined by an arrow out of the one whose height is not below the other's. -/
private theorem nonempty_hom_of_adj_of_not_lt {α : Type*} [Preorder α] {ht : V → α}
    (hlt : ∀ ⦃a b : V⦄, (a ⟶ b) → ht b < ht a) {a b : V} (hab : (underlyingGraph V).Adj a b)
    (hnlt : ¬ht a < ht b) : Nonempty (a ⟶ b) :=
  ((underlyingGraph_adj.mp hab).2.resolve_right fun ⟨e⟩ ↦ hnlt (hlt e))

/-- **The underlying graph of an in-forest is acyclic.** If the arrows out of each vertex of a
quiver all share their target, and every arrow strictly lowers a height function `ht`, then the
underlying graph of the quiver has no cycle: at a vertex of a cycle where `ht` is maximal, both
edges of the cycle would have to be arrows out of that vertex, and they lead to distinct
vertices. -/
theorem isAcyclic_underlyingGraph_of_lt {α : Type*} [Preorder α] (ht : V → α)
    (hlt : ∀ ⦃a b : V⦄, (a ⟶ b) → ht b < ht a)
    (hout : ∀ ⦃a b b' : V⦄, (a ⟶ b) → (a ⟶ b') → b = b') :
    (underlyingGraph V).IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨u, hu, hmax⟩ := c.support.toFinset.exists_maximalFor ht ⟨v, by simp⟩
  have hu : u ∈ c.support := List.mem_toFinset.mp hu
  have hmax' (x : V) (hx : x ∈ (c.rotate u hu).support) : ¬ht u < ht x := fun h ↦
    h.not_ge (hmax (List.mem_toFinset.mpr ((c.mem_support_rotate_iff u hu).mp hx)) h.le)
  have hc' := hc.rotate hu
  have hnil := hc'.not_nil
  obtain ⟨e⟩ := nonempty_hom_of_adj_of_not_lt hlt ((c.rotate u hu).adj_snd hnil)
    (hmax' _ ((c.rotate u hu).getVert_mem_support 1))
  obtain ⟨e'⟩ := nonempty_hom_of_adj_of_not_lt hlt ((c.rotate u hu).adj_penultimate hnil).symm
    (hmax' _ ((c.rotate u hu).getVert_mem_support _))
  exact hc'.snd_ne_penultimate (hout e e')

/-- **A quiver whose arrows lower a height function has at most one arrow between any two
vertices**, counted in both directions, once it has at most one arrow in each direction: two arrows
in opposite directions would raise and lower the height function `ht` at once. -/
theorem subsingleton_hom_sum_of_lt {α : Type*} [Preorder α] (ht : V → α)
    (hlt : ∀ ⦃a b : V⦄, (a ⟶ b) → ht b < ht a) [∀ a b : V, Subsingleton (a ⟶ b)]
    (a b : V) : Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)) := by
  refine ⟨?_⟩
  rintro (e | e) (e' | e')
  · exact congrArg _ (Subsingleton.elim e e')
  · exact ((hlt e).trans (hlt e')).false.elim
  · exact ((hlt e).trans (hlt e')).false.elim
  · exact congrArg _ (Subsingleton.elim e e')

end UnderlyingGraph

/-- **The underlying graph depends only on which vertices are joined**: two quiver structures
which join the same pairs of vertices by an arrow, in one direction or the other, have the same
underlying graph. -/
theorem underlyingGraph_congr {q q' : _root_.Quiver.{v} V}
    (h : ∀ a b : V, Nonempty (@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a) ↔
      Nonempty (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a)) :
    @underlyingGraph V q = @underlyingGraph V q' := by
  ext a b
  rw [@underlyingGraph_adj V q, @underlyingGraph_adj V q', ← nonempty_sum, ← nonempty_sum]
  exact and_congr_right fun _ ↦ h a b

end Quiver

end TauCeti
