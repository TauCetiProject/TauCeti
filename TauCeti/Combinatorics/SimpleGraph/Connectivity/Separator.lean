/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Minimal
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.ArrowWalk

import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Vertex separators of a pair of vertices

A set `S` of vertices of a simple graph `G` *separates* `a` from `b` (`SimpleGraph.IsSeparator`)
when `a, b ∉ S` and `b` is not reachable from `a` once the vertices of `S` are deleted, that is, in
the subgraph `G.induce Sᶜ` induced on the remaining vertices. It is a *minimal* `a`–`b` separator
(`SimpleGraph.IsMinimalSeparator`) when no proper subset separates `a` from `b`. Minimality is for
the fixed pair: a minimal `a`–`b` separator may contain a minimal separator of another pair. No
finiteness is assumed anywhere.

Minimal separators are the separators of Dirac's characterization of chordal graphs. The two facts
about them proved here are the ones its proof uses: every vertex of a minimal `a`–`b` separator has
a neighbour reachable from `a` after deleting the separator, and two distinct nonadjacent vertices
`a`, `b` always have a minimal separator, which can be chosen among the neighbours of `a`.

## Main definitions

* `SimpleGraph.IsSeparator G a b S`: `S` separates `a` from `b`.
* `SimpleGraph.IsMinimalSeparator G a b S`: `S` is a minimal `a`–`b` separator.

## Main results

* `SimpleGraph.isSeparator_iff`: `S` separates `a` from `b` exactly when it avoids `a` and `b` and
  meets every walk from `a` to `b`.
* `SimpleGraph.isMinimalSeparator_iff`: a separator is minimal exactly when deleting any one of its
  vertices gives a set that no longer separates.
* `SimpleGraph.IsMinimalSeparator.exists_adj_reachable`: each vertex of a minimal `a`–`b`
  separator has a neighbour in the part of the graph reachable from `a`.
* `SimpleGraph.exists_isMinimalSeparator_subset_neighborSet`: distinct nonadjacent vertices have
  a minimal separator consisting of neighbours of the first.

## References

* L. Vandenberghe and M. S. Andersen, *Chordal Graphs and Semidefinite Optimization*, Foundations
  and Trends in Optimization 1 (4), 2014, Section 3.3.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b x : V} {S T : Set V}

/-- A set `S` of vertices *separates* `a` from `b` when neither `a` nor `b` lies in `S` and `b` is
not reachable from `a` in the graph obtained by deleting `S`, that is, in the subgraph of `G`
induced on the complement of `S`. -/
structure IsSeparator (G : SimpleGraph V) (a b : V) (S : Set V) : Prop where
  left_notMem : a ∉ S
  right_notMem : b ∉ S
  not_reachable : ¬(G.induce Sᶜ).Reachable ⟨a, left_notMem⟩ ⟨b, right_notMem⟩

/-- A set separates `a` from `b` exactly when it avoids `a` and `b` and meets every walk from `a`
to `b`. -/
theorem isSeparator_iff :
    G.IsSeparator a b S ↔ a ∉ S ∧ b ∉ S ∧ ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ S := by
  refine ⟨fun h ↦ ⟨h.left_notMem, h.right_notMem, fun p ↦ ?_⟩, fun ⟨ha, hb, h⟩ ↦ ⟨ha, hb, ?_⟩⟩
  · by_contra! hp
    exact h.not_reachable (reachable_induce_iff.2 ⟨p, hp⟩)
  · rintro hr
    obtain ⟨p, hp⟩ := reachable_induce_iff.1 hr
    obtain ⟨v, hv, hvS⟩ := h p
    exact hp v hv hvS

/-- A separator of `a` from `b` meets every walk from `a` to `b`. -/
theorem IsSeparator.exists_mem_support (h : G.IsSeparator a b S) (p : G.Walk a b) :
    ∃ v ∈ p.support, v ∈ S :=
  (isSeparator_iff.1 h).2.2 p

/-- Separation is symmetric in the two vertices. -/
theorem IsSeparator.symm (h : G.IsSeparator a b S) : G.IsSeparator b a S :=
  isSeparator_iff.2 ⟨h.right_notMem, h.left_notMem, fun p ↦ by
    simpa using h.exists_mem_support p.reverse⟩

theorem isSeparator_comm : G.IsSeparator a b S ↔ G.IsSeparator b a S :=
  ⟨.symm, .symm⟩

/-- No set separates a vertex from itself. -/
theorem IsSeparator.ne (h : G.IsSeparator a b S) : a ≠ b := by
  rintro rfl
  obtain ⟨v, hv, hvS⟩ := h.exists_mem_support .nil
  rw [Walk.support_nil, List.mem_singleton] at hv
  exact h.left_notMem (hv ▸ hvS)

/-- No set separates two adjacent vertices. -/
theorem IsSeparator.not_adj (h : G.IsSeparator a b S) : ¬G.Adj a b := fun hab ↦ by
  obtain ⟨v, hv, hvS⟩ := h.exists_mem_support hab.toWalk
  rw [Adj.support_toWalk, List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl
  exacts [h.left_notMem hvS, h.right_notMem hvS]

/-- A set containing a separator of `a` from `b` and avoiding `a` and `b` separates them. -/
theorem IsSeparator.mono (h : G.IsSeparator a b S) (hST : S ⊆ T) (ha : a ∉ T) (hb : b ∉ T) :
    G.IsSeparator a b T :=
  isSeparator_iff.2 ⟨ha, hb, fun p ↦
    let ⟨v, hv, hvS⟩ := h.exists_mem_support p
    ⟨v, hv, hST hvS⟩⟩

/-- A *minimal* separator of `a` from `b` is a set separating `a` from `b` no proper subset of which
separates `a` from `b`. Minimality refers to the fixed pair `a`, `b`. -/
def IsMinimalSeparator (G : SimpleGraph V) (a b : V) (S : Set V) : Prop :=
  Minimal (G.IsSeparator a b) S

theorem isMinimalSeparator_def :
    G.IsMinimalSeparator a b S ↔ Minimal (G.IsSeparator a b) S :=
  Iff.rfl

theorem IsMinimalSeparator.isSeparator (h : G.IsMinimalSeparator a b S) : G.IsSeparator a b S :=
  (isMinimalSeparator_def.1 h).prop

/-- A separator of `a` from `b` is minimal exactly when removing any one of its vertices leaves a
set that does not separate `a` from `b`. -/
theorem isMinimalSeparator_iff :
    G.IsMinimalSeparator a b S ↔
      G.IsSeparator a b S ∧ ∀ x ∈ S, ¬G.IsSeparator a b (S \ {x}) := by
  refine ⟨fun h ↦ ⟨h.isSeparator, fun x hx hx' ↦ ?_⟩, fun ⟨h, h'⟩ ↦
    isMinimalSeparator_def.2 ⟨h, fun T hT hTS ↦ ?_⟩⟩
  · exact (isMinimalSeparator_def.1 h |>.2 hx' Set.sdiff_subset hx).2 rfl
  · intro x hx
    by_contra hxT
    exact h' x hx (hT.mono (fun y hy ↦ ⟨hTS hy, by rintro rfl; exact hxT hy⟩)
      (fun ha ↦ h.left_notMem ha.1) (fun hb ↦ h.right_notMem hb.1))

/-- Minimal separation is symmetric in the two vertices. -/
theorem IsMinimalSeparator.symm (h : G.IsMinimalSeparator a b S) : G.IsMinimalSeparator b a S := by
  rw [isMinimalSeparator_iff] at h ⊢
  exact ⟨h.1.symm, fun x hx hx' ↦ h.2 x hx hx'.symm⟩

theorem isMinimalSeparator_comm : G.IsMinimalSeparator a b S ↔ G.IsMinimalSeparator b a S :=
  ⟨.symm, .symm⟩

/-- Every vertex `x` of a minimal separator of `a` from `b` has a neighbour that is reachable from
`a` after deleting the separator. -/
theorem IsMinimalSeparator.exists_adj_reachable (h : G.IsMinimalSeparator a b S) (hx : x ∈ S) :
    ∃ (w : V) (hw : w ∉ S), G.Adj x w ∧
      (G.induce Sᶜ).Reachable ⟨a, h.isSeparator.left_notMem⟩ ⟨w, hw⟩ := by
  have hS := h.isSeparator
  obtain ⟨p, hp⟩ : ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ S \ {x} := by
    have := (isMinimalSeparator_iff.1 h).2 x hx
    rw [isSeparator_iff] at this
    push Not at this
    exact this (fun ha ↦ hS.left_notMem ha.1) (fun hb ↦ hS.right_notMem hb.1)
  -- the vertices reachable from `a` by walks avoiding `S`
  let C : Set V := {v | ∃ q : G.Walk a v, ∀ w ∈ q.support, w ∉ S}
  have hbC : b ∉ C := fun ⟨q, hq⟩ ↦
    let ⟨v, hv, hvS⟩ := hS.exists_mem_support q
    hq v hv hvS
  obtain ⟨d, hd, ⟨q, hq⟩, hdC⟩ := p.exists_boundary_dart C ⟨.nil, by simpa using hS.left_notMem⟩ hbC
  have hdS : d.snd ∈ S := by
    by_contra hdS
    refine hdC ⟨q.concat d.adj, fun w hw ↦ ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    exacts [hq w hw, hdS]
  have hdx : d.snd = x := by
    by_contra hdx
    exact hp _ (p.dart_snd_mem_support_of_mem_darts hd) ⟨hdS, hdx⟩
  refine ⟨d.fst, hq _ q.end_mem_support, hdx ▸ d.adj.symm, reachable_induce_iff.2 ⟨q, hq⟩⟩

/-- **Existence of minimal separators.** Two distinct nonadjacent vertices `a` and `b` have a
minimal separator all of whose vertices are neighbours of `a`. No finiteness is needed. -/
theorem exists_isMinimalSeparator_subset_neighborSet (hab : a ≠ b) (h : ¬G.Adj a b) :
    ∃ S ⊆ G.neighborSet a, G.IsMinimalSeparator a b S := by
  -- `D` is the set of vertices joined to `b` by a walk avoiding the neighbours of `a`, and the
  -- separator `T` consists of the neighbours of `a` with a neighbour in `D`
  let D : Set V := {v | ∃ q : G.Walk v b, ∀ w ∈ q.support, w ∉ G.neighborSet a}
  let T : Set V := {x | G.Adj a x ∧ ∃ d ∈ D, G.Adj x d}
  have hbD : b ∈ D := ⟨.nil, by simpa using h⟩
  have haD : a ∉ D := by
    rintro ⟨_ | ⟨hv, q⟩, hq⟩
    · exact hab rfl
    · exact hq _ (by simp) hv
  have haT : a ∉ T := fun ha ↦ G.loopless.irrefl a ha.1
  have hbT : b ∉ T := fun hb ↦ h hb.1
  refine ⟨T, fun x hx ↦ hx.1, isMinimalSeparator_iff.2 ⟨isSeparator_iff.2 ⟨haT, hbT, fun p ↦ ?_⟩,
    fun x hx hsep ↦ ?_⟩⟩
  · -- a walk from `b` to `a` leaves `D` through a neighbour of `a` with a neighbour in `D`
    obtain ⟨d, hd, ⟨q, hq⟩, hdD⟩ := p.reverse.exists_boundary_dart D hbD haD
    have hda : G.Adj a d.snd := by
      by_contra hda
      refine hdD ⟨q.cons d.adj.symm, fun w hw ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      exacts [hda, hq w hw]
    refine ⟨d.snd, ?_, hda, d.fst, ⟨q, hq⟩, d.adj.symm⟩
    simpa using p.reverse.dart_snd_mem_support_of_mem_darts hd
  · -- deleting `x` from `T` reopens the walk from `a` through `x` and `D` to `b`
    obtain ⟨hax, d, ⟨q, hq⟩, hxd⟩ := hx
    obtain ⟨v, hv, hvT, hvx⟩ := hsep.exists_mem_support ((q.cons hxd).cons hax)
    rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    exacts [haT hvT, hvx rfl, hq v hv hvT.1]

end SimpleGraph
