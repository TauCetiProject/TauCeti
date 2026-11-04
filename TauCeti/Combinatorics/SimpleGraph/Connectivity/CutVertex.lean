/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutVertex

import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Cut vertices of simple graphs

A vertex of a simple graph is a cut vertex when deleting it separates two vertices that were
previously connected. The predicate is defined through the native multigraph cut-vertex API for
`Graph.ofSimpleGraph`, and `SimpleGraph.isCutVertex_iff_exists_forall_walk_mem_support` restates it
with walks of the simple graph itself: a cut vertex lies on every walk between two other mutually
reachable vertices.

For a vertex set inducing a connected graph without cut vertices, any two of its vertices other
than a given vertex are joined by a walk inside the set avoiding it
(`SimpleGraph.exists_walk_forall_mem_support_mem_and_ne`); conversely, such walks rule out cut
vertices (`SimpleGraph.not_isCutVertex_induce_of_exists_walk`). Together these give the ear lemma
`SimpleGraph.Walk.IsPath.not_isCutVertex_induce_union_support`: adding the vertices of a path
between two vertices of such a set preserves the absence of cut vertices (R. Diestel,
*Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1).
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u}

/-- A vertex of a simple graph is a cut vertex when deleting it separates two vertices that were
previously connected. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  (Graph.ofSimpleGraph G).IsCutVertex v

/-- The cut-vertex predicate for a simple graph is the native multigraph predicate after applying
`Graph.ofSimpleGraph`. -/
theorem isCutVertex_def (G : SimpleGraph V) (v : V) :
    G.IsCutVertex v ↔ (Graph.ofSimpleGraph G).IsCutVertex v :=
  Iff.rfl

/-- A vertex is a cut vertex exactly when it lies on every walk between some two other vertices
that are reachable from each other. -/
theorem isCutVertex_iff_exists_forall_walk_mem_support {G : SimpleGraph V} {v : V} :
    G.IsCutVertex v ↔
      ∃ u w, u ≠ v ∧ w ≠ v ∧ G.Reachable u w ∧ ∀ p : G.Walk u w, v ∈ p.support := by
  rw [isCutVertex_def, Graph.isCutVertex_def]
  simp only [reachable_ofSimpleGraph_iff, Graph.reachable_deleteVerts_iff_exists_walk,
    Set.mem_singleton_iff, not_exists, not_and, not_forall, not_not]
  refine exists₂_congr fun u w ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ ⟨fun h p ↦ ?_, fun h p _ ↦ ?_⟩
  · obtain ⟨z, hz, rfl⟩ := h p.toGraph (by simp)
    simpa using hz
  · exact ⟨v, by simpa using h p.toSimpleGraph, rfl⟩

/-- If `x` is not a cut vertex, then two vertices other than `x` that are reachable from each other
are joined by a walk avoiding `x`. -/
theorem Reachable.exists_walk_notMem_support_of_not_isCutVertex {G : SimpleGraph V} {a z x : V}
    (h : G.Reachable a z) (hx : ¬G.IsCutVertex x) (hax : a ≠ x) (hzx : z ≠ x) :
    ∃ p : G.Walk a z, x ∉ p.support := by
  by_contra hn
  simp only [not_exists, not_not] at hn
  exact hx (isCutVertex_iff_exists_forall_walk_mem_support.2 ⟨a, z, hax, hzx, h, hn⟩)

/-- A graph induced on a singleton has no cut vertex. -/
theorem not_isCutVertex_induce_singleton (G : SimpleGraph V) (v : V)
    (w : ↑({v} : Set V)) :
    ¬(G.induce {v}).IsCutVertex w := by
  apply Graph.not_isCutVertex_of_compl_subsingleton
  intro x hx y hy
  apply Subtype.ext
  have hxv := x.property
  have hyv := y.property
  simp only [Set.mem_singleton_iff] at hxv hyv
  exact hxv.trans hyv.symm

/-- A graph induced on a pair of vertices has no cut vertex. -/
@[simp]
theorem not_isCutVertex_induce_pair (G : SimpleGraph V) (u v : V)
    (w : ↑({u, v} : Set V)) :
    ¬(G.induce {u, v}).IsCutVertex w := by
  apply Graph.not_isCutVertex_of_compl_subsingleton
  rintro ⟨x, hx⟩ ⟨-, hxw⟩ ⟨y, hy⟩ ⟨-, hyw⟩
  apply Subtype.ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · rcases w.property with hw | hw
    · exact (hxw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
    · exact (hyw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
  · rcases w.property with hw | hw
    · exact (hyw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
    · exact (hxw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
  · rfl

/-! ### Induced graphs without cut vertices -/

section Induce

variable {G : SimpleGraph V} {B : Set V}

/-- If a vertex set induces a connected graph without cut vertices, then any two of its vertices
other than `x` are joined by a walk of `G` inside the set avoiding `x`. -/
theorem exists_walk_forall_mem_support_mem_and_ne (hconn : (G.induce B).Connected)
    (hcut : ∀ v, ¬(G.induce B).IsCutVertex v) {a z x : V} (ha : a ∈ B) (hz : z ∈ B)
    (hax : a ≠ x) (hzx : z ≠ x) :
    ∃ p : G.Walk a z, ∀ y ∈ p.support, y ∈ B ∧ y ≠ x := by
  have hreach := hconn.preconnected ⟨a, ha⟩ ⟨z, hz⟩
  obtain ⟨p, hp⟩ : ∃ p : (G.induce B).Walk ⟨a, ha⟩ ⟨z, hz⟩, ∀ y ∈ p.support, (y : V) ≠ x := by
    by_cases hx : x ∈ B
    · obtain ⟨p, hp⟩ := hreach.exists_walk_notMem_support_of_not_isCutVertex (hcut ⟨x, hx⟩)
        (fun h ↦ hax (congrArg Subtype.val h)) (fun h ↦ hzx (congrArg Subtype.val h))
      exact ⟨p, fun y hy hyx ↦ hp (by obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hyx; exact hy)⟩
    · exact hreach.elim fun p ↦ ⟨p, fun y _ hyx ↦ hx (hyx ▸ y.property)⟩
  have hq : ∀ y ∈ (p.map (Embedding.induce B).toHom).support, y ∈ B ∧ y ≠ x := by
    intro y hy
    simp only [Walk.support_map, List.mem_map] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨y.property, hp y hy⟩
  exact ⟨_, hq⟩

/-- A vertex set induces a graph without cut vertices when, for each vertex `x`, any two other
vertices of the set are joined by a walk of `G` inside the set avoiding `x`. -/
theorem not_isCutVertex_induce_of_exists_walk
    (h : ∀ x ∈ B, ∀ a ∈ B, ∀ b ∈ B, a ≠ x → b ≠ x →
      ∃ p : G.Walk a b, ∀ y ∈ p.support, y ∈ B ∧ y ≠ x) (x : B) :
    ¬(G.induce B).IsCutVertex x := by
  rw [isCutVertex_iff_exists_forall_walk_mem_support]
  rintro ⟨a, b, hax, hbx, -, hall⟩
  obtain ⟨p, hp⟩ := h x x.property a a.property b b.property
    (fun h ↦ hax (Subtype.ext h)) (fun h ↦ hbx (Subtype.ext h))
  have hx := hall (p.induce B fun y hy ↦ (hp y hy).1)
  rw [Walk.support_induce, List.mem_attachWith] at hx
  exact (hp x hx).2 rfl

/-- **Adding an ear.** If a vertex set induces a connected graph without cut vertices, then adding
the vertices of a path between two of its vertices gives a vertex set whose induced graph still
has no cut vertex. -/
theorem Walk.IsPath.not_isCutVertex_induce_union_support (hconn : (G.induce B).Connected)
    (hcut : ∀ v, ¬(G.induce B).IsCutVertex v) {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (ha : a ∈ B) (hb : b ∈ B) (x : ↑(B ∪ {y | y ∈ p.support})) :
    ¬(G.induce (B ∪ {y | y ∈ p.support})).IsCutVertex x := by
  apply not_isCutVertex_induce_of_exists_walk
  intro x _
  -- Each vertex other than `x` reaches a vertex of `B` other than `x` inside the union.
  have hreach : ∀ c ∈ B ∪ {y | y ∈ p.support}, c ≠ x → ∃ z ∈ B, z ≠ x ∧
      ∃ q : G.Walk c z, ∀ y ∈ q.support, y ∈ B ∪ {y | y ∈ p.support} ∧ y ≠ x := by
    rintro c (hcB | hcp) hcx
    · exact ⟨c, hcB, hcx, Walk.nil, by simp [hcB, hcx]⟩
    · -- Split the path at `c`; since it is a path, `x` lies on at most one of the two pieces.
      obtain ⟨q, r, -, -, hqr⟩ := hp.mem_support_iff_exists_append.mp hcp
      have hsupp : ∀ y, y ∈ q.support ∨ y ∈ r.support → y ∈ B ∪ {y | y ∈ p.support} :=
        fun y hy ↦ Or.inr (by rw [Set.mem_ofPred_eq, hqr, Walk.mem_support_append_iff]; exact hy)
      by_cases hxq : x ∈ q.support
      · have hxr : x ∉ r.support := fun hxr ↦
          (hqr ▸ hp).ne_of_mem_support_of_append (Ne.symm hcx) hxq hxr rfl
        refine ⟨b, hb, fun hbx ↦ hxr (hbx ▸ r.end_mem_support), r, fun y hy ↦
          ⟨hsupp y (Or.inr hy), fun hyx ↦ hxr (hyx ▸ hy)⟩⟩
      · refine ⟨a, ha, fun hax ↦ hxq (hax ▸ q.start_mem_support), q.reverse, fun y hy ↦ ?_⟩
        rw [Walk.support_reverse, List.mem_reverse] at hy
        exact ⟨hsupp y (Or.inl hy), fun hyx ↦ hxq (hyx ▸ hy)⟩
  intro c hc d hd hcx hdx
  obtain ⟨z, hzB, hzx, q, hq⟩ := hreach c hc hcx
  obtain ⟨z', hz'B, hz'x, r, hr⟩ := hreach d hd hdx
  obtain ⟨m, hm⟩ := exists_walk_forall_mem_support_mem_and_ne hconn hcut hzB hz'B hzx hz'x
  refine ⟨(q.append m).append r.reverse, fun y hy ↦ ?_⟩
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
  rcases hy with (hy | hy) | hy
  · exact hq y hy
  · exact ⟨Or.inl (hm y hy).1, (hm y hy).2⟩
  · exact hr y hy

end Induce

end SimpleGraph
