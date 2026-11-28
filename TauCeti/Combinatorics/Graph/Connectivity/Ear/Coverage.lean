/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic

import Mathlib.Data.Set.Pairwise.Lattice

/-!
# Vertex coverage of ear decompositions

An ear decomposition introduces a vertex at the first stage containing it. This file packages
the vertices introduced by each displayed ear and proves that they partition the vertices outside
the initial graph. In particular, every non-initial vertex is introduced by a unique ear.

These results complement the edge coverage API: edge identities of distinct ears are disjoint,
while the endpoints of later ears may be vertices introduced earlier. The new vertices of an ear
are precisely the vertices in its support that do not belong to its base graph.

The conventions follow R. Diestel, *Graph Theory*, Chapter 3.
-/

public section

open Set

universe u v

namespace Graph.Ear

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-- The internal vertices introduced when an ear is added to its base graph. -/
def newVertexSet (e : G.Ear H) : Set α :=
  V(e.toGraph) \ V(H)

/-- A vertex is new in an ear exactly when it lies on the ear and not in its base graph. -/
@[simp]
theorem mem_newVertexSet_iff (e : G.Ear H) (x : α) :
    x ∈ e.newVertexSet ↔ x ∈ e.toWalk.2.2.support ∧ x ∉ V(H) := by
  rw [newVertexSet, e.vertexSet_toGraph]
  simp only [mem_sdiff, mem_ofPred_eq]

/-- The new vertices of an ear are exactly the non-endpoint vertices of its support. -/
theorem mem_newVertexSet_iff_ne_endpoints (e : G.Ear H) (x : α) :
    x ∈ e.newVertexSet ↔
      x ∈ e.toWalk.2.2.support ∧ x ≠ e.toWalk.1 ∧ x ≠ e.toWalk.2.1 := by
  cases e with
  | «open» h walk isPath start_mem end_mem endpoints_ne internal_new edges_new =>
      rw [mem_newVertexSet_iff, toWalk_open]
      constructor
      · rintro ⟨hx, hxH⟩
        exact ⟨hx, fun hxs ↦ hxH (hxs ▸ start_mem), fun hxt ↦ hxH (hxt ▸ end_mem)⟩
      · rintro ⟨hx, hxs, hxt⟩
        exact ⟨hx, internal_new x hx hxs hxt⟩
  | «closed» h walk isCycle base_mem internal_new edges_new =>
      rw [mem_newVertexSet_iff, toWalk_closed]
      constructor
      · rintro ⟨hx, hxH⟩
        exact ⟨hx, fun hxs ↦ hxH (hxs ▸ base_mem), fun hxs ↦ hxH (hxs ▸ base_mem)⟩
      · rintro ⟨hx, hxs, -⟩
        exact ⟨hx, internal_new x hx hxs⟩

end Graph.Ear

namespace Graph.EarDecomposition

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-- The vertices introduced by the `i`-th ear of a decomposition. -/
def newVertexSet (d : G.EarDecomposition H) (i : Fin d.length) : Set α :=
  (d.earAt i).2.newVertexSet

/-- A vertex is introduced by an ear exactly when it lies on that ear but not in its base graph. -/
@[simp]
theorem mem_newVertexSet_iff (d : G.EarDecomposition H) (i : Fin d.length) (x : α) :
    x ∈ d.newVertexSet i ↔
      x ∈ (d.walkAt i).2.2.support ∧ x ∉ V((d.earAt i).1) := by
  rw [newVertexSet, (d.earAt i).2.mem_newVertexSet_iff, d.walkAt_eq]

/-- A vertex is introduced at a step exactly when it is a non-endpoint vertex of that ear. -/
theorem mem_newVertexSet_iff_ne_endpoints (d : G.EarDecomposition H) (i : Fin d.length)
    (x : α) :
    x ∈ d.newVertexSet i ↔
      x ∈ (d.walkAt i).2.2.support ∧ x ≠ (d.walkAt i).1 ∧ x ≠ (d.walkAt i).2.1 := by
  rw [newVertexSet, (d.earAt i).2.mem_newVertexSet_iff_ne_endpoints, d.walkAt_eq]

/-- The vertices at a stage are the initial vertices together with those introduced by the
preceding ears. -/
theorem vertexSet_graphAfter_eq_union_biUnion_newVertexSet (d : G.EarDecomposition H)
    (i : Fin (d.length + 1)) :
    V(d.graphAfter i) =
      V(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < i), d.newVertexSet j := by
  induction i using Fin.induction with
  | zero => simp
  | succ k ih =>
      have ih' : V((d.earAt k).1) =
          V(d.initial) ∪ ⋃ (j : Fin d.length) (_ : j.castSucc < k.castSucc),
            d.newVertexSet j := by
        simpa only [d.earAt_fst] using ih
      rw [d.graphAfter_succ, (d.earAt k).2.vertexSet_add, ih']
      ext x
      simp only [newVertexSet, Graph.Ear.newVertexSet, mem_union, mem_iUnion, mem_sdiff]
      constructor
      · rintro ((hx | ⟨j, hj, hxj⟩) | hxk)
        · exact Or.inl hx
        · exact Or.inr ⟨j, hj.trans k.castSucc_lt_succ, hxj⟩
        · by_cases hbase : x ∈ V((d.earAt k).1)
          · have hold := (Set.ext_iff.mp ih' x).mp hbase
            simp only [mem_union, mem_iUnion] at hold
            rcases hold with hx0 | ⟨j, hj, hxj⟩
            · exact Or.inl hx0
            · exact Or.inr ⟨j, hj.trans k.castSucc_lt_succ, hxj⟩
          · exact Or.inr ⟨k, k.castSucc_lt_succ, hxk, hbase⟩
      · rintro (hx | ⟨j, hj, hxj⟩)
        · exact Or.inl (Or.inl hx)
        · have hjk : j ≤ k := not_lt.mp fun hkj ↦ hj.not_ge (Fin.succ_le_castSucc_iff.mpr hkj)
          rcases lt_or_eq_of_le hjk with hjk | rfl
          · exact Or.inl (Or.inr ⟨j, Fin.castSucc_lt_castSucc_iff.mpr hjk, hxj⟩)
          · exact Or.inr hxj.1

/-- The final vertices are the initial vertices together with the vertices introduced by the
displayed ears. -/
theorem vertexSet_eq_union_iUnion_newVertexSet (d : G.EarDecomposition H) :
    V(H) = V(d.initial) ∪ ⋃ i : Fin d.length, d.newVertexSet i := by
  rw [← congrArg vertexSet d.graphAfter_last,
    d.vertexSet_graphAfter_eq_union_biUnion_newVertexSet]
  simp [Fin.castSucc_lt_last]

/-- No vertex introduced by an ear belongs to the initial graph. -/
theorem disjoint_vertexSet_initial_newVertexSet (d : G.EarDecomposition H)
    (i : Fin d.length) : Disjoint V(d.initial) (d.newVertexSet i) := by
  rw [Set.disjoint_left]
  intro x hx hxi
  apply hxi.2
  simpa only [d.earAt_fst] using (d.initial_le_graphAfter i.castSucc).vertexSet_mono hx

/-- Distinct ears of a decomposition introduce disjoint sets of vertices. -/
theorem pairwise_disjoint_newVertexSet (d : G.EarDecomposition H) :
    Pairwise fun i j : Fin d.length ↦ Disjoint (d.newVertexSet i) (d.newVertexSet j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [Set.disjoint_left]
    intro x hxi hxj
    apply hxj.2
    simpa only [d.earAt_fst] using
      (d.monotone_graphAfter (Fin.succ_le_castSucc_iff.mpr hij)).vertexSet_mono
        ((d.toGraph_earAt_le_graphAfter_succ i).vertexSet_mono hxi.1)
  · have hdisj : Disjoint (d.newVertexSet j) (d.newVertexSet i) := by
      rw [Set.disjoint_left]
      intro x hxj hxi
      apply hxi.2
      simpa only [d.earAt_fst] using
        (d.monotone_graphAfter (Fin.succ_le_castSucc_iff.mpr hji)).vertexSet_mono
          ((d.toGraph_earAt_le_graphAfter_succ j).vertexSet_mono hxj.1)
    exact hdisj.symm

/-- Every vertex outside the initial graph is introduced by a unique displayed ear. -/
theorem existsUnique_mem_newVertexSet (d : G.EarDecomposition H) {x : α}
    (hx : x ∈ V(H)) (hx0 : x ∉ V(d.initial)) :
    ∃! i : Fin d.length, x ∈ d.newVertexSet i := by
  rw [d.vertexSet_eq_union_iUnion_newVertexSet] at hx
  obtain hx | hx := hx
  · exact (hx0 hx).elim
  · have hpair : (Set.univ : Set (Fin d.length)).PairwiseDisjoint d.newVertexSet :=
      d.pairwise_disjoint_newVertexSet.pairwiseDisjoint Set.univ
    simpa using pairwiseDisjoint_unique hpair (by simpa using hx)

/-- Every final vertex either belongs to the initial graph or is introduced by a unique ear. -/
theorem mem_initial_or_existsUnique_mem_newVertexSet (d : G.EarDecomposition H) {x : α}
    (hx : x ∈ V(H)) :
    x ∈ V(d.initial) ∨ ∃! i : Fin d.length, x ∈ d.newVertexSet i := by
  by_cases hx0 : x ∈ V(d.initial)
  · exact Or.inl hx0
  · exact Or.inr (d.existsUnique_mem_newVertexSet hx hx0)

/-- Every final edge belongs either to the initial graph or to a unique displayed ear. -/
theorem mem_edgeSet_initial_or_existsUnique_mem_edges_walkAt (d : G.EarDecomposition H)
    {e : β} (he : e ∈ E(H)) :
    e ∈ E(d.initial) ∨ ∃! i : Fin d.length, e ∈ (d.walkAt i).2.2.edges := by
  rw [d.edgeSet_eq_union_iUnion] at he
  simp only [mem_union, mem_iUnion] at he
  rcases he with he | ⟨i, hei⟩
  · exact Or.inl he
  · right
    have hmem (j : Fin d.length) :
        e ∈ (d.walkAt j).2.2.edges ↔ e ∈ E((d.earAt j).2.toGraph) := by
      rw [d.walkAt_eq, (d.earAt j).2.edgeSet_toGraph]
      simp only [mem_ofPred_eq]
    have hpair : (Set.univ : Set (Fin d.length)).PairwiseDisjoint
        (fun j ↦ E((d.earAt j).2.toGraph)) :=
      d.pairwise_disjoint_edgeSet_earAt.pairwiseDisjoint Set.univ
    have hiUnion : e ∈ ⋃ j ∈ (Set.univ : Set (Fin d.length)), E((d.earAt j).2.toGraph) := by
      simp only [mem_iUnion]
      exact ⟨i, Set.mem_univ i, hei⟩
    obtain ⟨j, hj, huniq⟩ := pairwiseDisjoint_unique hpair hiUnion
    exact ⟨j, (hmem j).mpr hj.2, fun k hk ↦ huniq k ⟨Set.mem_univ k, (hmem k).mp hk⟩⟩

end Graph.EarDecomposition
