/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CutVertex

import Mathlib.Order.Preorder.Finite
import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Blocks of simple graphs

A block is a maximal set of vertices whose induced graph is connected and has no cut vertex.
Singleton isolated vertices and the endpoints of bridge edges are therefore retained as blocks;
this convention makes blocks cover every vertex and every edge, and is the one used by the
block--cut incidence graph.

This file introduces the block predicate and its basic maximality API. It proves that every
vertex, and both ends of every edge, lie in some block when the vertex type is finite. Distinct
blocks meet in at most one vertex, so the block containing the endpoints of an edge is unique.

The definition follows R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Section 3.1, with isolated vertices included as singleton blocks.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {B C : Set V} {u v : V}

/-! ### Blocks -/

/-- A block of a simple graph is a maximal vertex set inducing a connected graph with no cut
vertex. In particular, isolated vertices are singleton blocks and bridge edges give two-vertex
blocks. -/
def IsBlock (G : SimpleGraph V) (B : Set V) : Prop :=
  Maximal (fun C : Set V ↦
    (G.induce C).Connected ∧ ∀ v, ¬(G.induce C).IsCutVertex v) B

/-- The defining characterization of a block, including its maximality among connected induced
subgraphs without cut vertices. -/
theorem isBlock_iff : G.IsBlock B ↔
    (G.induce B).Connected ∧
      (∀ v, ¬(G.induce B).IsCutVertex v) ∧
      ∀ ⦃C⦄, (G.induce C).Connected →
        (∀ v, ¬(G.induce C).IsCutVertex v) → B ⊆ C → B = C := by
  rw [IsBlock, maximal_subset_iff]
  constructor
  · rintro ⟨⟨hconn, hcut⟩, hmax⟩
    exact ⟨hconn, hcut, fun {C} hconn hcut hBC ↦ hmax ⟨hconn, hcut⟩ hBC⟩
  · rintro ⟨hconn, hcut, hmax⟩
    exact ⟨⟨hconn, hcut⟩, fun _ ⟨hconn, hcut⟩ hBC ↦ hmax hconn hcut hBC⟩

/-- The graph induced by a block is connected. -/
theorem IsBlock.connected (hB : G.IsBlock B) : (G.induce B).Connected :=
  hB.prop.1

/-- The graph induced by a block has no cut vertex. -/
theorem IsBlock.not_isCutVertex (hB : G.IsBlock B) (v : B) :
    ¬(G.induce B).IsCutVertex v :=
  hB.prop.2 v

/-- A block is nonempty. -/
theorem IsBlock.nonempty (hB : G.IsBlock B) : B.Nonempty :=
  let ⟨v⟩ := hB.connected.nonempty
  ⟨v, v.property⟩

/-- A block equals any larger vertex set that also induces a connected graph without cut
vertices. -/
theorem IsBlock.eq_of_subset (hB : G.IsBlock B) (hconn : (G.induce C).Connected)
    (hcut : ∀ v, ¬(G.induce C).IsCutVertex v) (hBC : B ⊆ C) : B = C :=
  Maximal.eq_of_subset hB ⟨hconn, hcut⟩ hBC

/-! ### Existence -/

/-- In a finite graph, every connected induced subgraph without cut vertices is contained in a
block. -/
theorem exists_isBlock_superset [Finite V] (hconn : (G.induce B).Connected)
    (hcut : ∀ v, ¬(G.induce B).IsCutVertex v) :
    ∃ C, G.IsBlock C ∧ B ⊆ C := by
  let P : Set (Set V) :=
    {C | (G.induce C).Connected ∧ ∀ v, ¬(G.induce C).IsCutVertex v}
  have hBP : B ∈ P := ⟨hconn, hcut⟩
  obtain ⟨C, hBC, hC⟩ := P.toFinite.exists_le_maximal hBP
  exact ⟨C, by simpa only [IsBlock, P, Set.mem_ofPred_eq] using hC, hBC⟩

/-- Every vertex of a finite simple graph belongs to a block. -/
theorem exists_isBlock_mem [Finite V] (G : SimpleGraph V) (v : V) :
    ∃ B, G.IsBlock B ∧ v ∈ B := by
  have hconn : (G.induce {v}).Connected := by
    rw [G.induce_singleton_eq_top]
    exact Connected.of_subsingleton
  obtain ⟨B, hB, hvB⟩ := exists_isBlock_superset hconn (G.not_isCutVertex_induce_singleton v)
  exact ⟨B, hB, hvB (Set.mem_singleton v)⟩

/-- A singleton is a block exactly when its vertex is isolated. -/
@[simp]
theorem isBlock_singleton_iff_isIsolated (G : SimpleGraph V) (v : V) :
    G.IsBlock {v} ↔ G.IsIsolated v := by
  constructor
  · intro hB w hvw
    have heq : ({v} : Set V) = {v, w} :=
      hB.eq_of_subset (G.induce_pair_connected_of_adj hvw) (G.not_isCutVertex_induce_pair v w)
        (Set.singleton_subset_iff.mpr (Set.mem_insert v {w}))
    have hw : w ∈ ({v} : Set V) := by
      rw [heq]
      simp
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    exact G.irrefl (hwv ▸ hvw)
  · intro hv
    rw [IsBlock, maximal_subset_iff]
    have hconn : (G.induce {v}).Connected := by
      rw [G.induce_singleton_eq_top]
      exact Connected.of_subsingleton
    refine ⟨⟨hconn, G.not_isCutVertex_induce_singleton v⟩, ?_⟩
    rintro C ⟨hconn, -⟩ hvC
    apply Set.Subset.antisymm
    · exact hvC
    · intro x hx
      have hxv : x = v := by
        by_contra hxv
        have hreach : G.Reachable x v :=
          (hconn.preconnected ⟨x, hx⟩ ⟨v, hvC (Set.mem_singleton v)⟩).map
            (Embedding.induce C).toHom
        exact (not_reachable_of_neighborSet_right_eq_empty hxv hv.neighborSet_eq_empty) hreach
      exact hxv ▸ Set.mem_singleton v

/-- Every edge of a finite simple graph has both endpoints in some block. -/
theorem Adj.exists_isBlock_superset_pair [Finite V] (h : G.Adj u v) :
    ∃ B, G.IsBlock B ∧ {u, v} ⊆ B :=
  exists_isBlock_superset (G.induce_pair_connected_of_adj h) (G.not_isCutVertex_induce_pair u v)

/-! ### Intersections and edge uniqueness -/

private theorem IsBlock.exists_walk_avoiding (hB : G.IsBlock B)
    {a z x : V} (ha : a ∈ B) (hz : z ∈ B) (hax : a ≠ x) (hzx : z ≠ x) :
    ∃ p : (G.induce B).Walk ⟨a, ha⟩ ⟨z, hz⟩,
      ∀ y ∈ p.support, (y : V) ≠ x := by
  by_cases hx : x ∈ B
  · let aB : B := ⟨a, ha⟩
    let zB : B := ⟨z, hz⟩
    let xB : B := ⟨x, hx⟩
    have hreach : (Graph.ofSimpleGraph (G.induce B)).Reachable aB zB :=
      (reachable_ofSimpleGraph_iff _ _ _).2 (hB.connected.preconnected aB zB)
    have hdel : ((Graph.ofSimpleGraph (G.induce B)).deleteVerts {xB}).Reachable aB zB := by
      by_contra hn
      apply hB.not_isCutVertex xB
      rw [SimpleGraph.isCutVertex_def, Graph.isCutVertex_def]
      exact ⟨aB, zB, by simpa [aB, xB], by simpa [zB, xB], hreach, hn⟩
    obtain ⟨p, -, hp⟩ := Graph.reachable_deleteVerts_iff_exists_walk.mp hdel
    refine ⟨p.toSimpleGraph, ?_⟩
    intro y hy hyx
    have hyp : y ∉ ({xB} : Set B) := hp y (by simpa using hy)
    apply hyp
    simp only [Set.mem_singleton_iff]
    exact Subtype.ext hyx
  · exact (hB.connected.preconnected ⟨a, ha⟩ ⟨z, hz⟩).elim fun p ↦
      ⟨p, fun y _ hyx ↦ hx (hyx ▸ y.property)⟩

private theorem IsBlock.not_isCutVertex_induce_union (hB : G.IsBlock B)
    (hC : G.IsBlock C) {u v : V} (huB : u ∈ B) (huC : u ∈ C)
    (hvB : v ∈ B) (hvC : v ∈ C) (huv : u ≠ v)
    (x : ↑(B ∪ C)) : ¬(G.induce (B ∪ C)).IsCutVertex x := by
  classical
  -- One of the two common vertices survives deletion of `x` and serves as a hub.
  obtain ⟨z, hzB, hzC, hzx⟩ : ∃ z, z ∈ B ∧ z ∈ C ∧ z ≠ x.1 := by
    by_cases hxu : x.1 = u
    · exact ⟨v, hvB, hvC, fun hvx ↦ huv (hxu.symm.trans hvx.symm)⟩
    · exact ⟨u, huB, huC, Ne.symm hxu⟩
  let zU : ↑(B ∪ C) := ⟨z, Or.inl hzB⟩
  -- Connect a vertex to the hub inside either block, retaining avoidance under inclusion.
  have connect (a : ↑(B ∪ C)) (hax : a ≠ x) :
      ∃ p : (G.induce (B ∪ C)).Walk a zU,
        ∀ y ∈ p.support, y ≠ x := by
    have hax' : a.1 ≠ x.1 := fun h ↦ hax (Subtype.ext h)
    have map_avoiding {D : Set V} (hDU : D ⊆ B ∪ C) {haD : a.1 ∈ D}
        {hzD : z ∈ D} (p : (G.induce D).Walk ⟨a.1, haD⟩ ⟨z, hzD⟩)
        (hp : ∀ y ∈ p.support, (y : V) ≠ x.1) :
        ∃ q : (G.induce (B ∪ C)).Walk a zU,
          ∀ y ∈ q.support, y ≠ x := by
      let q := p.map (G.induceHomOfLE hDU).toHom
      have hq : ∀ y ∈ q.support, y ≠ x := by
        intro y hy hyx
        simp only [q, Walk.support_map] at hy
        obtain ⟨w, hw, hwy⟩ := List.mem_map.mp hy
        apply hp w hw
        exact congrArg Subtype.val (hwy.trans hyx)
      have hstart : (G.induceHomOfLE hDU).toHom ⟨a.1, haD⟩ = a := Subtype.ext rfl
      have hend : (G.induceHomOfLE hDU).toHom ⟨z, hzD⟩ = zU := Subtype.ext rfl
      cases hstart
      cases hend
      exact ⟨q, hq⟩
    have haU : a.1 ∈ B ∨ a.1 ∈ C := a.property
    rcases haU with haB | haC
    · obtain ⟨p, hp⟩ := hB.exists_walk_avoiding haB hzB hax' hzx
      exact map_avoiding Set.subset_union_left p hp
    · obtain ⟨p, hp⟩ := hC.exists_walk_avoiding haC hzC hax' hzx
      exact map_avoiding Set.subset_union_right p hp
  rw [SimpleGraph.isCutVertex_def, Graph.isCutVertex_def]
  rintro ⟨a, b, hax, hbx, -, hn⟩
  obtain ⟨p, hp⟩ := connect a hax
  obtain ⟨q, hq⟩ := connect b hbx
  -- The two hub paths concatenate to a walk in the union avoiding the deleted vertex.
  apply hn
  apply Graph.reachable_deleteVerts_iff_exists_walk.mpr
  refine ⟨(p.append q.reverse).toGraph, by simp, ?_⟩
  intro y hy
  rw [Walk.support_toGraph, Walk.support_append] at hy
  simp only [List.mem_append] at hy
  simp only [Set.mem_singleton_iff]
  rcases hy with hy | hy
  · exact hp y hy
  · apply hq y
    have hy' : y ∈ q.reverse.support := List.mem_of_mem_tail hy
    rw [Walk.support_reverse] at hy'
    simpa using hy'

/-- Two distinct blocks meet in at most one vertex. -/
theorem IsBlock.inter_subsingleton (hB : G.IsBlock B) (hC : G.IsBlock C) (hBC : B ≠ C) :
    (B ∩ C).Subsingleton := by
  intro u hu v hv
  by_contra huv
  have hconn : (G.induce (B ∪ C)).Connected :=
    G.induce_union_connected hB.connected.preconnected hC.connected.preconnected
      ⟨u, hu.1, hu.2⟩
  have hcut : ∀ x, ¬(G.induce (B ∪ C)).IsCutVertex x := fun x ↦
    hB.not_isCutVertex_induce_union hC hu.1 hu.2 hv.1 hv.2 huv x
  have hBU : B = B ∪ C := hB.eq_of_subset hconn hcut Set.subset_union_left
  have hCU : C = B ∪ C := hC.eq_of_subset hconn hcut Set.subset_union_right
  exact hBC (hBU.trans hCU.symm)

/-- Two blocks containing the endpoints of the same edge are equal. -/
theorem IsBlock.eq_of_adj_mem (hB : G.IsBlock B) (hC : G.IsBlock C) (h : G.Adj u v)
    (huB : u ∈ B) (hvB : v ∈ B) (huC : u ∈ C) (hvC : v ∈ C) : B = C := by
  by_contra hBC
  exact h.ne (hB.inter_subsingleton hC hBC ⟨huB, huC⟩ ⟨hvB, hvC⟩)

/-- Every edge of a finite simple graph has both endpoints in a unique block. -/
theorem Adj.existsUnique_isBlock_superset_pair [Finite V] (h : G.Adj u v) :
    ∃! B, G.IsBlock B ∧ {u, v} ⊆ B := by
  obtain ⟨B, hB, huvB⟩ := h.exists_isBlock_superset_pair
  refine ⟨B, ⟨hB, huvB⟩, ?_⟩
  rintro C ⟨hC, huvC⟩
  exact hC.eq_of_adj_mem hB h (huvC (by simp)) (huvC (by simp))
    (huvB (by simp)) (huvB (by simp))

end SimpleGraph
