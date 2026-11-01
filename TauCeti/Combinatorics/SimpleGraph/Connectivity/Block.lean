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

Combining maximality of blocks with the ear lemma
`SimpleGraph.Walk.IsPath.not_isCutVertex_induce_union_support` shows that a vertex lying in two
distinct blocks is a cut vertex.
Conversely, in a finite graph a cut vertex lies in two distinct blocks, giving
`SimpleGraph.isCutVertex_iff_exists_isBlock_ne`; a vertex that is not a cut vertex lies in exactly
one block. These are the incidences of the block--cut forest.

The definition and the cut-vertex characterization follow R. Diestel, *Graph Theory*, 5th ed.,
Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1, with isolated vertices included as
singleton blocks.
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
  -- Connect a vertex to the hub inside either block; the walk stays inside the union.
  have connect (a : ↑(B ∪ C)) (hax : a ≠ x) :
      ∃ p : (G.induce (B ∪ C)).Walk a zU,
        ∀ y ∈ p.support, y ≠ x := by
    have hax' : a.1 ≠ x.1 := fun h ↦ hax (Subtype.ext h)
    obtain ⟨p, hp⟩ : ∃ p : G.Walk a.1 z, ∀ y ∈ p.support, y ∈ B ∪ C ∧ y ≠ x.1 := by
      rcases a.property with haB | haC
      · obtain ⟨p, hp⟩ := exists_walk_forall_mem_support_mem_and_ne hB.connected
          hB.not_isCutVertex haB hzB hax' hzx
        exact ⟨p, fun y hy ↦ ⟨Or.inl (hp y hy).1, (hp y hy).2⟩⟩
      · obtain ⟨p, hp⟩ := exists_walk_forall_mem_support_mem_and_ne hC.connected
          hC.not_isCutVertex haC hzC hax' hzx
        exact ⟨p, fun y hy ↦ ⟨Or.inr (hp y hy).1, (hp y hy).2⟩⟩
    refine ⟨p.induce (B ∪ C) fun y hy ↦ (hp y hy).1, fun y hy hyx ↦ ?_⟩
    rw [Walk.support_induce, List.mem_attachWith] at hy
    exact (hp y hy).2 (congrArg Subtype.val hyx)
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

/-! ### Cut vertices and blocks -/

/-- A vertex lying in two distinct blocks has a neighbour in the first of them. -/
private theorem IsBlock.exists_adj_of_ne (hB : G.IsBlock B) (hC : G.IsBlock C) (hBC : B ≠ C)
    (hvB : v ∈ B) (hvC : v ∈ C) : ∃ u ∈ B, G.Adj v u := by
  -- A vertex of a block other than `v` yields a neighbour of `v` inside that block.
  have hadj {D : Set V} (hD : G.IsBlock D) (hvD : v ∈ D) {d : V} (hdD : d ∈ D) (hdv : d ≠ v) :
      ∃ u ∈ D, G.Adj v u := by
    obtain ⟨p⟩ := hD.connected.preconnected ⟨v, hvD⟩ ⟨d, hdD⟩
    have hp : ¬p.Nil := Walk.not_nil_of_ne fun h ↦ hdv (congrArg Subtype.val h).symm
    exact ⟨p.snd, p.snd.property, induce_adj.1 (Walk.adj_snd hp)⟩
  by_cases h : ∃ d ∈ B, d ≠ v
  · obtain ⟨d, hdB, hdv⟩ := h
    exact hadj hB hvB hdB hdv
  · -- Otherwise `B = {v}`, so `v` is isolated and `C = {v}` as well.
    simp only [not_exists, not_and, not_not] at h
    have hBv : B = {v} := Set.eq_singleton_iff_unique_mem.2 ⟨hvB, h⟩
    have hiso : G.IsIsolated v := (G.isBlock_singleton_iff_isIsolated v).1 (hBv ▸ hB)
    refine (hBC ?_).elim
    rw [hBv, eq_comm, Set.eq_singleton_iff_unique_mem]
    refine ⟨hvC, fun c hcC ↦ by_contra fun hcv ↦ ?_⟩
    obtain ⟨u, -, hvu⟩ := hadj hC hvC hcC hcv
    exact hiso u hvu

/-- A vertex lying in two distinct blocks is a cut vertex. -/
theorem IsBlock.isCutVertex_of_ne (hB : G.IsBlock B) (hC : G.IsBlock C) (hBC : B ≠ C)
    (hvB : v ∈ B) (hvC : v ∈ C) : G.IsCutVertex v := by
  classical
  obtain ⟨u, huB, hvu⟩ := hB.exists_adj_of_ne hC hBC hvB hvC
  obtain ⟨w, hwC, hvw⟩ := hC.exists_adj_of_ne hB hBC.symm hvC hvB
  rw [isCutVertex_iff_exists_forall_walk_mem_support]
  refine ⟨u, w, hvu.ne', hvw.ne', hvu.symm.reachable.trans hvw.reachable, fun p ↦ ?_⟩
  by_contra hvp
  -- A path from `w` to `u` avoiding `v`, closed up by the edge `uv`, is an ear of `C`
  -- containing `u`; maximality of `C` then puts `u` in `B ∩ C`.
  have hvp' : v ∉ p.bypass.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    exact fun h ↦ hvp (p.support_bypass_subset_support h)
  let P := p.bypass.reverse.concat hvu.symm
  have hP : P.IsPath := p.bypass_isPath.reverse.concat hvp' hvu.symm
  have hconn : (G.induce (C ∪ {y | y ∈ P.support})).Connected :=
    induce_union_connected hC.connected.preconnected P.connected_induce_support.preconnected
      ⟨w, hwC, P.start_mem_support⟩
  have hCP := hC.eq_of_subset hconn
    (hP.not_isCutVertex_induce_union_support hC.connected hC.not_isCutVertex hwC hvC)
    Set.subset_union_left
  have huC : u ∈ C := hCP ▸ Or.inr (by simp [P, Walk.support_concat])
  exact hvu.ne (hB.inter_subsingleton hC hBC ⟨hvB, hvC⟩ ⟨huB, huC⟩)

/-- In a finite graph, a cut vertex lies in two distinct blocks. -/
theorem IsCutVertex.exists_isBlock_ne [Finite V] (h : G.IsCutVertex v) :
    ∃ B C, G.IsBlock B ∧ G.IsBlock C ∧ B ≠ C ∧ v ∈ B ∧ v ∈ C := by
  classical
  rw [isCutVertex_iff_exists_forall_walk_mem_support] at h
  obtain ⟨u, w, huv, hwv, ⟨p⟩, hall⟩ := h
  -- A vertex `c ≠ v` reaching `v` reaches a neighbour of `v` along a walk avoiding `v`.
  have hnbr {c : V} (hc : G.Reachable c v) (hcv : c ≠ v) :
      ∃ a, G.Adj a v ∧ ∃ q : G.Walk c a, v ∉ q.support := by
    obtain ⟨p⟩ := hc
    let S : Set V := {y | ∃ q : G.Walk c y, v ∉ q.support}
    have hcS : c ∈ S := ⟨Walk.nil, by simpa using hcv.symm⟩
    have hvS : v ∉ S := fun ⟨q, hq⟩ ↦ hq q.end_mem_support
    obtain ⟨d, -, ⟨q, hq⟩, hd⟩ := p.exists_boundary_dart S hcS hvS
    refine ⟨d.fst, ?_, q, hq⟩
    by_cases hdv : d.snd = v
    · exact hdv ▸ d.adj
    · exact (hd ⟨q.concat d.adj, by simp [Walk.support_concat, hq, Ne.symm hdv]⟩).elim
  obtain ⟨a, hav, qa, hqa⟩ := hnbr ⟨p.takeUntil v (hall p)⟩ huv
  obtain ⟨b, hbv, qb, hqb⟩ := hnbr ⟨(p.dropUntil v (hall p)).reverse⟩ hwv
  obtain ⟨B, hB, havB⟩ := hav.exists_isBlock_superset_pair
  obtain ⟨C, hC, hbvC⟩ := hbv.exists_isBlock_superset_pair
  refine ⟨B, C, hB, hC, fun hBC ↦ ?_, havB (by simp), hbvC (by simp)⟩
  -- Inside a common block, `a` and `b` are joined avoiding `v`, so `u` reaches `w` avoiding `v`.
  subst hBC
  obtain ⟨r, hr⟩ := exists_walk_forall_mem_support_mem_and_ne hB.connected hB.not_isCutVertex
    (havB (by simp)) (hbvC (by simp)) hav.ne hbv.ne
  have hv := hall ((qa.append r).append qb.reverse)
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hv
  rcases hv with (hv | hv) | hv
  · exact hqa hv
  · exact (hr v hv).2 rfl
  · exact hqb hv

/-- **Cut vertices and blocks.** In a finite graph, a vertex is a cut vertex exactly when it lies
in two distinct blocks. -/
theorem isCutVertex_iff_exists_isBlock_ne [Finite V] :
    G.IsCutVertex v ↔ ∃ B C, G.IsBlock B ∧ G.IsBlock C ∧ B ≠ C ∧ v ∈ B ∧ v ∈ C :=
  ⟨IsCutVertex.exists_isBlock_ne, fun ⟨_, _, hB, hC, hBC, hvB, hvC⟩ ↦
    hB.isCutVertex_of_ne hC hBC hvB hvC⟩

/-- In a finite graph, a vertex is not a cut vertex exactly when it lies in a unique block. -/
theorem not_isCutVertex_iff_existsUnique_isBlock_mem [Finite V] :
    ¬G.IsCutVertex v ↔ ∃! B, G.IsBlock B ∧ v ∈ B := by
  rw [isCutVertex_iff_exists_isBlock_ne]
  constructor
  · intro h
    obtain ⟨B, hB, hvB⟩ := G.exists_isBlock_mem v
    refine ⟨B, ⟨hB, hvB⟩, fun C ⟨hC, hvC⟩ ↦ by_contra fun hCB ↦ h ⟨C, B, hC, hB, hCB, hvC, hvB⟩⟩
  · rintro ⟨B, -, huniq⟩ ⟨C, D, hC, hD, hCD, hvC, hvD⟩
    exact hCD ((huniq C ⟨hC, hvC⟩).trans (huniq D ⟨hD, hvD⟩).symm)

end SimpleGraph
