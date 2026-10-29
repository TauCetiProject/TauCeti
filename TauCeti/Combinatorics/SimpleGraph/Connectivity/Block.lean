/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CutVertex

import Mathlib.Order.Preorder.Finite

/-!
# Blocks of simple graphs

A block is a maximal set of vertices whose induced graph is connected and has no cut vertex.
Singleton isolated vertices and the endpoints of bridge edges are therefore retained as blocks;
this convention makes blocks cover every vertex and every edge, and is the one used by the
block--cut incidence graph.

This file introduces the block predicate and its basic maximality API.  It also proves that every
vertex, and both ends of every edge, lie in some block when the vertex type is finite.  These
existence results are the starting point for the later uniqueness and intersection theory of
blocks.

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

end SimpleGraph
