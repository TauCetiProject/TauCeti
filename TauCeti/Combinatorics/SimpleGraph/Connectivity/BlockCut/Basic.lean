/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Block
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The block--cut incidence graph

The block--cut incidence graph of a simple graph has one vertex for each block, one vertex for
each cut vertex, and an edge recording every incidence of a cut vertex with a block.  This file
constructs the graph and gives its basic API: the two vertex kinds, adjacency characterizations,
the canonical bipartition, and the description of each neighborhood.

This incidence graph is the carrier on which the block--cut forest records how blocks are joined
at cut vertices.  In particular, retaining cut vertices as their own kind of vertex distinguishes
several blocks meeting at one original vertex from ordinary adjacency between blocks.

The construction follows R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Section 3.1.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The type of blocks of `G`; these form the block kind of vertex in `G.blockCutGraph`. -/
abbrev BlockVertex := {B : Set V // G.IsBlock B}

/-- The type of cut vertices of `G`; these form the cut-vertex kind of vertex in
`G.blockCutGraph`. -/
abbrev CutVertex := {v : V // G.IsCutVertex v}

/-- The vertices of the block--cut incidence graph, with blocks and cut vertices as its two
parts. -/
abbrev BlockCutVertex := G.BlockVertex ⊕ G.CutVertex

/-- The block--cut incidence graph of `G`.  A block vertex and a cut vertex are adjacent exactly
when the original vertex belongs to the block. -/
def blockCutGraph : SimpleGraph G.BlockCutVertex where
  Adj x y :=
    match x, y with
    | .inl B, .inr v => (v : V) ∈ (B : Set V)
    | .inr v, .inl B => (v : V) ∈ (B : Set V)
    | _, _ => False
  symm := ⟨by rintro (B | v) (C | w) <;> simp_all⟩
  loopless := ⟨by rintro (B | v) <;> simp⟩

@[simp]
theorem not_blockCutGraph_adj_block_block (B C : G.BlockVertex) :
    ¬G.blockCutGraph.Adj (.inl B) (.inl C) := by
  simp [blockCutGraph]

@[simp]
theorem not_blockCutGraph_adj_cutVertex_cutVertex (v w : G.CutVertex) :
    ¬G.blockCutGraph.Adj (.inr v) (.inr w) := by
  simp [blockCutGraph]

/-- A block vertex is adjacent to precisely the cut vertices that it contains. -/
@[simp]
theorem blockCutGraph_adj_block_cutVertex (B : G.BlockVertex) (v : G.CutVertex) :
    G.blockCutGraph.Adj (.inl B) (.inr v) ↔ (v : V) ∈ (B : Set V) :=
  Iff.rfl

/-- A cut vertex is adjacent to precisely the blocks that contain it. -/
@[simp]
theorem blockCutGraph_adj_cutVertex_block (v : G.CutVertex) (B : G.BlockVertex) :
    G.blockCutGraph.Adj (.inr v) (.inl B) ↔ (v : V) ∈ (B : Set V) :=
  Iff.rfl

/-- The displayed block and cut-vertex parts form a bipartition of the block--cut incidence
graph. -/
theorem blockCutGraph_isBipartiteWith :
    G.blockCutGraph.IsBipartiteWith (range Sum.inl) (range Sum.inr) where
  disjoint := Set.isCompl_range_inl_range_inr.disjoint
  mem_of_adj := by
    rintro (B | v) (C | w) h
    · simp at h
    · exact Or.inl ⟨⟨B, rfl⟩, ⟨w, rfl⟩⟩
    · exact Or.inr ⟨⟨v, rfl⟩, ⟨C, rfl⟩⟩
    · simp at h

/-- Every block--cut incidence graph is bipartite. -/
theorem blockCutGraph_isBipartite : G.blockCutGraph.IsBipartite :=
  G.blockCutGraph_isBipartiteWith.isBipartite

/-- The neighbors of a block vertex are exactly its cut vertices. -/
theorem mem_neighborSet_blockCutGraph_block_iff (B : G.BlockVertex) (x : G.BlockCutVertex) :
    x ∈ G.blockCutGraph.neighborSet (.inl B) ↔
      ∃ v : G.CutVertex, x = .inr v ∧ (v : V) ∈ (B : Set V) := by
  rcases x with C | v
  · simp
  · simp [SimpleGraph.mem_neighborSet]

/-- The neighbors of a cut vertex are exactly the blocks that contain it. -/
theorem mem_neighborSet_blockCutGraph_cutVertex_iff (v : G.CutVertex)
    (x : G.BlockCutVertex) :
    x ∈ G.blockCutGraph.neighborSet (.inr v) ↔
      ∃ B : G.BlockVertex, x = .inl B ∧ (v : V) ∈ (B : Set V) := by
  rcases x with B | w
  · simp [SimpleGraph.mem_neighborSet]
  · simp

/-- The neighborhood of a block vertex is canonically equivalent to the cut vertices belonging
to that block. -/
def neighborSetBlockEquiv (B : G.BlockVertex) :
    G.blockCutGraph.neighborSet (.inl B) ≃ {v : G.CutVertex // (v : V) ∈ (B : Set V)} where
  toFun x := by
    rcases x with ⟨C | v, hx⟩
    · simp at hx
    · exact ⟨v, by simpa [SimpleGraph.mem_neighborSet] using hx⟩
  invFun v := ⟨.inr v.1, by simp [SimpleGraph.mem_neighborSet, v.2]⟩
  left_inv x := by
    rcases x with ⟨C | v, hx⟩
    · simp at hx
    · rfl
  right_inv v := rfl

/-- Applying `neighborSetBlockEquiv` preserves the underlying block--cut vertex. -/
@[simp]
theorem neighborSetBlockEquiv_apply_coe (B : G.BlockVertex)
    (x : G.blockCutGraph.neighborSet (.inl B)) :
    Sum.inr ((G.neighborSetBlockEquiv B x) : G.CutVertex) = (x : G.BlockCutVertex) := by
  rcases x with ⟨C | v, hx⟩
  · simp at hx
  · rfl

/-- The inverse of `neighborSetBlockEquiv` includes a cut vertex into the block--cut graph. -/
@[simp]
theorem neighborSetBlockEquiv_symm_apply_coe (B : G.BlockVertex)
    (v : {v : G.CutVertex // (v : V) ∈ (B : Set V)}) :
    ((G.neighborSetBlockEquiv B).symm v : G.BlockCutVertex) = .inr v.1 := by
  simp [neighborSetBlockEquiv]

/-- The neighborhood of a cut vertex is canonically equivalent to the blocks containing that
vertex. -/
def neighborSetCutVertexEquiv (v : G.CutVertex) :
    G.blockCutGraph.neighborSet (.inr v) ≃ {B : G.BlockVertex // (v : V) ∈ (B : Set V)} where
  toFun x := by
    rcases x with ⟨B | w, hx⟩
    · exact ⟨B, by simpa [SimpleGraph.mem_neighborSet] using hx⟩
    · simp at hx
  invFun B := ⟨.inl B.1, by simp [SimpleGraph.mem_neighborSet, B.2]⟩
  left_inv x := by
    rcases x with ⟨B | w, hx⟩
    · rfl
    · simp at hx
  right_inv B := rfl

/-- Applying `neighborSetCutVertexEquiv` preserves the underlying block--cut vertex. -/
@[simp]
theorem neighborSetCutVertexEquiv_apply_coe (v : G.CutVertex)
    (x : G.blockCutGraph.neighborSet (.inr v)) :
    Sum.inl ((G.neighborSetCutVertexEquiv v x) : G.BlockVertex) = (x : G.BlockCutVertex) := by
  rcases x with ⟨B | w, hx⟩
  · rfl
  · simp at hx

/-- The inverse of `neighborSetCutVertexEquiv` includes a block into the block--cut graph. -/
@[simp]
theorem neighborSetCutVertexEquiv_symm_apply_coe (v : G.CutVertex)
    (B : {B : G.BlockVertex // (v : V) ∈ (B : Set V)}) :
    ((G.neighborSetCutVertexEquiv v).symm B : G.BlockCutVertex) = .inl B.1 := by
  simp [neighborSetCutVertexEquiv]

end SimpleGraph
