/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Block

/-!
# Vertex blocks of multigraphs

Vertex blocks and cut vertices do not see loops or parallel-edge multiplicities. This file
therefore transports the simple-graph block theory to a multigraph through its underlying simple
graph on the actual vertices. Since native multigraph cut vertices agree with the cut vertices of
the simplification (`Graph.isCutVertex_iff_toSimpleGraph_isCutVertex`), the simple-graph block
incidence criteria transfer directly.

In particular, every nonloop edge of a finite-vertex multigraph has both endpoints in a unique
vertex block. Parallel edges have the same endpoint block, while loops lie in every induced block
containing their incident vertex; vertex blocks are not intended to partition loop identities.

The block convention follows R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics
173, Springer, 2017, Section 3.1.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Vertex blocks -/

/-- A vertex block of a multigraph is a block of its underlying simple graph on the actual
vertices. Thus loops and parallel edges do not change the collection of vertex blocks. -/
abbrev IsBlock (G : Graph α β) (B : Set V(G)) : Prop :=
  G.toSimpleGraph.IsBlock B

/-- In a finite-vertex multigraph, a native cut vertex is exactly an actual vertex lying in two
distinct vertex blocks. -/
theorem isCutVertex_iff_exists_isBlock_ne [Finite V(G)] {v : V(G)} :
    G.IsCutVertex v ↔
      ∃ B C : Set V(G), G.IsBlock B ∧ G.IsBlock C ∧ B ≠ C ∧ v ∈ B ∧ v ∈ C := by
  rw [isCutVertex_iff_toSimpleGraph_isCutVertex v.property,
    SimpleGraph.isCutVertex_iff_exists_isBlock_ne]

/-- In a finite-vertex multigraph, an actual vertex is not a cut vertex exactly when it lies in a
unique vertex block. -/
theorem not_isCutVertex_iff_existsUnique_isBlock_mem [Finite V(G)] {v : V(G)} :
    ¬G.IsCutVertex v ↔ ∃! B : Set V(G), G.IsBlock B ∧ v ∈ B := by
  rw [isCutVertex_iff_toSimpleGraph_isCutVertex v.property,
    SimpleGraph.not_isCutVertex_iff_existsUnique_isBlock_mem]

/-- Two vertex blocks containing both ends of the same nonloop edge are equal. In particular,
parallel edge identities determine the same vertex block. -/
theorem IsBlock.eq_of_isLink_mem {B C : Set V(G)} {e : β} {x y : α}
    (hB : G.IsBlock B) (hC : G.IsBlock C) (h : G.IsLink e x y) (hxy : x ≠ y)
    (hxB : (⟨x, h.left_mem⟩ : V(G)) ∈ B) (hyB : (⟨y, h.right_mem⟩ : V(G)) ∈ B)
    (hxC : (⟨x, h.left_mem⟩ : V(G)) ∈ C) (hyC : (⟨y, h.right_mem⟩ : V(G)) ∈ C) :
    B = C := by
  have hadj : G.toSimpleGraph.Adj (⟨x, h.left_mem⟩ : V(G)) ⟨y, h.right_mem⟩ :=
    ⟨fun h' ↦ hxy (congrArg Subtype.val h'), e, h⟩
  apply SimpleGraph.IsBlock.eq_of_adj_mem hB hC hadj
  exacts [hxB, hyB, hxC, hyC]

/-- Every nonloop edge of a finite-vertex multigraph has both endpoints in a unique vertex block.
The edge identity is retained in the hypothesis, so the result applies separately to parallel
edges, even though they determine the same block. -/
theorem IsLink.existsUnique_isBlock_superset_pair [Finite V(G)] {e : β} {x y : α}
    (h : G.IsLink e x y) (hxy : x ≠ y) :
    ∃! B : Set V(G), G.IsBlock B ∧
      {(⟨x, h.left_mem⟩ : V(G)), ⟨y, h.right_mem⟩} ⊆ B := by
  have hadj : G.toSimpleGraph.Adj ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
    ⟨fun h' ↦ hxy (congrArg Subtype.val h'), e, h⟩
  exact hadj.existsUnique_isBlock_superset_pair

/-- A vertex lying in two distinct multigraph vertex blocks is a native cut vertex. This direction
does not require finiteness. -/
theorem IsBlock.isCutVertex_of_ne {B C : Set V(G)} {v : V(G)} (hB : G.IsBlock B)
    (hC : G.IsBlock C) (hBC : B ≠ C) (hvB : v ∈ B) (hvC : v ∈ C) :
    G.IsCutVertex v := by
  rw [isCutVertex_iff_toSimpleGraph_isCutVertex v.property]
  exact SimpleGraph.IsBlock.isCutVertex_of_ne hB hC hBC hvB hvC

end Graph
