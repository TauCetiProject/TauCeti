/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Block.Basic

/-!
# The block--cut incidence graph

The block--cut incidence graph of a simple graph has one vertex for every block and one vertex
for every cut vertex.  A block vertex is adjacent to a cut-vertex vertex exactly when the cut
vertex belongs to the block.  This file constructs the graph and gives its incidence,
bipartition, and reachability interfaces.

For a finite original vertex type, every original vertex has a canonical location in the
incidence graph: a cut vertex is sent to its cut-vertex node, while every other vertex is sent
to the unique block containing it.  Two original vertices are reachable exactly when their
locations in the incidence graph are reachable.  This is the representation needed to compare
the connected components of the two graphs and to recover separation from paths in the
block--cut forest.

The construction follows R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Section 3.1.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {u v : V}

/-! ### Incidence data -/

/-- The type of blocks of a simple graph. -/
abbrev Block (G : SimpleGraph V) := {B : Set V // G.IsBlock B}

/-- The type of cut vertices of a simple graph. -/
abbrev CutVertex (G : SimpleGraph V) := {v : V // G.IsCutVertex v}

/-- The vertices of the block--cut incidence graph: blocks on the left and cut vertices on the
right. -/
abbrev BlockCutVertex (G : SimpleGraph V) := G.Block ⊕ G.CutVertex

/-- An incidence of a block with a cut vertex that it contains. -/
abbrev BlockCutIncidence (G : SimpleGraph V) :=
  {p : G.Block × G.CutVertex // p.2.1 ∈ p.1.1}

/-- The block--cut incidence graph.  Its edges are exactly the incidences between blocks and the
cut vertices they contain. -/
def blockCutGraph (G : SimpleGraph V) : SimpleGraph G.BlockCutVertex :=
  SimpleGraph.fromRel fun x y ↦
    ∃ B : G.Block, ∃ v : G.CutVertex, x = .inl B ∧ y = .inr v ∧ v.1 ∈ B.1

@[simp]
theorem blockCutGraph_adj_inl_inr (B : G.Block) (v : G.CutVertex) :
    G.blockCutGraph.Adj (.inl B) (.inr v) ↔ v.1 ∈ B.1 := by
  simp [blockCutGraph]

@[simp]
theorem blockCutGraph_adj_inr_inl (v : G.CutVertex) (B : G.Block) :
    G.blockCutGraph.Adj (.inr v) (.inl B) ↔ v.1 ∈ B.1 := by
  rw [adj_comm, blockCutGraph_adj_inl_inr]

@[simp]
theorem not_blockCutGraph_adj_inl_inl (B C : G.Block) :
    ¬G.blockCutGraph.Adj (.inl B) (.inl C) := by
  simp [blockCutGraph]

@[simp]
theorem not_blockCutGraph_adj_inr_inr (v w : G.CutVertex) :
    ¬G.blockCutGraph.Adj (.inr v) (.inr w) := by
  simp [blockCutGraph]

/-- The block nodes and cut-vertex nodes form the canonical bipartition of the incidence graph. -/
theorem isBipartiteWith_blockCutGraph :
    G.blockCutGraph.IsBipartiteWith (range Sum.inl) (range Sum.inr) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨B, rfl⟩ ⟨v, h⟩
    exact Sum.inr_ne_inl h
  mem_of_adj := by
    rintro (B | v) (C | w) h
    · exact (not_blockCutGraph_adj_inl_inl B C h).elim
    · exact .inl ⟨⟨B, rfl⟩, ⟨w, rfl⟩⟩
    · exact .inr ⟨⟨v, rfl⟩, ⟨C, rfl⟩⟩
    · exact (not_blockCutGraph_adj_inr_inr v w h).elim

/-- The neighbours of a block node are precisely its cut vertices. -/
theorem neighborSet_blockCutGraph_inl (B : G.Block) :
    G.blockCutGraph.neighborSet (.inl B) =
      Sum.inr '' {v : G.CutVertex | v.1 ∈ B.1} := by
  ext x
  rcases x with C | v
  · simp
  · simp

/-- The neighbours of a cut-vertex node are precisely the blocks containing it. -/
theorem neighborSet_blockCutGraph_inr (v : G.CutVertex) :
    G.blockCutGraph.neighborSet (.inr v) =
      Sum.inl '' {B : G.Block | v.1 ∈ B.1} := by
  ext x
  rcases x with B | w
  · simp
  · simp

/-- Incidences inject into the edge set of the block--cut graph. -/
def BlockCutIncidence.toEdge (i : G.BlockCutIncidence) : G.blockCutGraph.edgeSet :=
  ⟨s(.inl i.1.1, .inr i.1.2), by simpa using i.2⟩

/-- Distinct block--cut incidences give distinct edges. -/
theorem BlockCutIncidence.toEdge_injective :
    Function.Injective (BlockCutIncidence.toEdge (G := G)) := by
  rintro ⟨⟨B, v⟩, hv⟩ ⟨⟨C, w⟩, hw⟩ h
  rcases Sym2.eq_iff.mp (congr_arg Subtype.val h) with h' | h'
  · apply Subtype.ext
    exact Prod.ext (Sum.inl_injective h'.1) (Sum.inr_injective h'.2)
  · exact (Sum.inl_ne_inr h'.1).elim

private theorem BlockCutIncidence.toEdge_surjective :
    Function.Surjective (BlockCutIncidence.toEdge (G := G)) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    rcases x with B | v <;> rcases y with C | w
    · simp at he
    · exact ⟨⟨⟨B, w⟩, by simpa using he⟩, rfl⟩
    · exact ⟨⟨⟨C, v⟩, by simpa using he⟩, by
        apply Subtype.ext
        exact Sym2.eq_swap⟩
    · simp at he

/-- Edges of the block--cut graph are equivalent to block--cut-vertex incidences. -/
noncomputable def blockCutIncidenceEquivEdgeSet (G : SimpleGraph V) :
    G.BlockCutIncidence ≃ G.blockCutGraph.edgeSet :=
  Equiv.ofBijective BlockCutIncidence.toEdge
    ⟨BlockCutIncidence.toEdge_injective, BlockCutIncidence.toEdge_surjective⟩

/-! ### Original vertices in the incidence graph -/

/-- The unique block containing a vertex that is not a cut vertex. -/
noncomputable def blockOfNotCutVertex [Finite V] (G : SimpleGraph V) (v : V)
    (hv : ¬G.IsCutVertex v) : G.Block :=
  ⟨((G.not_isCutVertex_iff_existsUnique_isBlock_mem).mp hv).choose,
    ((G.not_isCutVertex_iff_existsUnique_isBlock_mem).mp hv).choose_spec.1.1⟩

/-- A non-cut vertex belongs to its unique block. -/
theorem mem_blockOfNotCutVertex [Finite V] (G : SimpleGraph V) (v : V)
    (hv : ¬G.IsCutVertex v) : v ∈ (G.blockOfNotCutVertex v hv).1 :=
  ((G.not_isCutVertex_iff_existsUnique_isBlock_mem).mp hv).choose_spec.1.2

/-- Any block containing a non-cut vertex is its canonical block. -/
theorem blockOfNotCutVertex_eq [Finite V] (G : SimpleGraph V) (v : V)
    (hv : ¬G.IsCutVertex v) (B : G.Block) (hvB : v ∈ B.1) :
    G.blockOfNotCutVertex v hv = B := by
  apply Subtype.ext
  exact (((G.not_isCutVertex_iff_existsUnique_isBlock_mem).mp hv).choose_spec.2 B
    ⟨B.2, hvB⟩).symm

/-- The canonical location of an original vertex in the block--cut graph.  Cut vertices use their
cut-vertex node; every other vertex uses its unique block node. -/
noncomputable def blockCutVertexOf [Finite V] (G : SimpleGraph V) (v : V) :
    G.BlockCutVertex := by
  classical
  exact if hv : G.IsCutVertex v then .inr ⟨v, hv⟩ else .inl (G.blockOfNotCutVertex v hv)

/-- A cut vertex is located at its cut-vertex node. -/
@[simp]
theorem blockCutVertexOf_eq_inr [Finite V] (G : SimpleGraph V) (v : V)
    (hv : G.IsCutVertex v) : G.blockCutVertexOf v = .inr ⟨v, hv⟩ := by
  simp [blockCutVertexOf, hv]

/-- A non-cut vertex is located at its unique block node. -/
@[simp]
theorem blockCutVertexOf_eq_inl [Finite V] (G : SimpleGraph V) (v : V)
    (hv : ¬G.IsCutVertex v) :
    G.blockCutVertexOf v = .inl (G.blockOfNotCutVertex v hv) := by
  simp [blockCutVertexOf, hv]

/-- The locations of adjacent original vertices are reachable in the block--cut graph. -/
theorem Adj.reachable_blockCutVertexOf [Finite V] (h : G.Adj u v) :
    G.blockCutGraph.Reachable (G.blockCutVertexOf u) (G.blockCutVertexOf v) := by
  obtain ⟨B, ⟨hB, huvB⟩, -⟩ := h.existsUnique_isBlock_superset_pair
  have huB : u ∈ B := huvB (by simp)
  have hvB : v ∈ B := huvB (by simp)
  by_cases hu : G.IsCutVertex u <;> by_cases hv : G.IsCutVertex v
  · rw [G.blockCutVertexOf_eq_inr u hu, G.blockCutVertexOf_eq_inr v hv]
    exact (Adj.reachable (blockCutGraph_adj_inr_inl ⟨u, hu⟩ ⟨B, hB⟩ |>.2 huB)).trans
      (Adj.reachable (blockCutGraph_adj_inl_inr ⟨B, hB⟩ ⟨v, hv⟩ |>.2 hvB))
  · rw [G.blockCutVertexOf_eq_inr u hu, G.blockCutVertexOf_eq_inl v hv,
      G.blockOfNotCutVertex_eq v hv ⟨B, hB⟩ hvB]
    exact Adj.reachable (blockCutGraph_adj_inr_inl ⟨u, hu⟩ ⟨B, hB⟩ |>.2 huB)
  · rw [G.blockCutVertexOf_eq_inl u hu, G.blockCutVertexOf_eq_inr v hv,
      G.blockOfNotCutVertex_eq u hu ⟨B, hB⟩ huB]
    exact Adj.reachable (blockCutGraph_adj_inl_inr ⟨B, hB⟩ ⟨v, hv⟩ |>.2 hvB)
  · rw [G.blockCutVertexOf_eq_inl u hu, G.blockCutVertexOf_eq_inl v hv,
      G.blockOfNotCutVertex_eq u hu ⟨B, hB⟩ huB,
      G.blockOfNotCutVertex_eq v hv ⟨B, hB⟩ hvB]

/-- Reachability of original vertices maps to reachability of their locations in the block--cut
graph. -/
theorem Reachable.blockCutVertexOf [Finite V] (h : G.Reachable u v) :
    G.blockCutGraph.Reachable (G.blockCutVertexOf u) (G.blockCutVertexOf v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih => exact (Adj.reachable_blockCutVertexOf hadj).trans ih

/-- An original vertex is reachable from every vertex in its canonical block. -/
theorem reachable_of_mem_blockOfNotCutVertex [Finite V] (G : SimpleGraph V) (v w : V)
    (hv : ¬G.IsCutVertex v) (hw : w ∈ (G.blockOfNotCutVertex v hv).1) :
    G.Reachable v w := by
  exact ((G.blockOfNotCutVertex v hv).2.connected
    ⟨v, G.mem_blockOfNotCutVertex v hv⟩ ⟨w, hw⟩).map
      ⟨Subtype.val, fun h ↦ h⟩

/-! ### Reachability and connectivity -/

/-- An original vertex represented by a block--cut vertex.  A block node is represented by an
arbitrary vertex of that nonempty block, and a cut-vertex node represents itself. -/
noncomputable def BlockCutVertex.rep (x : G.BlockCutVertex) : V :=
  match x with
  | .inl B => B.2.nonempty.choose
  | .inr v => v.1

private theorem BlockCutVertex.rep_inl (B : G.Block) :
    BlockCutVertex.rep (.inl B) = B.2.nonempty.choose :=
  by simp [BlockCutVertex.rep]

@[simp]
theorem BlockCutVertex.rep_inr (v : G.CutVertex) : BlockCutVertex.rep (.inr v) = v.1 :=
  by simp [BlockCutVertex.rep]

/-- The representative of a block node belongs to that block. -/
theorem BlockCutVertex.rep_inl_mem (B : G.Block) :
    BlockCutVertex.rep (.inl B) ∈ B.1 :=
  B.2.nonempty.choose_spec

/-- Representatives of adjacent block--cut vertices are reachable in the original graph. -/
theorem BlockCutVertex.reachable_rep_of_adj {x y : G.BlockCutVertex}
    (h : G.blockCutGraph.Adj x y) : G.Reachable x.rep y.rep := by
  rcases x with B | v <;> rcases y with C | w
  · exact (not_blockCutGraph_adj_inl_inl B C h).elim
  · exact (B.2.connected ⟨_, BlockCutVertex.rep_inl_mem B⟩
      ⟨_, (blockCutGraph_adj_inl_inr B w).mp h⟩).map
        ⟨Subtype.val, fun h ↦ h⟩
  · exact ((C.2.connected ⟨_, BlockCutVertex.rep_inl_mem C⟩
      ⟨_, (blockCutGraph_adj_inr_inl v C).mp h⟩).map
        ⟨Subtype.val, fun h ↦ h⟩).symm
  · exact (not_blockCutGraph_adj_inr_inr v w h).elim

/-- Reachability in the block--cut graph gives reachability of representatives in the original
graph. -/
theorem Reachable.blockCutVertex_rep {x y : G.BlockCutVertex}
    (h : G.blockCutGraph.Reachable x y) : G.Reachable x.rep y.rep := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih => exact (BlockCutVertex.reachable_rep_of_adj hadj).trans ih

/-- An original vertex is reachable from the representative of its canonical location in the
block--cut graph. -/
theorem reachable_rep_blockCutVertexOf [Finite V] (G : SimpleGraph V) (v : V) :
    G.Reachable v (G.blockCutVertexOf v).rep := by
  by_cases hv : G.IsCutVertex v
  · rw [G.blockCutVertexOf_eq_inr v hv, BlockCutVertex.rep_inr]
  · rw [G.blockCutVertexOf_eq_inl v hv, BlockCutVertex.rep_inl]
    exact G.reachable_of_mem_blockOfNotCutVertex v _ hv
      (G.blockOfNotCutVertex v hv).2.nonempty.choose_spec

/-- Every block--cut vertex reaches the canonical location of its representative. -/
theorem BlockCutVertex.reachable_blockCutVertexOf_rep [Finite V] (x : G.BlockCutVertex) :
    G.blockCutGraph.Reachable x (G.blockCutVertexOf x.rep) := by
  rcases x with B | v
  · by_cases hv : G.IsCutVertex (BlockCutVertex.rep (.inl B))
    · rw [G.blockCutVertexOf_eq_inr _ hv]
      exact Adj.reachable ((blockCutGraph_adj_inl_inr B ⟨_, hv⟩).mpr
        (BlockCutVertex.rep_inl_mem B))
    · rw [G.blockCutVertexOf_eq_inl _ hv,
        G.blockOfNotCutVertex_eq _ hv B (BlockCutVertex.rep_inl_mem B)]
  · rw [BlockCutVertex.rep_inr, G.blockCutVertexOf_eq_inr v.1 v.2]

/-- Original vertices are reachable exactly when their canonical locations in the block--cut
graph are reachable. -/
theorem reachable_blockCutVertexOf_iff [Finite V] :
    G.blockCutGraph.Reachable (G.blockCutVertexOf u) (G.blockCutVertexOf v) ↔
      G.Reachable u v := by
  constructor
  · intro h
    exact (G.reachable_rep_blockCutVertexOf u).trans
      (h.blockCutVertex_rep.trans (G.reachable_rep_blockCutVertexOf v).symm)
  · exact Reachable.blockCutVertexOf

/-- The block--cut graph is preconnected exactly when the original graph is preconnected. -/
theorem preconnected_blockCutGraph_iff [Finite V] :
    G.blockCutGraph.Preconnected ↔ G.Preconnected := by
  constructor
  · intro h u v
    exact reachable_blockCutVertexOf_iff.mp (h (G.blockCutVertexOf u) (G.blockCutVertexOf v))
  · intro h x y
    exact x.reachable_blockCutVertexOf_rep.trans
      ((h x.rep y.rep).blockCutVertexOf.trans y.reachable_blockCutVertexOf_rep.symm)

/-- The block--cut graph is connected exactly when the original graph is connected. -/
@[simp]
theorem connected_blockCutGraph_iff [Finite V] :
    G.blockCutGraph.Connected ↔ G.Connected := by
  constructor
  · intro h
    exact { preconnected := preconnected_blockCutGraph_iff.mp h.preconnected
            nonempty := h.nonempty.map BlockCutVertex.rep }
  · intro h
    exact { preconnected := preconnected_blockCutGraph_iff.mpr h.preconnected
            nonempty := h.nonempty.map G.blockCutVertexOf }

end SimpleGraph
