/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.Graph.Connectivity.Block
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Examples
public import TauCeti.Combinatorics.Graph.Union
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Basic
import Mathlib.Tactic.FinCases

/-!
# The block–cut tree of two triangles sharing a vertex

This file computes the vertex blocks, the cut vertices and the block–cut tree of the multigraph
formed by the triangles `0 — 1 — 2` and `0 — 3 — 4`, which share the vertex `0`, together with a
loop at `0`. Its vertex blocks are the two triangles, its only cut vertex is `0`, and its
block–cut graph is isomorphic to the path on three vertices, with the cut vertex `0` between the
two blocks.

The loop illustrates the vertex-block convention for multigraphs. Vertex blocks are the blocks of
the underlying simple graph, so the loop does not change them, and the loop lies in the subgraph
induced by each of the two blocks. Whereas every nonloop edge lies in a unique vertex block
(`Graph.IsLink.existsUnique_isBlock_superset_pair`), loops at a cut vertex are therefore not
partitioned among the vertex blocks.
-/

public section

namespace TauCeti.Examples.TrianglesSharingVertexBlockCut

open Set SimpleGraph
open scoped Graph

private def loopPart : Graph (Fin 5) (Sym2 (Fin 5)) := Graph.bouquet 0 {s(0, 0)}

private theorem edgeSets_disjoint : Disjoint E(trianglesSharingVertexGraph) E(loopPart) := by
  simp [loopPart]

/-- The triangles `0 — 1 — 2` and `0 — 3 — 4` sharing the vertex `0`, with a loop `s(0, 0)` at
the shared vertex. -/
def graph : Graph (Fin 5) (Sym2 (Fin 5)) :=
  (Graph.Compatible.of_disjoint_edgeSet edgeSets_disjoint).union

/-- Every element of `Fin 5` is an actual vertex of `graph`. -/
@[simp]
theorem mem_vertexSet (i : Fin 5) : i ∈ V(graph) := by
  simp [graph]

/-- An element of `Fin 5`, viewed as an actual vertex of `graph`. -/
abbrev vertex (i : Fin 5) : V(graph) := ⟨i, mem_vertexSet i⟩

/-- The edge `s(0, 0)` is a loop of `graph` at the shared vertex. -/
theorem isLoopAt : graph.IsLoopAt s(0, 0) 0 := by
  simp [graph, loopPart]

/-- The underlying simple graph of `graph` forgets the loop: it is the simple graph of the two
triangles. -/
theorem toSimpleGraph_adj {x y : V(graph)} :
    graph.toSimpleGraph.Adj x y ↔ trianglesSharingVertex.Adj x y := by
  have hadj : graph.Adj x y ↔ trianglesSharingVertex.Adj x y ∨ (x.1 = 0 ∧ y.1 = 0) := by
    simp [graph, loopPart]
  rw [Graph.toSimpleGraph_adj, hadj]
  exact ⟨fun ⟨hxy, h⟩ ↦ h.resolve_right fun ⟨hx, hy⟩ ↦ hxy (Subtype.ext (hx.trans hy.symm)),
    fun h ↦ ⟨fun hxy ↦ h.ne (congrArg Subtype.val hxy), Or.inl h⟩⟩

/-- The first triangle `0 — 1 — 2`, as a set of actual vertices of `graph`. -/
def firstTriangle : Set V(graph) := Subtype.val ⁻¹' {0, 1, 2}

/-- The second triangle `0 — 3 — 4`, as a set of actual vertices of `graph`. -/
def secondTriangle : Set V(graph) := Subtype.val ⁻¹' {0, 3, 4}

@[simp]
theorem mem_firstTriangle {x : V(graph)} : x ∈ firstTriangle ↔ x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 :=
  Iff.rfl

@[simp]
theorem mem_secondTriangle {x : V(graph)} : x ∈ secondTriangle ↔ x.1 = 0 ∨ x.1 = 3 ∨ x.1 = 4 :=
  Iff.rfl

/-- The two triangles are different vertex sets. -/
theorem firstTriangle_ne_secondTriangle : firstTriangle ≠ secondTriangle := by
  intro h
  have h1 : vertex 1 ∈ secondTriangle := h ▸ by simp
  simp at h1

/-! ### Vertex blocks -/

/-- The vertices of a triangle of `graph` through `0` form a vertex block, because any two of them
are adjacent and no edge leaves the triangle except at `0`. -/
private theorem isBlock_preimage {S : Set (Fin 5)} {a : Fin 5} (ha : a ∈ S) (ha0 : a ≠ 0)
    (h0 : 0 ∈ S) (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → trianglesSharingVertex.Adj i j)
    (hclosed : ∀ i ∈ S, ∀ j, i ≠ 0 → trianglesSharingVertex.Adj i j → j ∈ S) :
    graph.IsBlock (Subtype.val ⁻¹' S) := by
  have hB : graph.toSimpleGraph.IsClique (Subtype.val ⁻¹' S) := fun x hx y hy hxy ↦
    toSimpleGraph_adj.mpr (hS _ hx _ hy fun h ↦ hxy (Subtype.ext h))
  have : Nonempty (Subtype.val ⁻¹' S : Set V(graph)) := ⟨⟨vertex a, ha⟩⟩
  refine SimpleGraph.isBlock_iff.mpr ⟨?_, ?_, fun C hconn hcut hBC ↦ ?_⟩
  · rw [induce_eq_top.mpr hB]
    exact connected_top
  · -- Two distinct vertices of a clique are joined by a single edge, avoiding every other vertex.
    refine not_isCutVertex_induce_of_exists_walk fun x _ c hc d hd hcx hdx ↦ ?_
    by_cases hcd : c = d
    · subst hcd
      exact ⟨Walk.nil, by simpa using ⟨hc, hcx⟩⟩
    · exact ⟨Walk.cons (hB hc hd hcd) Walk.nil, by simpa using ⟨⟨hc, hcx⟩, hd, hdx⟩⟩
  refine hBC.antisymm fun y hyC ↦ by_contra fun hyB ↦ ?_
  -- A walk inside `C` from `a` to `y` avoiding `0` would leave the triangle away from `0`.
  obtain ⟨p, hp⟩ := exists_walk_forall_mem_support_mem_and_ne (x := vertex 0) hconn hcut
    (hBC (Set.mem_preimage.mpr ha : vertex a ∈ Subtype.val ⁻¹' S)) hyC
    (fun h ↦ ha0 (congrArg Subtype.val h))
    (fun hy ↦ hyB (hy ▸ h0))
  obtain ⟨d, hd, hdB, hdB'⟩ := p.exists_boundary_dart _ ha hyB
  have hd0 : d.fst ≠ vertex 0 := (hp _ (p.dart_fst_mem_support_of_mem_darts hd)).2
  exact hdB' (hclosed _ hdB _ (fun h ↦ hd0 (Subtype.ext h)) (toSimpleGraph_adj.mp d.adj))

/-- The first triangle is a vertex block. -/
theorem isBlock_firstTriangle : graph.IsBlock firstTriangle :=
  isBlock_preimage (a := 1) (by simp) (by decide) (by simp)
    (by simp only [mem_insert_iff, mem_singleton_iff]; decide)
    (by simp only [mem_insert_iff, mem_singleton_iff]; decide)

/-- The second triangle is a vertex block. -/
theorem isBlock_secondTriangle : graph.IsBlock secondTriangle :=
  isBlock_preimage (a := 3) (by simp) (by decide) (by simp)
    (by simp only [mem_insert_iff, mem_singleton_iff]; decide)
    (by simp only [mem_insert_iff, mem_singleton_iff]; decide)

private theorem exists_adj (x : V(graph)) : ∃ y, graph.toSimpleGraph.Adj x y := by
  have key : ∀ i : Fin 5, trianglesSharingVertex.Adj i (if i = 0 then 1 else 0) := by decide
  exact ⟨vertex (if x.1 = 0 then 1 else 0), toSimpleGraph_adj.mpr (key x.1)⟩

private theorem adj_mem_triangle {x y : V(graph)} (h : graph.toSimpleGraph.Adj x y) :
    x ∈ firstTriangle ∧ y ∈ firstTriangle ∨ x ∈ secondTriangle ∧ y ∈ secondTriangle := by
  have key : ∀ i j : Fin 5, trianglesSharingVertex.Adj i j →
      (i = 0 ∨ i = 1 ∨ i = 2) ∧ (j = 0 ∨ j = 1 ∨ j = 2) ∨
        (i = 0 ∨ i = 3 ∨ i = 4) ∧ (j = 0 ∨ j = 3 ∨ j = 4) := by
    decide
  exact key x.1 y.1 (toSimpleGraph_adj.mp h)

/-- **The vertex blocks of `graph`** are exactly the two triangles. -/
theorem isBlock_iff {B : Set V(graph)} :
    graph.IsBlock B ↔ B = firstTriangle ∨ B = secondTriangle := by
  refine ⟨fun hB ↦ ?_, ?_⟩
  · obtain ⟨v, hvB⟩ := hB.nonempty
    -- The block `B` is not the singleton `{v}`, because `v` has a neighbour.
    obtain ⟨d, hdB, hdv⟩ : ∃ d ∈ B, d ≠ v := by
      by_contra! h
      obtain ⟨w, hvw⟩ := exists_adj v
      exact (graph.toSimpleGraph.isBlock_singleton_iff_isIsolated v).mp
        (Set.eq_singleton_iff_unique_mem.mpr ⟨hvB, h⟩ ▸ hB) w hvw
    -- So `B` contains an edge, and that edge lies in one of the two triangles.
    obtain ⟨p⟩ := hB.connected.preconnected ⟨v, hvB⟩ ⟨d, hdB⟩
    have hp : ¬p.Nil := Walk.not_nil_of_ne fun h ↦ hdv (congrArg Subtype.val h).symm
    have hvu : graph.toSimpleGraph.Adj v p.snd := induce_adj.mp (Walk.adj_snd hp)
    rcases adj_mem_triangle hvu with ⟨hv, hu⟩ | ⟨hv, hu⟩
    · exact Or.inl (hB.eq_of_adj_mem isBlock_firstTriangle hvu hvB p.snd.property hv hu)
    · exact Or.inr (hB.eq_of_adj_mem isBlock_secondTriangle hvu hvB p.snd.property hv hu)
  · rintro (rfl | rfl)
    exacts [isBlock_firstTriangle, isBlock_secondTriangle]

/-- **The cut vertices of `graph`.** The shared vertex `0` is the only cut vertex. -/
theorem isCutVertex_iff {i : Fin 5} : graph.IsCutVertex i ↔ i = 0 := by
  refine (Graph.isCutVertex_iff_exists_isBlock_ne (v := vertex i)).trans ⟨?_, ?_⟩
  · rintro ⟨B, C, hB, hC, hBC, hiB, hiC⟩
    rcases isBlock_iff.mp hB with rfl | rfl <;> rcases isBlock_iff.mp hC with rfl | rfl
    · exact absurd rfl hBC
    · simp only [mem_firstTriangle, mem_secondTriangle] at hiB hiC
      omega
    · simp only [mem_firstTriangle, mem_secondTriangle] at hiB hiC
      omega
    · exact absurd rfl hBC
  · rintro rfl
    exact ⟨firstTriangle, secondTriangle, isBlock_firstTriangle, isBlock_secondTriangle,
      firstTriangle_ne_secondTriangle, by simp, by simp⟩

/-! ### The block–cut tree -/

/-- The first triangle, as a block vertex of the block–cut graph. -/
def firstBlock : graph.toSimpleGraph.BlockVertex := ⟨firstTriangle, isBlock_firstTriangle⟩

/-- The second triangle, as a block vertex of the block–cut graph. -/
def secondBlock : graph.toSimpleGraph.BlockVertex := ⟨secondTriangle, isBlock_secondTriangle⟩

/-- The shared vertex `0`, as a cut vertex of the block–cut graph. -/
def sharedCutVertex : graph.toSimpleGraph.CutVertex :=
  ⟨vertex 0, (Graph.isCutVertex_iff_toSimpleGraph_isCutVertex _).mp (isCutVertex_iff.mpr rfl)⟩

@[simp]
theorem coe_firstBlock : (firstBlock : Set V(graph)) = firstTriangle :=
  (rfl)

@[simp]
theorem coe_secondBlock : (secondBlock : Set V(graph)) = secondTriangle :=
  (rfl)

@[simp]
theorem coe_sharedCutVertex : (sharedCutVertex : V(graph)) = vertex 0 :=
  (rfl)

private def blockCutVertexOfFin : Fin 3 → graph.toSimpleGraph.BlockCutVertex
  | 0 => .inl firstBlock
  | 1 => .inr sharedCutVertex
  | 2 => .inl secondBlock

private theorem blockCutVertexOfFin_bijective : Function.Bijective blockCutVertexOfFin := by
  have hne : firstBlock ≠ secondBlock := fun h ↦
    firstTriangle_ne_secondTriangle (congrArg Subtype.val h)
  refine ⟨fun a b hab ↦ ?_, ?_⟩
  · fin_cases a <;> fin_cases b <;> simp_all [blockCutVertexOfFin, hne.symm]
  · rintro (⟨B, hB⟩ | ⟨⟨v, hv⟩, hcut⟩)
    · rcases isBlock_iff.mp hB with rfl | rfl
      exacts [⟨0, rfl⟩, ⟨2, rfl⟩]
    · rw [← Graph.isCutVertex_iff_toSimpleGraph_isCutVertex, isCutVertex_iff] at hcut
      subst hcut
      exact ⟨1, rfl⟩

/-- **The block–cut tree of `graph`** is the path `firstBlock — sharedCutVertex — secondBlock`:
the path graph on three vertices is isomorphic to the block–cut graph, sending `0`, `1`, `2` to
the first triangle, the shared vertex `0` and the second triangle. -/
noncomputable def pathGraphIsoBlockCutGraph :
    pathGraph 3 ≃g graph.toSimpleGraph.blockCutGraph where
  toEquiv := .ofBijective _ blockCutVertexOfFin_bijective
  map_rel_iff' {a b} := by
    fin_cases a <;> fin_cases b <;>
      simp [blockCutVertexOfFin, pathGraph_adj]

@[simp]
theorem pathGraphIsoBlockCutGraph_zero : pathGraphIsoBlockCutGraph 0 = .inl firstBlock :=
  (rfl)

@[simp]
theorem pathGraphIsoBlockCutGraph_one : pathGraphIsoBlockCutGraph 1 = .inr sharedCutVertex :=
  (rfl)

@[simp]
theorem pathGraphIsoBlockCutGraph_two : pathGraphIsoBlockCutGraph 2 = .inl secondBlock :=
  (rfl)

/-- The block–cut graph of `graph` is a tree. -/
theorem blockCutGraph_isTree : graph.toSimpleGraph.blockCutGraph.IsTree :=
  pathGraphIsoBlockCutGraph.isTree_iff.mp (isTree_pathGraph_add_one 2)

/-! ### The loop and the vertex-block convention -/

/-- The loop at the cut vertex `0` lies in the subgraph induced by every vertex block of `graph`.
Since the two triangles are distinct vertex blocks, the vertex blocks do not partition the loops of
`graph`. -/
theorem isLoopAt_induce_of_isBlock {B : Set V(graph)} (hB : graph.IsBlock B) :
    (graph.induce (Subtype.val '' B)).IsLoopAt s(0, 0) 0 := by
  have h0 : vertex 0 ∈ B := by
    rcases isBlock_iff.mp hB with rfl | rfl <;> simp
  rw [← Graph.isLink_self_iff, Graph.induce_isLink]
  exact ⟨isLoopAt, ⟨_, h0, rfl⟩, ⟨_, h0, rfl⟩⟩

end TauCeti.Examples.TrianglesSharingVertexBlockCut
