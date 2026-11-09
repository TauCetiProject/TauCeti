/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Open

/-!
# Examples of open ear decompositions on the diamond graph

This file exercises the public API of open ear decompositions on the four-cycle with a diagonal
(the diamond graph `(completeGraph (Fin 4)).deleteEdges {s(1, 3)}` on `Fin 4`):

* an explicit open ear decomposition starting from the spanning four-cycle `0 - 1 - 2 - 3 - 0` and
  adjoining the diagonal `0 - 2` as a single-edge open ear (a chord with no internal vertices);
* an explicit open ear decomposition starting from the triangle `0 - 1 - 2 - 0` and adjoining the
  two-edge path `0 - 3 - 2` through vertex `3` as an open ear;
* certification of `2`-vertex-connectivity, `2`-edge-connectivity, and prescribed-edge open ear
  decompositions through the public characterization theorems.
-/

open SimpleGraph

-- On the diamond graph (`K₄` minus `{1, 3}`), construct two explicit open ear decompositions of `⊤`
-- of length `1`—one starting from the four-cycle `0 - 1 - 2 - 3 - 0` and one starting from the
-- triangle `0 - 1 - 2 - 0`—with distinct initial subgraphs, and deduce `2`-vertex-connectivity,
-- `2`-edge-connectivity, and an open ear decomposition whose initial cycle contains `{0, 2}`.
example :
    let G : SimpleGraph (Fin 4) := (completeGraph (Fin 4)).deleteEdges {s(1, 3)}
    ∃ d₁ d₂ : G.EarDecomposition ⊤,
      d₁.IsOpen ∧ d₂.IsOpen ∧ d₁.length = 1 ∧ d₂.length = 1 ∧
        d₁.initial ≠ d₂.initial ∧ G.IsVertexConnected 2 ∧ G.IsEdgeConnected 2 ∧
        ∃ d₃ : G.EarDecomposition ⊤, d₃.IsOpen ∧ d₃.initial.Adj 0 2 := by
  intro G
  have h01 : G.Adj 0 1 := by simp [G, deleteEdges_adj]
  have h12 : G.Adj 1 2 := by simp [G, deleteEdges_adj]
  have h23 : G.Adj 2 3 := by simp [G, deleteEdges_adj]
  have h30 : G.Adj 3 0 := by simp [G, deleteEdges_adj]
  have h02 : G.Adj 0 2 := by simp [G, deleteEdges_adj]
  have h20 : G.Adj 2 0 := by simp [G, deleteEdges_adj]
  have h03 : G.Adj 0 3 := by simp [G, deleteEdges_adj]
  have h32 : G.Adj 3 2 := by simp [G, deleteEdges_adj]
  -- Decomposition 1: spanning four-cycle `0 - 1 - 2 - 3 - 0` followed by the chord `0 - 2`.
  let c₄ : G.Walk 0 0 := Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h30 .nil)))
  have hc₄ : c₄.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    exact ⟨by simp [Walk.cons_isPath_iff], by simp⟩
  let e₁ : G.Ear c₄.toSubgraph :=
    Ear.«open» h02.toWalk (Walk.IsPath.cons .nil (by simp))
      (by simp [c₄]) (by simp [c₄]) (by decide)
      (fun w hw h0 h2 ↦ by
        simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        exact (hw.elim h0 h2).elim)
      (fun e he ↦ by
        simp only [Adj.toWalk, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at he
        subst he
        rw [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet]
        simp [c₄])
  have htop₁ : e₁.adjoin = ⊤ := by
    refine eq_top_iff.mpr ⟨fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
    · clear hx
      simp only [Ear.verts_adjoin, e₁, Ear.toSubgraph_open, Set.mem_union,
        Walk.mem_verts_toSubgraph, c₄, Adj.toWalk, Walk.support_cons, Walk.support_nil]
      revert x
      decide
    · have hxy' : x ≠ y ∧ s(x, y) ≠ s(1, 3) := by simpa [G, deleteEdges_adj] using hxy
      clear hxy
      simp only [Ear.adj_adjoin, e₁, Ear.toSubgraph_open,
        Walk.adj_toSubgraph_iff_mem_edges, c₄, Adj.toWalk, Walk.edges_cons, Walk.edges_nil]
      revert x y
      decide
  let d₁ : G.EarDecomposition ⊤ := ((EarDecomposition.cycle c₄ hc₄).snoc e₁).copy htop₁
  have hd₁ : d₁.IsOpen := by
    simp [d₁, e₁, EarDecomposition.isOpen_cycle c₄ hc₄]
  -- Decomposition 2: triangle `0 - 1 - 2 - 0` followed by the two-edge path `0 - 3 - 2`.
  let c₃ : G.Walk 0 0 := Walk.cons h01 (Walk.cons h12 (Walk.cons h20 .nil))
  have hc₃ : c₃.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    exact ⟨by simp [Walk.cons_isPath_iff], by simp⟩
  let p₂ : G.Walk 0 2 := Walk.cons h03 (Walk.cons h32 .nil)
  have hp₂ : p₂.IsPath := by simp [p₂, Walk.cons_isPath_iff]
  let e₂ : G.Ear c₃.toSubgraph :=
    Ear.«open» p₂ hp₂ (by simp [c₃]) (by simp [c₃]) (by decide)
      (fun w hw h0 h2 ↦ by
        simp only [p₂, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact (h0 rfl).elim
        · simp [c₃]
        · exact (h2 rfl).elim)
      (fun e he ↦ by
        simp only [p₂, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at he
        rw [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet]
        rcases he with rfl | rfl <;> simp [c₃])
  have htop₂ : e₂.adjoin = ⊤ := by
    refine eq_top_iff.mpr ⟨fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
    · clear hx
      simp only [Ear.verts_adjoin, e₂, Ear.toSubgraph_open, Set.mem_union,
        Walk.mem_verts_toSubgraph, c₃, p₂, Walk.support_cons, Walk.support_nil]
      revert x
      decide
    · have hxy' : x ≠ y ∧ s(x, y) ≠ s(1, 3) := by simpa [G, deleteEdges_adj] using hxy
      clear hxy
      simp only [Ear.adj_adjoin, e₂, Ear.toSubgraph_open,
        Walk.adj_toSubgraph_iff_mem_edges, c₃, p₂, Walk.edges_cons, Walk.edges_nil]
      revert x y
      decide
  let d₂ : G.EarDecomposition ⊤ := ((EarDecomposition.cycle c₃ hc₃).snoc e₂).copy htop₂
  have hd₂ : d₂.IsOpen := by
    simp [d₂, e₂, EarDecomposition.isOpen_cycle c₃ hc₃]
  have hne : d₁.initial ≠ d₂.initial := by
    intro h
    have h3 : (3 : Fin 4) ∈ d₁.initial.verts := by simp [d₁]; simp [c₄]
    rw [h] at h3
    simp [d₂] at h3
    simp [c₃] at h3
  have hG2 : G.IsVertexConnected 2 := hd₁.isVertexConnected_two
  exact ⟨d₁, d₂, hd₁, hd₂, by simp [d₁], by simp [d₂], hne, hG2, d₁.isEdgeConnected_two,
    h02.exists_isOpen_earDecomposition_adj_initial hG2⟩
