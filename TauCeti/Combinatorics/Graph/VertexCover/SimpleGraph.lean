/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import TauCeti.Combinatorics.Graph.VertexCover.Basic

/-!
# Vertex covers and simplification

Simplification preserves vertex covers of a loopless multigraph, even with parallel edges.
For a multigraph with loops, a cover of the simplification is a cover of the original graph
exactly when it also contains every vertex carrying a loop.

For `Graph.ofSimpleGraph H`, vertex covers correspond to Mathlib's `SimpleGraph.IsVertexCover`
under the canonical identification of actual vertices with vertices of `H`. Both preimage and
image forms are provided, so covers obtained from multigraph matching theorems can be used
directly with the simple-graph vertex cover number.
-/

public section

open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {C : Set V(G)}

/-- A multigraph vertex cover is a cover of its simplification. -/
theorem IsVertexCover.toSimpleGraph (hC : G.IsVertexCover C) :
    G.toSimpleGraph.IsVertexCover C := by
  intro x y hxy
  rw [G.toSimpleGraph_adj] at hxy
  obtain ⟨e, he⟩ := hxy.2
  exact isVertexCover_def.1 hC he

/-- Simplification forgets precisely the requirement to cover vertices carrying loops. -/
theorem isVertexCover_iff_toSimpleGraph_and_forall_isLoopAt :
    G.IsVertexCover C ↔ G.toSimpleGraph.IsVertexCover C ∧
      ∀ (x : V(G)) (e : β), G.IsLoopAt e x → x ∈ C := by
  constructor
  · intro hC
    refine ⟨hC.toSimpleGraph, fun x e he ↦ ?_⟩
    simpa using isVertexCover_def.1 hC (x := x) (y := x) he
  · rintro ⟨hC, hloop⟩
    refine isVertexCover_def.2 fun e x y he ↦ ?_
    by_cases hxy : x = y
    · subst y
      exact Or.inl (hloop x e he)
    · apply hC
      rw [G.toSimpleGraph_adj]
      exact ⟨hxy, ⟨e, he⟩⟩

/-- For loopless multigraphs, simplification preserves vertex covers in both directions. -/
@[simp]
theorem isVertexCover_toSimpleGraph_iff [G.Loopless] :
    G.toSimpleGraph.IsVertexCover C ↔ G.IsVertexCover C := by
  rw [isVertexCover_iff_toSimpleGraph_and_forall_isLoopAt]
  simp

end Graph

namespace SimpleGraph

variable {α : Type u} {H : SimpleGraph α}

/-- Pulling a vertex set back to the actual vertices of `Graph.ofSimpleGraph` preserves covers. -/
@[simp]
theorem isVertexCover_ofSimpleGraph_preimage_iff {C : Set α} :
    (Graph.ofSimpleGraph H).IsVertexCover (Subtype.val ⁻¹' C) ↔ H.IsVertexCover C := by
  constructor
  · intro hC x y hxy
    exact Graph.isVertexCover_def.1 hC (x := ⟨x, by simp⟩) (y := ⟨y, by simp⟩)
      (e := s(x, y)) (by simpa using hxy)
  · intro hC
    refine Graph.isVertexCover_def.2 fun e x y he ↦ ?_
    exact hC (Graph.ofSimpleGraph_adj_iff _ _ |>.1 ⟨e, he⟩)

/-- A cover of `Graph.ofSimpleGraph` gives a cover on the original simple-graph carrier. -/
@[simp]
theorem isVertexCover_ofSimpleGraph_image_iff {C : Set V(Graph.ofSimpleGraph H)} :
    H.IsVertexCover (Subtype.val '' C) ↔ (Graph.ofSimpleGraph H).IsVertexCover C := by
  rw [← isVertexCover_ofSimpleGraph_preimage_iff]
  simp only [Set.preimage_image_eq _ Subtype.val_injective]

end SimpleGraph
