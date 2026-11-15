/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Vertex covers of multigraphs

A *vertex cover* of a multigraph `G : Graph α β` is a set of actual vertices meeting every edge:
every edge has an end in the set. Parallel edges are allowed, and a loop at `v` is met only by sets
containing `v`.

## Main definitions

* `Graph.IsVertexCover G C`: the set `C` of actual vertices meets every edge of `G`.

## Main results

* `Graph.isVertexCover_iff_forall_exists_inc`: a set of actual vertices is a vertex cover exactly
  when every actual edge is incident with one of its vertices.
* `Graph.isVertexCover_empty_iff`: the empty set is a vertex cover exactly when there are no actual
  edges.
-/

public section

open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

variable (G) in
/-- The set `C` of actual vertices is a *vertex cover* of `G`: every edge has an end in `C`. A loop
at `v` is met only by sets containing `v`. -/
def IsVertexCover (C : Set V(G)) : Prop :=
  ∀ ⦃e : β⦄ ⦃x y : V(G)⦄, G.IsLink e x y → x ∈ C ∨ y ∈ C

theorem isVertexCover_def {C : Set V(G)} :
    G.IsVertexCover C ↔ ∀ ⦃e : β⦄ ⦃x y : V(G)⦄, G.IsLink e x y → x ∈ C ∨ y ∈ C :=
  Iff.rfl

/-- A set of actual vertices is a vertex cover exactly when every actual edge is incident with one
of its vertices. -/
theorem isVertexCover_iff_forall_exists_inc {C : Set V(G)} :
    G.IsVertexCover C ↔ ∀ e : E(G), ∃ x ∈ C, G.Inc e x := by
  refine ⟨fun hC e ↦ ?_, fun hC e x y he ↦ ?_⟩
  · obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet e.2
    rcases hC (x := ⟨x, he.left_mem⟩) (y := ⟨y, he.right_mem⟩) he with hx | hy
    exacts [⟨_, hx, he.inc_left⟩, ⟨_, hy, he.inc_right⟩]
  · obtain ⟨z, hz, hze⟩ := hC ⟨e, he.edge_mem⟩
    rcases hze.eq_or_eq_of_isLink he with h | h
    · exact .inl (Subtype.ext h ▸ hz)
    · exact .inr (Subtype.ext h ▸ hz)

/-- Every actual edge is incident with a vertex of a vertex cover. -/
theorem IsVertexCover.exists_mem_inc {C : Set V(G)} (hC : G.IsVertexCover C) (e : E(G)) :
    ∃ x ∈ C, G.Inc e x :=
  isVertexCover_iff_forall_exists_inc.1 hC e

/-- A superset of a vertex cover is a vertex cover. -/
theorem IsVertexCover.subset {C D : Set V(G)} (hC : G.IsVertexCover C) (hCD : C ⊆ D) :
    G.IsVertexCover D :=
  fun _ _ _ he ↦ (hC he).imp (@hCD _) (@hCD _)

/-- The set of all actual vertices is a vertex cover. -/
@[simp]
theorem isVertexCover_univ : G.IsVertexCover Set.univ :=
  fun _ _ _ _ ↦ .inl trivial

/-- The empty set is a vertex cover exactly when there are no actual edges. -/
@[simp]
theorem isVertexCover_empty_iff : G.IsVertexCover ∅ ↔ E(G) = ∅ := by
  simp [isVertexCover_iff_forall_exists_inc, Set.eq_empty_iff_forall_notMem]

end Graph
