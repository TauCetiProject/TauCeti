/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import TauCeti.Combinatorics.Graph.EdgeEnds
public import TauCeti.Combinatorics.Graph.Incidence

/-!
# Matchings in multigraphs

An ordinary matching in a multigraph is a finite set of actual edge identities, with no selected
loop and with at most one selected edge incident to each actual vertex.  Parallel edges remain
distinct, but two parallel edges cannot both belong to a matching because they share their ends.

This file also constructs the graph traced by a finite set of actual edges.  Its vertices are
exactly the ends of those edges and its edges are exactly the selected identities, so a matching
has no artificial isolated vertices.  A perfect matching is a matching whose traced vertex set is
the whole actual vertex set.

These definitions provide the edge-identity interface used to decompose regular bipartite
multigraphs into perfect matchings.  The comparison with unit-capacity multiset matchings is in
`TauCeti.Combinatorics.Graph.Matching.Capacitated`.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {M N : Finset E(G)}

/-- A finite set of actual multigraph edges is a matching when it contains no loop and at most one
selected edge is incident to each actual vertex. -/
def IsMatching (G : Graph α β) (M : Finset E(G)) : Prop :=
  (∀ e ∈ M, ¬(G.edgeEnds e).IsDiag) ∧
    ∀ x : V(G), ∀ e ∈ M, G.Inc e.1 x.1 →
      ∀ f ∈ M, G.Inc f.1 x.1 → e = f

/-- The defining characterization of a multigraph matching. -/
theorem isMatching_iff : G.IsMatching M ↔
    (∀ e ∈ M, ¬(G.edgeEnds e).IsDiag) ∧
      ∀ x : V(G), ∀ e ∈ M, G.Inc e.1 x.1 →
        ∀ f ∈ M, G.Inc f.1 x.1 → e = f :=
  Iff.rfl

/-- The empty edge set is a matching. -/
@[simp]
theorem isMatching_empty (G : Graph α β) : G.IsMatching ∅ := by
  simp [isMatching_iff]

namespace IsMatching

/-- Every selected edge of a matching has distinct ends. -/
theorem not_isDiag (hM : G.IsMatching M) {e : E(G)} (he : e ∈ M) :
    ¬(G.edgeEnds e).IsDiag :=
  hM.1 e he

/-- Two selected edges of a matching incident to the same vertex are equal. -/
theorem eq_of_inc (hM : G.IsMatching M) {x : V(G)} {e f : E(G)}
    (heM : e ∈ M) (he : G.Inc e.1 x.1) (hfM : f ∈ M) (hf : G.Inc f.1 x.1) :
    e = f :=
  hM.2 x e heM he f hfM hf

/-- Passing to a subset of the selected edges preserves a matching. -/
theorem mono (hM : G.IsMatching M) (hNM : N ⊆ M) : G.IsMatching N := by
  exact ⟨fun e he ↦ hM.not_isDiag (hNM he),
    fun x e heN he f hfN hf ↦ hM.eq_of_inc (hNM heN) he (hNM hfN) hf⟩

end IsMatching

/-- The actual vertices incident to one of the selected edge identities. -/
def matchingVertexSet (G : Graph α β) (M : Finset E(G)) : Set V(G) :=
  {x | ∃ e ∈ M, G.Inc e.1 x.1}

/-- Membership in the vertex set traced by selected edges means incidence with a selected edge. -/
theorem mem_matchingVertexSet_iff {x : V(G)} :
    x ∈ G.matchingVertexSet M ↔ ∃ e ∈ M, G.Inc e.1 x.1 :=
  Iff.rfl

/-- The graph traced by selected actual edges. Its ambient vertices and edges are unchanged, but
its actual vertices are exactly the selected edges' ends and its actual edges are exactly the
selected identities. -/
def matchingSubgraph (G : Graph α β) (M : Finset E(G)) : Graph α β :=
  (G.induce (Subtype.val '' G.matchingVertexSet M)).restrict (Subtype.val '' (M : Set E(G)))

/-- The actual vertices of the graph traced by `M` are exactly the ends of edges in `M`. -/
@[simp]
theorem vertexSet_matchingSubgraph :
    V(G.matchingSubgraph M) = Subtype.val '' G.matchingVertexSet M :=
  by
    simp only [matchingSubgraph, Graph.vertexSet_restrict, Graph.vertexSet_induce]

/-- A selected actual edge belongs to the graph traced by the selected edges. -/
theorem mem_edgeSet_matchingSubgraph_of_mem {e : E(G)} (he : e ∈ M) :
    e.1 ∈ E(G.matchingSubgraph M) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  have hx : (⟨x, hxy.left_mem⟩ : V(G)) ∈ G.matchingVertexSet M :=
    ⟨e, he, hxy.inc_left⟩
  have hy : (⟨y, hxy.right_mem⟩ : V(G)) ∈ G.matchingVertexSet M :=
    ⟨e, he, hxy.inc_right⟩
  exact ⟨⟨x, y, hxy, ⟨_, hx, rfl⟩, ⟨_, hy, rfl⟩⟩, e, by simpa, rfl⟩

/-- The actual edges of the graph traced by `M` are exactly the selected edge identities. -/
@[simp]
theorem edgeSet_matchingSubgraph :
    E(G.matchingSubgraph M) = Subtype.val '' (M : Set E(G)) := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · rintro _ ⟨e, he, rfl⟩
    exact mem_edgeSet_matchingSubgraph_of_mem he

/-- The graph traced by selected edges is a subgraph of the original graph. -/
theorem matchingSubgraph_le : G.matchingSubgraph M ≤ G := by
  apply Graph.IsSubgraph.trans Graph.restrict_le
  apply Graph.induce_le
  rintro _ ⟨x, -, rfl⟩
  exact x.2

/-- Incidence in the graph traced by `M` is incidence in `G` together with membership in `M`. -/
@[simp]
theorem matchingSubgraph_inc {e : β} {x : α} :
    (G.matchingSubgraph M).Inc e x ↔
      G.Inc e x ∧ ∃ he : e ∈ E(G), (⟨e, he⟩ : E(G)) ∈ M := by
  constructor
  · intro h
    have hG := h.mono matchingSubgraph_le
    have heM : e ∈ E(G.matchingSubgraph M) := h.edge_mem
    rw [edgeSet_matchingSubgraph] at heM
    obtain ⟨e', he', heq⟩ := heM
    subst e
    exact ⟨hG, e'.2, he'⟩
  · rintro ⟨hx, he, heM⟩
    obtain ⟨y, hxy⟩ := hx
    refine ⟨y, ?_⟩
    refine ⟨⟨⟨e, he⟩, heM, rfl⟩, hxy, ?_, ?_⟩
    · exact ⟨⟨x, hxy.left_mem⟩, ⟨⟨e, he⟩, heM, hxy.inc_left⟩, rfl⟩
    · exact ⟨⟨y, hxy.right_mem⟩, ⟨⟨e, he⟩, heM, hxy.inc_right⟩, rfl⟩

/-- Every actual vertex of a traced graph is incident to one of its actual edges; no isolated
vertices are introduced. -/
theorem exists_inc_matchingSubgraph_of_mem_vertexSet {x : α}
    (hx : x ∈ V(G.matchingSubgraph M)) : ∃ e, (G.matchingSubgraph M).Inc e x := by
  obtain ⟨x', ⟨e, heM, he⟩, rfl⟩ := hx
  exact ⟨e.1, matchingSubgraph_inc.2 ⟨he, e.2, heM⟩⟩

/-- A perfect matching is a matching whose selected edges are incident to every actual vertex. -/
def IsPerfectMatching (G : Graph α β) (M : Finset E(G)) : Prop :=
  G.IsMatching M ∧ G.matchingVertexSet M = Set.univ

/-- A finite edge set is a perfect matching exactly when it is a matching and every actual vertex
is incident to a selected edge. -/
theorem isPerfectMatching_iff : G.IsPerfectMatching M ↔
    G.IsMatching M ∧ ∀ x : V(G), ∃ e ∈ M, G.Inc e.1 x.1 := by
  rw [IsPerfectMatching, Set.eq_univ_iff_forall]
  rfl

namespace IsPerfectMatching

/-- A perfect matching is a matching. -/
theorem isMatching (hM : G.IsPerfectMatching M) : G.IsMatching M :=
  hM.1

/-- Every actual vertex is incident to a selected edge of a perfect matching. -/
theorem exists_inc (hM : G.IsPerfectMatching M) (x : V(G)) :
    ∃ e ∈ M, G.Inc e.1 x.1 :=
  isPerfectMatching_iff.1 hM |>.2 x

/-- Every actual vertex is incident to a unique selected edge of a perfect matching. -/
theorem existsUnique_inc (hM : G.IsPerfectMatching M) (x : V(G)) :
    ∃! e : E(G), e ∈ M ∧ G.Inc e.1 x.1 := by
  obtain ⟨e, heM, he⟩ := hM.exists_inc x
  exact ⟨e, ⟨heM, he⟩, fun f hf ↦ hM.isMatching.eq_of_inc hf.1 hf.2 heM he⟩

end IsPerfectMatching

end Graph
