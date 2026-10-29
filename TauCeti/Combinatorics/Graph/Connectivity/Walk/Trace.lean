/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps
public import TauCeti.Combinatorics.Graph.Union

/-!
# The graph traced by a multigraph walk

This file associates to an edge-labelled multigraph walk the graph consisting exactly of its
visited vertices and traversed edge identities.  This graph retains the ambient vertex and edge
types, so it can be compared directly with the ambient graph and combined with other traced graphs.
The construction records an isolated vertex for a zero-length walk, including when that vertex is
not an actual vertex of the ambient graph.

The interface follows Mathlib's `SimpleGraph.Walk.toSubgraph`, adapted to Mathlib's multigraph
representation in which a subgraph is itself a `Graph` and parallel edges retain their identities.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}
variable {w x y z : α}

/-- The graph consisting of the vertices and edge identities traversed by a walk. -/
def walkGraph (G : Graph α β) {x y : α} (p : G.Walk x y) : Graph α β :=
  (G.induce {a | a ∈ p.support}).deleteEdges {e | e ∉ p.edges}

namespace Walk

@[simp, grind =]
theorem vertexSet_walkGraph (p : G.Walk x y) :
    V(G.walkGraph p) = {a | a ∈ p.support} :=
  (rfl)

/-- The links of a traced graph are precisely the ambient links whose identities occur in the
walk. -/
@[simp, grind =]
theorem walkGraph_isLink (p : G.Walk x y) (e : β) (a b : α) :
    (G.walkGraph p).IsLink e a b ↔ G.IsLink e a b ∧ e ∈ p.edges := by
  simp only [walkGraph, deleteEdges_isLink, induce_isLink, mem_ofPred_eq, not_not]
  constructor
  · rintro ⟨⟨hab, -, -⟩, he⟩
    exact ⟨hab, he⟩
  · rintro ⟨hab, he⟩
    exact ⟨⟨hab, p.mem_support_of_isLink_of_mem_edges hab he,
      p.mem_support_of_isLink_of_mem_edges hab.symm he⟩, he⟩

/-- An edge belongs to the graph traced by a walk exactly when the walk traverses it. -/
theorem mem_edgeSet_walkGraph (p : G.Walk x y) (e : β) :
    e ∈ E(G.walkGraph p) ↔ e ∈ p.edges := by
  constructor
  · simp only [walkGraph, edgeSet_deleteEdges, mem_sdiff, mem_ofPred_eq, not_not, and_imp]
    exact fun _ he ↦ he
  · intro he
    obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet (p.edges_subset_edgeSet he)
    exact ((p.walkGraph_isLink e a b).mpr ⟨hab, he⟩).edge_mem

/-- The edge set of a traced graph is the set represented by the walk's edge list. -/
@[simp, grind =]
theorem edgeSet_walkGraph (p : G.Walk x y) :
    E(G.walkGraph p) = {e | e ∈ p.edges} :=
  Set.ext fun e ↦ p.mem_edgeSet_walkGraph e

/-- A traced graph is a subgraph of the ambient graph when the walk starts at an actual vertex. -/
theorem walkGraph_le (p : G.Walk x y) (hx : x ∈ V(G)) : G.walkGraph p ≤ G := by
  refine { vertexSet_mono := ?_, isLink_mono := ?_ }
  · intro a ha
    exact p.support_subset_vertexSet hx a ha
  · intro e a b hab
    exact (p.walkGraph_isLink e a b).mp hab |>.1

/-- A walk traces a subgraph of its ambient graph exactly when its starting point is an actual
ambient vertex. -/
@[simp]
theorem walkGraph_le_iff (p : G.Walk x y) : G.walkGraph p ≤ G ↔ x ∈ V(G) :=
  ⟨fun h ↦ h.vertexSet_mono p.start_mem_support, p.walkGraph_le⟩

/-- A positive-length walk always traces a subgraph of its ambient graph. -/
theorem walkGraph_le_of_pos (p : G.Walk x y) (hp : 0 < p.length) : G.walkGraph p ≤ G := by
  apply p.walkGraph_le
  exact p.support_subset_vertexSet_of_pos hp x p.start_mem_support

/-- The endpoints of a walk are reachable within the graph traced by that walk. -/
theorem reachable_walkGraph (p : G.Walk x y) :
    (G.walkGraph p).Reachable x y := by
  cases p with
  | nil => exact Reachable.refl (by simp)
  | cons e h p =>
      apply reachable_def.mpr
      refine ⟨by simp, ⟨(Walk.cons e h p).transfer ?_ ?_⟩⟩
      · exact (Walk.cons e h p).walkGraph_le_of_pos (by simp)
      · intro f hf
        exact ((Walk.cons e h p).mem_edgeSet_walkGraph f).mpr hf

/-- Inclusion between two traced graphs is equivalent to inclusion of their vertex and edge
lists, regarded as sets. -/
theorem walkGraph_le_walkGraph_iff (p : G.Walk x y) (q : G.Walk z w) :
    G.walkGraph p ≤ G.walkGraph q ↔
      (∀ ⦃a⦄, a ∈ p.support → a ∈ q.support) ∧
        ∀ ⦃e⦄, e ∈ p.edges → e ∈ q.edges := by
  constructor
  · intro hpq
    constructor
    · intro a ha
      exact hpq.vertexSet_mono ha
    · intro e he
      exact (q.mem_edgeSet_walkGraph e).mp
        (hpq.edgeSet_mono ((p.mem_edgeSet_walkGraph e).mpr he))
  · rintro ⟨hv, he⟩
    refine { vertexSet_mono := hv, isLink_mono := ?_ }
    intro e a b hab
    rw [q.walkGraph_isLink]
    rcases (p.walkGraph_isLink e a b).mp hab with ⟨hab, hep⟩
    exact ⟨hab, he hep⟩

/-- Mapping a walk to a supergraph does not change its traced graph. -/
@[simp, grind =]
theorem walkGraph_mapLe (h : G ≤ H) (p : G.Walk x y) :
    H.walkGraph (p.mapLe h) = G.walkGraph p := by
  apply Graph.ext
  · simp
  · intro e a b
    simp only [walkGraph_isLink, edges_mapLe_eq_edges]
    constructor
    · rintro ⟨hab, he⟩
      exact ⟨(h.isLink_iff (p.edges_subset_edgeSet he)).mpr hab, he⟩
    · rintro ⟨hab, he⟩
      exact ⟨h.isLink_mono hab, he⟩

/-- Restricting a walk to a subgraph containing its edges does not change its traced graph. -/
@[simp]
theorem walkGraph_transfer (h : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    G.walkGraph (p.transfer h hp) = H.walkGraph p := by
  rw [← walkGraph_mapLe h, mapLe_transfer]

/-- A zero-length walk traces the edgeless graph on its base vertex. -/
@[simp, grind =]
theorem walkGraph_nil (G : Graph α β) (x : α) :
    G.walkGraph (Walk.nil : G.Walk x x) = Graph.noEdge {x} β := by
  apply Graph.ext
  · ext a
    simp
  · intro e a b
    simp

/-- A one-edge walk traces exactly that edge and its endpoints. -/
@[simp]
theorem _root_.Graph.IsLink.walkGraph_toWalk {e : β} (h : G.IsLink e x y) :
    G.walkGraph h.toWalk = (G.induce {x, y}).restrict {e} := by
  apply Graph.ext
  · ext a
    simp [eq_comm]
  · intro f a b
    simp only [walkGraph_isLink, IsLink.edges_toWalk, List.mem_singleton,
      restrict_isLink, mem_singleton_iff, induce_isLink, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hab, rfl⟩
      exact ⟨rfl, hab, hab.left_eq_or_eq h, hab.right_eq_or_eq h⟩
    · rintro ⟨rfl, hab, -, -⟩
      exact ⟨hab, rfl⟩

/-- Traced graphs of walks in one ambient graph are compatible. -/
theorem walkGraph_compatible (p : G.Walk x y) (q : G.Walk z w) :
    (G.walkGraph p).Compatible (G.walkGraph q) := by
  intro e hep heq a b
  rw [p.walkGraph_isLink, q.walkGraph_isLink]
  simp only [(p.mem_edgeSet_walkGraph e).mp hep, (q.mem_edgeSet_walkGraph e).mp heq, and_true]

/-- Concatenating walks takes the compatible union of their traced graphs. -/
theorem walkGraph_append (p : G.Walk x y) (q : G.Walk y z) :
    G.walkGraph (p.append q) = (p.walkGraph_compatible q).union := by
  apply Graph.ext
  · ext a
    simp only [vertexSet_walkGraph, Compatible.vertexSet_union, mem_ofPred_eq, mem_union,
      support_append, List.mem_append]
    constructor
    · rintro (ha | ha)
      · exact Or.inl ha
      · exact Or.inr ((q.mem_support_iff).mpr (Or.inr ha))
    · rintro (ha | ha)
      · exact Or.inl ha
      · rcases (q.mem_support_iff).mp ha with rfl | ha
        · exact Or.inl p.end_mem_support
        · exact Or.inr ha
  · intro e a b
    simp only [walkGraph_isLink, Compatible.union_isLink, edges_append, List.mem_append]
    tauto

/-- Prepending an edge takes the compatible union of its one-edge trace and the remaining
walk's trace. -/
theorem walkGraph_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    G.walkGraph (.cons e h p) = (h.toWalk.walkGraph_compatible p).union := by
  simpa only [h.toWalk_eq_cons, cons_append, nil_append] using walkGraph_append h.toWalk p

/-- Reversing a walk does not change its traced graph. -/
@[simp, grind =]
theorem walkGraph_reverse (p : G.Walk x y) : G.walkGraph p.reverse = G.walkGraph p := by
  apply Graph.ext
  · ext a
    simp [support_reverse]
  · intro e a b
    simp [walkGraph_isLink, edges_reverse]

/-- Bypassing repeated vertices (removing closed sub-walks) can only shrink a walk's traced
graph. -/
theorem walkGraph_bypass_le [DecidableEq α] (p : G.Walk x y) :
    G.walkGraph p.bypass ≤ G.walkGraph p :=
  (walkGraph_le_walkGraph_iff p.bypass p).mpr
    ⟨p.support_bypass_subset_support, p.edges_bypass_subset_edges⟩

end Walk

end Graph
