/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence
public import TauCeti.Combinatorics.Graph.Orientation.Basic

/-!
# Indegrees and outdegrees of multigraph orientations

The indegree of a vertex under an orientation of a multigraph with finitely many actual edges
counts the actual edges whose chosen head is that vertex; the outdegree counts those whose chosen
tail is that vertex. Parallel edges are counted separately and a loop contributes one to each.
Reversal exchanges the two counts, and summing either over all vertices counts every edge once.

On a vertex set `S`, the total indegree lies between the number of edges internal to `S` and the
number of edges incident with `S`: an internal edge has its head in `S`, and an edge with its head
in `S` is incident with `S`. These are the necessary conditions of the prescribed and bounded
indegree theorems.

## Main declarations

* `Graph.Orientation.indegree`, `Graph.Orientation.outdegree`: the two degree counts.
* `Graph.Orientation.sum_indegree`: the indegrees sum to the number of actual edges.
* `Graph.Orientation.card_internalEdges_le_sum_indegree` and
  `Graph.Orientation.sum_indegree_le_card_incidentEdges`: the bounds on total indegree.
-/

public section

open Finset

namespace Graph.Orientation

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E} [Fintype G.edgeSet]

open Classical in
/-- The number of actual edges whose chosen head is `v`. A loop at `v` counts once. -/
noncomputable def indegree (o : Orientation G) (v : G.vertexSet) : ℕ :=
  #{e | o.head e = v}

open Classical in
/-- The number of actual edges whose chosen tail is `v`. A loop at `v` counts once. -/
noncomputable def outdegree (o : Orientation G) (v : G.vertexSet) : ℕ :=
  #{e | o.tail e = v}

theorem indegree_def [DecidableEq G.vertexSet] (o : Orientation G) (v : G.vertexSet) :
    o.indegree v = #{e | o.head e = v} := by
  rw [indegree]
  congr

theorem outdegree_def [DecidableEq G.vertexSet] (o : Orientation G) (v : G.vertexSet) :
    o.outdegree v = #{e | o.tail e = v} := by
  rw [outdegree]
  congr

@[simp]
theorem indegree_reverse (o : Orientation G) (v : G.vertexSet) :
    o.reverse.indegree v = o.outdegree v := by
  classical
  simp [indegree_def, outdegree_def]

@[simp]
theorem outdegree_reverse (o : Orientation G) (v : G.vertexSet) :
    o.reverse.outdegree v = o.indegree v := by
  simpa using (o.reverse.indegree_reverse v).symm

/-- Reversal turns any condition on outdegrees into the same condition on indegrees. -/
theorem exists_outdegree_iff_exists_indegree (P : (G.vertexSet → ℕ) → Prop) :
    (∃ o : Orientation G, P o.outdegree) ↔ ∃ o : Orientation G, P o.indegree := by
  constructor <;> rintro ⟨o, ho⟩ <;> refine ⟨o.reverse, ?_⟩
  · simpa [funext o.indegree_reverse] using ho
  · simpa [funext o.outdegree_reverse] using ho

/-- The total indegree on `S` counts the actual edges whose head lies in `S`. -/
theorem sum_indegree_eq_card_filter [DecidableEq G.vertexSet] (o : Orientation G)
    (S : Finset G.vertexSet) : ∑ v ∈ S, o.indegree v = #{e | o.head e ∈ S} := by
  simp only [indegree_def, card_filter]
  rw [sum_comm]
  simp

/-- The indegrees of an orientation sum to the number of actual edges, loops included. -/
theorem sum_indegree [Fintype G.vertexSet] (o : Orientation G) :
    ∑ v, o.indegree v = Fintype.card G.edgeSet := by
  classical
  simp [sum_indegree_eq_card_filter]

/-- The outdegrees of an orientation sum to the number of actual edges, loops included. -/
theorem sum_outdegree [Fintype G.vertexSet] (o : Orientation G) :
    ∑ v, o.outdegree v = Fintype.card G.edgeSet := by
  simpa using o.reverse.sum_indegree

/-- Every edge internal to `S` has its head in `S`, so it is counted by the total indegree on
`S`. -/
theorem card_internalEdges_le_sum_indegree (o : Orientation G) (S : Finset G.vertexSet) :
    #(G.internalEdges S) ≤ ∑ v ∈ S, o.indegree v := by
  classical
  rw [sum_indegree_eq_card_filter]
  refine card_le_card fun e he ↦ mem_filter.2 ⟨mem_univ e, ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := G.mem_internalEdges.1 he
  rcases (o.isLink e).eq_and_eq_or_eq_and_eq hxy with ⟨-, h⟩ | ⟨-, h⟩
  · rwa [Subtype.ext h]
  · rwa [Subtype.ext h]

/-- Every edge with its head in `S` is incident with `S`, so the total indegree on `S` is at most
the number of edges incident with `S`. -/
theorem sum_indegree_le_card_incidentEdges (o : Orientation G) (S : Finset G.vertexSet) :
    ∑ v ∈ S, o.indegree v ≤ #(G.incidentEdges S) := by
  classical
  rw [sum_indegree_eq_card_filter]
  exact card_le_card fun e he ↦ G.mem_incidentEdges.2 ⟨_, (mem_filter.1 he).2, o.head_inc e⟩

end Graph.Orientation
