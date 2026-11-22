/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic
public import TauCeti.Combinatorics.Graph.Isomorphism.Basic

/-!
# Isomorphism invariance of multigraph incidence counts

A multigraph isomorphism carries the edges at an actual vertex to the edges at its image, and the
loops at that vertex to the loops at its image (`Graph.Iso.mapEdgeSet_incidenceSet`,
`Graph.Iso.mapEdgeSet_loopSet`). Consequently it preserves both vertex incidence counts, the
finite sets of edges internal to or incident with a finite set of actual vertices, and the
neighbours of one finite set of actual vertices within another. Edge identities are part of the
isomorphism, so parallel edges and loops are counted exactly as in the original graph, and no
finiteness is needed for the vertex counts.
-/

public section

open Set

universe u v u' v'

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

namespace Iso

/-- A graph isomorphism preserves the incidence count of each vertex. -/
@[simp]
theorem incidenceCount_vertexEquiv (f : Iso G H) (x : V(G)) :
    H.incidenceCount (f.vertexEquiv x) = G.incidenceCount x := by
  rw [incidenceCount_def, incidenceCount_def, ← f.mapEdgeSet_incidenceSet,
    f.ncard_mapEdgeSet (G.incidenceSet_subset_edgeSet x)]

/-- A graph isomorphism preserves the nonloop incidence count of each vertex. -/
@[simp]
theorem nonloopIncidenceCount_vertexEquiv (f : Iso G H) (x : V(G)) :
    H.nonloopIncidenceCount (f.vertexEquiv x) = G.nonloopIncidenceCount x := by
  rw [nonloopIncidenceCount_def, nonloopIncidenceCount_def, ← f.mapEdgeSet_incidenceSet,
    ← f.mapEdgeSet_loopSet, ← f.mapEdgeSet_sdiff,
    f.ncard_mapEdgeSet (sdiff_subset.trans (G.incidenceSet_subset_edgeSet x))]

/-- A graph isomorphism carries the neighbours in `T` of `S` to the neighbours in the image of
`T` of the image of `S`. -/
@[simp]
theorem neighborsIn_map (f : Iso G H) (S T : Finset V(G)) :
    H.neighborsIn (S.map f.vertexEquiv.toEmbedding) (T.map f.vertexEquiv.toEmbedding) =
      (G.neighborsIn S T).map f.vertexEquiv.toEmbedding := by
  ext y
  simp only [mem_neighborsIn, Finset.mem_map_equiv]
  refine and_congr_right fun _ ↦ ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨_, hx, ?_⟩,
    fun ⟨x, hx, hxy⟩ ↦ ⟨f.vertexEquiv x, by simpa using hx, ?_⟩⟩
  · rwa [← f.map_adj_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rwa [← f.map_adj_iff, Equiv.apply_symm_apply] at hxy

section FiniteEdges

variable [Fintype G.edgeSet] [Fintype H.edgeSet]

/-- A graph isomorphism carries the edges internal to `S` to the edges internal to its image. -/
@[simp]
theorem internalEdges_map (f : Iso G H) (S : Finset V(G)) :
    H.internalEdges (S.map f.vertexEquiv.toEmbedding) =
      (G.internalEdges S).map f.edgeEquiv.toEmbedding := by
  ext e
  simp only [mem_internalEdges, Finset.mem_map_equiv]
  constructor
  · rintro ⟨x, hx, y, hy, he⟩
    refine ⟨_, hx, _, hy, (f.map_isLink_iff _ _ _).1 ?_⟩
    simpa using he
  · rintro ⟨x, hx, y, hy, he⟩
    refine ⟨f.vertexEquiv x, by simpa using hx, f.vertexEquiv y, by simpa using hy, ?_⟩
    simpa using (f.map_isLink_iff _ _ _).2 he

/-- A graph isomorphism carries the edges internal to a single vertex, namely its loops, to the
edges internal to its image. -/
@[simp]
theorem internalEdges_singleton_vertexEquiv (f : Iso G H) (x : V(G)) :
    H.internalEdges {f.vertexEquiv x} = (G.internalEdges {x}).map f.edgeEquiv.toEmbedding := by
  simpa using f.internalEdges_map {x}

/-- A graph isomorphism carries the edges incident with `S` to the edges incident with its
image. -/
@[simp]
theorem incidentEdges_map (f : Iso G H) (S : Finset V(G)) :
    H.incidentEdges (S.map f.vertexEquiv.toEmbedding) =
      (G.incidentEdges S).map f.edgeEquiv.toEmbedding := by
  ext e
  simp only [mem_incidentEdges, Finset.mem_map_equiv]
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨_, hx, (f.map_inc_iff _ _).1 ?_⟩
    simpa using he
  · rintro ⟨x, hx, he⟩
    refine ⟨f.vertexEquiv x, by simpa using hx, ?_⟩
    simpa using (f.map_inc_iff _ _).2 he

/-- A graph isomorphism carries the edges incident with a vertex to the edges incident with its
image. -/
@[simp]
theorem incidentEdges_singleton_vertexEquiv (f : Iso G H) (x : V(G)) :
    H.incidentEdges {f.vertexEquiv x} = (G.incidentEdges {x}).map f.edgeEquiv.toEmbedding := by
  simpa using f.incidentEdges_map {x}

end FiniteEdges

end Iso

end Graph
