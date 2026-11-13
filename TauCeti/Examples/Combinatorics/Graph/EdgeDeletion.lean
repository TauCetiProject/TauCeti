/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Project
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Deletion

/-!
# Counting surviving parallel edges and loops

These examples delete one of two parallel edges, or one of two loops, along with a nonexistent
edge identity. They check the internal- and incident-edge deletion formulas on finite graphs
whose ambient vertex and edge types are both infinite. Deleting all edges leaves the actual
vertices in place.
-/

public section

namespace TauCeti.Examples.EdgeDeletion

open Graph

/-- Two vertices joined by two parallel edges, on infinite ambient types. -/
abbrev parallel : Graph ℕ ℕ := Graph.banana 0 1 {0, 1}

/-- One vertex carrying two loops, on infinite ambient types. -/
abbrev loops : Graph ℕ ℕ := Graph.bouquet 0 {0, 1}

private abbrev deleted : Set ℕ := {1, 37}

private noncomputable instance : Fintype E(parallel) :=
  Set.Finite.fintype (by simp [parallel])
private noncomputable instance : Fintype E(parallel.deleteEdges deleted) :=
  Set.Finite.fintype ((Set.toFinite E(parallel)).subset Graph.deleteEdges_le.edgeSet_mono)
private noncomputable instance : Fintype E(loops) :=
  Set.Finite.fintype (by simp [loops])
private noncomputable instance : Fintype E(loops.deleteEdges deleted) :=
  Set.Finite.fintype ((Set.toFinite E(loops)).subset Graph.deleteEdges_le.edgeSet_mono)

private abbrev source : V(parallel) := ⟨0, by simp [parallel]⟩
private abbrev sink : V(parallel) := ⟨1, by simp [parallel]⟩
private abbrev base : V(loops) := ⟨0, by simp [loops]⟩

-- The surviving parallel edge retains identity 0; deleting the absent identity 37 has no effect.
example : ((parallel.deleteEdges deleted).incidentEdges ({source} : Finset V(parallel))).map
      (Set.embeddingOfSubset _ _
        (deleteEdges_le (G := parallel) (F := deleted)).edgeSet_mono) =
    {⟨0, by simp [parallel]⟩} := by
  classical
  rw [map_incidentEdges_deleteEdges]
  ext e
  simp [mem_incidentEdges, parallel, source, deleted, Graph.Inc, Subtype.ext_iff]
  omega

-- Exactly one edge remains internal to the pair of vertices.
example : ((parallel.deleteEdges deleted).internalEdges
    ({source, sink} : Finset V(parallel))).card = 1 := by
  classical
  rw [card_internalEdges_deleteEdges]
  have h : (parallel.internalEdges {source, sink}).filter (fun e ↦ e.1 ∉ deleted) =
      {⟨0, by simp [parallel]⟩} := by
    ext e
    simp [mem_internalEdges, parallel, source, sink, deleted, Subtype.ext_iff]
    omega
  simp only [h, Finset.card_singleton]

-- A singleton contains no nonloop edge internally, even though both parallel edges meet it.
example : ((parallel.deleteEdges deleted).internalEdges
    ({source} : Finset V(parallel))).card = 0 := by
  classical
  rw [card_internalEdges_deleteEdges]
  simp [mem_internalEdges, parallel, source]

-- A surviving loop is counted once, both as internal and as incident to its base vertex.
example : ((loops.deleteEdges deleted).internalEdges ({base} : Finset V(loops))).card = 1 ∧
    ((loops.deleteEdges deleted).incidentEdges ({base} : Finset V(loops))).card = 1 := by
  classical
  have hi : (loops.internalEdges {base}).filter (fun e ↦ e.1 ∉ deleted) =
      {⟨0, by simp [loops]⟩} := by
    ext e
    simp [mem_internalEdges, loops, base, deleted, Subtype.ext_iff]
    omega
  have hj : (loops.incidentEdges {base}).filter (fun e ↦ e.1 ∉ deleted) =
      {⟨0, by simp [loops]⟩} := by
    ext e
    simp [mem_incidentEdges, loops, base, deleted, Graph.Inc, Subtype.ext_iff]
    omega
  rw [card_internalEdges_deleteEdges, card_incidentEdges_deleteEdges]
  simp only [hi, hj, Finset.card_singleton, and_self]

-- Deletion does not discard a vertex when its last incident edges disappear.
example : V(parallel.deleteEdges {0, 1}) = {0, 1} ∧
    E(parallel.deleteEdges {0, 1}) = ∅ := by
  simp [parallel]

end TauCeti.Examples.EdgeDeletion
