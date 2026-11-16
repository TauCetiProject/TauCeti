/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Capacitated
public import TauCeti.Combinatorics.Graph.VertexCover.SimpleGraph

/-!
# Unit-capacity matchings and the vertex cover number

For a loopless multigraph, the size of a unit-capacity matching is at most the vertex cover
number of its underlying simple graph. Given a finite covering bipartition, the bound is attained.
Thus the matching side retains actual edge identities, while the cover optimum uses Mathlib's
canonical `SimpleGraph.vertexCoverNum` interface. Parallel edges and isolated vertices are
allowed. Weak duality requires only finitely many actual edges; attainment also requires two
finite bipartition sides covering every actual vertex.

The attainment result specializes the multiset capacitated Kőnig theorem proved in
`TauCeti.Combinatorics.Graph.Matching.Capacitated`.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}
variable [Fintype E(G)]

/-- **Weak duality with the simple-graph cover number.** A unit-capacity matching in a loopless
multigraph has size at most the vertex cover number of its simplification. -/
theorem IsCapacitatedMatching.sum_le_vertexCoverNum [G.Loopless]
    {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x) :
    (∑ e, x e : ℕ) ≤ G.toSimpleGraph.vertexCoverNum := by
  classical
  obtain ⟨C, hCnum, hC⟩ := G.toSimpleGraph.vertexCoverNum_exists
  by_cases hCf : C.Finite
  · have hCG : G.IsVertexCover C := isVertexCover_toSimpleGraph_iff.1 hC
    have h := hx.sum_le_sum_of_isVertexCover (C := hCf.toFinset) (by simpa using hCG)
    simp only [sum_const, smul_eq_mul, mul_one] at h
    exact (Nat.cast_le.mpr h).trans_eq (by simpa [hCf.encard_eq_coe_toFinset_card] using hCnum)
  · simp [← hCnum, Set.Infinite.encard_eq hCf]

/-- **Kőnig's theorem with the simple-graph cover number.** A multigraph with finitely many
actual edges and a finite covering bipartition has a unit-capacity matching whose size is the
vertex cover number of its simplification. -/
theorem IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum
    {L R : Finset V(G)} (hLR : G.IsBipartition L R) :
    ∃ x : E(G) → ℕ, G.IsCapacitatedMatching (fun _ ↦ 1) x ∧
      (∑ e, x e : ℕ) = G.toSimpleGraph.vertexCoverNum := by
  classical
  let : G.Loopless := hLR.loopless
  obtain ⟨x, C, hx, hC, hxC⟩ := hLR.exists_isCapacitatedMatching_isVertexCover_sum_eq (fun _ ↦ 1)
  refine ⟨x, hx, le_antisymm hx.sum_le_vertexCoverNum ?_⟩
  have h := hC.toSimpleGraph.vertexCoverNum_le
  simpa [hxC] using h

end Graph
