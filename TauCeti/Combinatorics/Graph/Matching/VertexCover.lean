/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Capacitated
public import TauCeti.Combinatorics.Graph.VertexCover.SimpleGraph

import TauCeti.Combinatorics.Graph.Simple

/-!
# Matchings and the vertex cover number

For a multigraph `G`, every ordinary matching has cardinality at most that of every vertex cover,
and at most the vertex cover number of the underlying simple graph `G.toSimpleGraph`. Because an
ordinary matching contains no loops, these weak-duality bounds need neither finiteness nor
looplessness. For unit-capacity multiset matchings on a loopless multigraph with finitely many
actual edges, the analogous bound holds for the total multiplicity.

Given a finite covering bipartition on a multigraph with finitely many actual edges, both bounds
are attained: the multiset capacitated Kőnig theorem of
`TauCeti.Combinatorics.Graph.Matching.Capacitated` yields a unit-capacity matching and a vertex
cover of equal size, and taking the positive support gives an ordinary matching of the same
cardinality. Thus the matching side retains actual edge identities (allowing parallel edges and
isolated vertices), while the cover optimum uses `SimpleGraph.vertexCoverNum`.

## Main results

* `Graph.IsMatching.encard_le_of_isVertexCover`, `Graph.IsMatching.encard_le_vertexCoverNum`:
  weak duality for ordinary matchings, without finiteness or looplessness hypotheses.
* `Graph.IsBipartition.exists_isMatching_isVertexCover_card_eq`,
  `Graph.IsBipartition.exists_isMatching_card_eq_vertexCoverNum`: **Kőnig's theorem** for ordinary
  matchings in finite bipartite multigraphs.
* `Graph.IsCapacitatedMatching.sum_le_vertexCoverNum`,
  `Graph.IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum`: the corresponding
  statements for unit-capacity multiset matchings.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Ordinary matchings and vertex covers -/

/-- **Weak duality with covers of the simplification.** Every matching in a multigraph has
cardinality at most that of any vertex cover of its underlying simple graph, even if `G` carries
loops outside the matching. -/
theorem IsMatching.encard_le_of_isVertexCover_toSimpleGraph {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.toSimpleGraph.IsVertexCover C) :
    M.encard ≤ C.encard := by
  -- Each selected edge is nonloop, so it projects to a simple-graph edge and meets `C`; since
  -- matching edges are vertex-disjoint, choosing an incident cover vertex is injective.
  have hex (e : M) : ∃ v : C, G.Inc e.val v.val := by
    obtain ⟨x, y, he⟩ : ∃ x y, G.IsLink e.val x y := G.exists_isLink_of_mem_edgeSet e.val.property
    have hxy : x ≠ y := fun h ↦
      hM.not_isLoopAt e.property x (isLink_self_iff.mp (h ▸ he))
    rcases hC (he.toSimpleGraph_adj hxy) with hx | hy
    exacts [⟨⟨⟨x, he.left_mem⟩, hx⟩, he.inc_left⟩, ⟨⟨⟨y, he.right_mem⟩, hy⟩, he.inc_right⟩]
  choose f hf using hex
  exact Function.Embedding.encard_le
    ⟨f, fun e₁ e₂ h ↦ Subtype.ext <| hM.eq_of_inc e₁.property e₂.property (hf e₁) (h ▸ hf e₂)⟩

/-- **Weak duality for ordinary matchings.** The cardinality of a matching is at most that of any
vertex cover. -/
theorem IsMatching.encard_le_of_isVertexCover {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.IsVertexCover C) :
    M.encard ≤ C.encard :=
  hM.encard_le_of_isVertexCover_toSimpleGraph hC.toSimpleGraph

/-- **Weak duality for ordinary matchings** in `Set.ncard` form, for a finite vertex cover. -/
theorem IsMatching.ncard_le_of_isVertexCover {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.IsVertexCover C) (hCf : C.Finite) :
    M.ncard ≤ C.ncard := by
  have hle := hM.encard_le_of_isVertexCover hC
  have hMf : M.Finite := hCf.finite_of_encard_le hle
  rwa [← hMf.cast_ncard_eq, ← hCf.cast_ncard_eq, Nat.cast_le] at hle

/-- **Weak duality for finite ordinary matchings and finite vertex covers.** -/
theorem IsMatching.card_le_card_of_isVertexCover {M : Finset E(G)}
    (hM : G.IsMatching (M : Set E(G))) {C : Finset V(G)} (hC : G.IsVertexCover (C : Set V(G))) :
    M.card ≤ C.card := by
  simpa using hM.ncard_le_of_isVertexCover hC C.finite_toSet

/-- **Weak duality with the simple-graph cover number.** Every matching in a multigraph has
cardinality at most the vertex cover number of its simplification. -/
theorem IsMatching.encard_le_vertexCoverNum {M : Set E(G)} (hM : G.IsMatching M) :
    M.encard ≤ G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨C, hCnum, hC⟩ := G.toSimpleGraph.vertexCoverNum_exists
  exact hCnum ▸ hM.encard_le_of_isVertexCover_toSimpleGraph hC

/-- **Kőnig's theorem for ordinary matchings in multigraphs.** A multigraph with finitely many
actual edges and a finite covering bipartition has an ordinary matching and a vertex cover of equal
cardinality. -/
theorem IsBipartition.exists_isMatching_isVertexCover_card_eq [Finite E(G)]
    {L R : Finset V(G)} (hLR : G.IsBipartition L R) :
    ∃ (M : Finset E(G)) (C : Finset V(G)), G.IsMatching (M : Set E(G)) ∧
      G.IsVertexCover (C : Set V(G)) ∧ M.card = C.card := by
  classical
  let _ := Fintype.ofFinite E(G)
  obtain ⟨x, C, hx, hC, hxC⟩ := hLR.exists_isCapacitatedMatching_isVertexCover_sum_eq (fun _ ↦ 1)
  refine ⟨Finset.univ.filter fun e ↦ x e ≠ 0, C, hx.supportFinset_isMatching hLR.loopless, hC, ?_⟩
  simpa [hx.sum_eq_card_support] using hxC

/-- **Kőnig's theorem with the simple-graph cover number.** A multigraph with finitely many actual
edges and a finite covering bipartition has an ordinary matching whose cardinality equals the
vertex cover number of its simplification. -/
theorem IsBipartition.exists_isMatching_card_eq_vertexCoverNum [Finite E(G)]
    {L R : Finset V(G)} (hLR : G.IsBipartition L R) :
    ∃ M : Finset E(G), G.IsMatching (M : Set E(G)) ∧
      (M.card : ℕ∞) = G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hLR.exists_isMatching_isVertexCover_card_eq
  refine ⟨M, hM, le_antisymm ?_ ?_⟩
  · simpa using hM.encard_le_vertexCoverNum
  · simpa [hMC] using hC.toSimpleGraph.vertexCoverNum_le

/-! ### Unit-capacity multiset matchings -/

section Fintype

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

end Fintype

end Graph
