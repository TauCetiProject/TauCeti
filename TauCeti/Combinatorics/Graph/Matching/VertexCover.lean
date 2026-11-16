/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Capacitated
public import TauCeti.Combinatorics.Graph.VertexCover.SimpleGraph

/-!
# Matchings, vertex covers, and Kőnig's theorem for multigraphs

Every ordinary matching `M` of a multigraph `G` has extended cardinality at most that of every
vertex cover of `G`, and indeed at most the vertex cover number `G.toSimpleGraph.vertexCoverNum` of
its underlying simple graph: no edge of `M` is a loop, so every edge of `M` descends to an edge of
`G.toSimpleGraph` and meets any cover of `G.toSimpleGraph` in a distinct vertex. Neither finiteness
nor looplessness of `G` is needed for these weak-duality bounds. For a loopless multigraph with
finitely many actual edges, unit-capacity multiset matchings satisfy the same bound.

Given a finite covering bipartition of a multigraph with finitely many actual edges, **Kőnig's
theorem** holds: the maximum size of a matching equals the minimum size of a vertex cover, which
coincides with `G.toSimpleGraph.vertexCoverNum`. Thus the matching side retains actual multigraph
edge identities (allowing parallel edges and isolated vertices), while the cover optimum uses
Mathlib's canonical `SimpleGraph.vertexCoverNum` interface.

## Main results

* `Graph.IsMatching.encard_le_encard_of_isVertexCover` and
  `Graph.IsMatching.encard_le_vertexCoverNum`: weak duality for ordinary matchings, without
  finiteness or looplessness assumptions.
* `Graph.IsCapacitatedMatching.sum_le_vertexCoverNum` and
  `Graph.IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum`: weak duality and
  attainment for unit-capacity multiset matchings.
* `Graph.IsBipartition.exists_isMatching_isVertexCover_card_eq` and
  `Graph.IsBipartition.exists_isMatching_isVertexCover_ncard_eq`: **Kőnig's theorem** for ordinary
  matchings in finite bipartite multigraphs, in witness form.
* `Graph.IsBipartition.exists_isMatching_encard_eq_vertexCoverNum` and
  `Graph.IsBipartition.iSup_encard_isMatching_eq_vertexCoverNum`: attainment and min-max identity
  against `G.toSimpleGraph.vertexCoverNum`.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 21.1.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Weak duality for ordinary matchings -/

namespace IsMatching

/-- Every matching has extended cardinality at most that of every vertex cover of the
simplification `G.toSimpleGraph`, even if `G` carries loops outside the matching. -/
theorem encard_le_encard_of_toSimpleGraph_isVertexCover {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.toSimpleGraph.IsVertexCover C) :
    M.encard ≤ C.encard := by
  -- No edge of a matching is a loop, so each edge of `M` descends to an edge of `G.toSimpleGraph`.
  have hex {e : E(G)} (heM : e ∈ M) : ∃ v ∈ C, G.Inc e v := by
    obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet e.2
    have hne : (⟨x, he.left_mem⟩ : V(G)) ≠ ⟨y, he.right_mem⟩ := by
      intro h
      have hxy : x = y := congrArg Subtype.val h
      exact hM.not_isLoopAt heM x (hxy ▸ he)
    have hadj : G.toSimpleGraph.Adj ⟨x, he.left_mem⟩ ⟨y, he.right_mem⟩ := by
      rw [G.toSimpleGraph_adj]
      exact ⟨hne, e, he⟩
    rcases hC hadj with hx | hy
    exacts [⟨⟨x, he.left_mem⟩, hx, he.inc_left⟩, ⟨⟨y, he.right_mem⟩, hy, he.inc_right⟩]
  choose f hfC hfInc using fun e : M ↦ hex e.2
  refine Function.Embedding.encard_le ⟨fun e ↦ ⟨f e, hfC e⟩, fun e e' h ↦ Subtype.ext ?_⟩
  have hfe : f e = f e' := congrArg Subtype.val h
  exact hM.eq_of_inc e.2 e'.2 (hfInc e) (hfe ▸ hfInc e')

/-- **Weak duality for ordinary matchings.** Every matching has extended cardinality at most that
of every vertex cover, without any finiteness or looplessness assumption. -/
theorem encard_le_encard_of_isVertexCover {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.IsVertexCover C) :
    M.encard ≤ C.encard :=
  hM.encard_le_encard_of_toSimpleGraph_isVertexCover hC.toSimpleGraph

/-- Every matching has cardinality at most that of every finite vertex cover. -/
theorem ncard_le_ncard_of_isVertexCover {M : Set E(G)} (hM : G.IsMatching M)
    {C : Set V(G)} (hC : G.IsVertexCover C) (hCf : C.Finite) :
    M.ncard ≤ C.ncard := by
  rw [Set.ncard_def, Set.ncard_def]
  exact ENat.toNat_le_toNat (hM.encard_le_encard_of_isVertexCover hC) hCf.encard_lt_top.ne

/-- Every finite matching has cardinality at most that of every finite vertex cover. -/
theorem card_le_card_of_isVertexCover {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G)))
    {C : Finset V(G)} (hC : G.IsVertexCover (C : Set V(G))) :
    M.card ≤ C.card := by
  simpa only [Set.ncard_coe_finset] using hM.ncard_le_ncard_of_isVertexCover hC C.finite_toSet

/-- **Weak duality with the simple-graph cover number.** Every ordinary matching has extended
cardinality at most the vertex cover number of the simplification `G.toSimpleGraph`. -/
theorem encard_le_vertexCoverNum {M : Set E(G)} (hM : G.IsMatching M) :
    M.encard ≤ G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨C, hCnum, hC⟩ := G.toSimpleGraph.vertexCoverNum_exists
  exact hCnum ▸ hM.encard_le_encard_of_toSimpleGraph_isVertexCover hC

/-- Every finite matching has cardinality at most `G.toSimpleGraph.vertexCoverNum`. -/
theorem card_le_vertexCoverNum {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G))) :
    (M.card : ℕ∞) ≤ G.toSimpleGraph.vertexCoverNum := by
  simpa only [Set.encard_coe_eq_coe_finsetCard] using hM.encard_le_vertexCoverNum

end IsMatching

/-! ### Unit-capacity matchings and the vertex cover number -/

section UnitCapacitated

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

end UnitCapacitated

/-! ### Kőnig's theorem for ordinary matchings -/

namespace IsBipartition

variable [Finite E(G)] {L R : Finset V(G)}

/-- **Kőnig's theorem for finite bipartite multigraphs.** Given a finite covering bipartition of a
multigraph with finitely many actual edges, some finite matching and some finite vertex cover have
equal cardinality. -/
theorem exists_isMatching_isVertexCover_card_eq (hLR : G.IsBipartition L R) :
    ∃ (M : Finset E(G)) (C : Finset V(G)),
      G.IsMatching (M : Set E(G)) ∧ G.IsVertexCover (C : Set V(G)) ∧ M.card = C.card := by
  classical
  let _ := Fintype.ofFinite E(G)
  obtain ⟨x, C, hx, hC, hxC⟩ := hLR.exists_isCapacitatedMatching_isVertexCover_sum_eq (fun _ ↦ 1)
  refine ⟨Finset.univ.filter fun e ↦ x e ≠ 0, C, hx.supportFinset_isMatching hLR.loopless, hC, ?_⟩
  simpa [hx.sum_eq_card_support] using hxC

/-- **Kőnig's theorem for finite bipartite multigraphs** (`Set.ncard` form): some matching `M` and
some vertex cover `C` satisfy `M.ncard = C.ncard`. -/
theorem exists_isMatching_isVertexCover_ncard_eq (hLR : G.IsBipartition L R) :
    ∃ (M : Set E(G)) (C : Set V(G)), G.IsMatching M ∧ G.IsVertexCover C ∧ M.ncard = C.ncard := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hLR.exists_isMatching_isVertexCover_card_eq
  refine ⟨M, C, hM, hC, ?_⟩
  simpa only [Set.ncard_coe_finset] using hMC

/-- In a multigraph with finitely many actual edges and a finite covering bipartition, some finite
matching attains the vertex cover number of the simplification `G.toSimpleGraph`. -/
theorem exists_isMatching_card_eq_vertexCoverNum (hLR : G.IsBipartition L R) :
    ∃ M : Finset E(G),
      G.IsMatching (M : Set E(G)) ∧ (M.card : ℕ∞) = G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hLR.exists_isMatching_isVertexCover_card_eq
  refine ⟨M, hM, le_antisymm hM.card_le_vertexCoverNum ?_⟩
  simpa [hMC] using hC.toSimpleGraph.vertexCoverNum_le

/-- In a multigraph with finitely many actual edges and a finite covering bipartition, some
matching has extended cardinality equal to `G.toSimpleGraph.vertexCoverNum`. -/
theorem exists_isMatching_encard_eq_vertexCoverNum (hLR : G.IsBipartition L R) :
    ∃ M : Set E(G), G.IsMatching M ∧ M.encard = G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨M, hM, hMnum⟩ := hLR.exists_isMatching_card_eq_vertexCoverNum
  exact ⟨M, hM, by simpa only [Set.encard_coe_eq_coe_finsetCard] using hMnum⟩

/-- **Kőnig's min-max identity for bipartite multigraphs.** The supremum of the extended
cardinalities of all matchings of `G` equals `G.toSimpleGraph.vertexCoverNum`. -/
theorem iSup_encard_isMatching_eq_vertexCoverNum (hLR : G.IsBipartition L R) :
    (⨆ (M : Set E(G)) (_ : G.IsMatching M), M.encard) = G.toSimpleGraph.vertexCoverNum := by
  obtain ⟨M, hM, hMnum⟩ := hLR.exists_isMatching_encard_eq_vertexCoverNum
  refine le_antisymm (iSup₂_le fun N hN ↦ hN.encard_le_vertexCoverNum) ?_
  exact hMnum ▸ le_iSup₂ (f := fun (N : Set E(G)) (_ : G.IsMatching N) ↦ N.encard) M hM

end IsBipartition

end Graph
