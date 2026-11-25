/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.MarkedTree

/-!
# Checks for the cover graph of a coded order

The cover graph of the chain `(ℕ, ≤)` with its least element marked is a ray with its end marked:
`u` and `v` are adjacent exactly when they differ by one, and `0` is the only marked vertex. In
particular it is a marked tree, so `markedTreeClass` contains an infinite code.
-/

public section

open FirstOrder FirstOrder.Language TauCeti TauCeti.RelationalConfiguration

namespace TauCeti.Examples.MarkedTree

/-- The code of the chain `(ℕ, ≤)`. -/
noncomputable abbrev chain : RelationalConfiguration Language.order ℕ :=
  @ofStructure Language.order ℕ (orderStructure ℕ)

private theorem relCovBy_chain (u v : ℕ) : RelCovBy (codeRel leSymb chain) u v ↔ u + 1 = v := by
  simp only [relCovBy_iff, chain, codeRel_leSymb_ofStructure_orderStructure, not_le]
  refine ⟨fun ⟨⟨_, _⟩, hw⟩ => ?_, fun h => ⟨⟨by omega, by omega⟩, fun w => by omega⟩⟩
  by_contra hne
  exact hw (u + 1) ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- In the cover graph of `(ℕ, ≤)`, two vertices are adjacent exactly when they differ by one. -/
private theorem codeRel_coverGraphCode_chain (u v : ℕ) :
    codeRel adjSymb (coverGraphCode chain) u v ↔ u + 1 = v ∨ v + 1 = u := by
  rw [codeRel_coverGraphCode, relCovBy_chain, relCovBy_chain]

/-- In the cover graph of `(ℕ, ≤)`, the only marked vertex is `0`. -/
private theorem isMarked_coverGraphCode_chain (v : ℕ) :
    IsMarked (coverGraphCode chain) v ↔ v = 0 := by
  simp only [isMarked_coverGraphCode, chain, codeRel_leSymb_ofStructure_orderStructure]
  exact ⟨fun h => Nat.le_zero.1 (h 0), fun h w => h ▸ Nat.zero_le w⟩

/-- The graph of the cover graph of `(ℕ, ≤)` is the Hasse diagram of `ℕ`. -/
private theorem markedGraph_coverGraphCode_chain :
    markedGraph (coverGraphCode chain) = SimpleGraph.hasse ℕ := by
  ext u v
  simp only [markedGraph_adj, codeRel_coverGraphCode_chain, SimpleGraph.hasse_adj,
    Nat.covBy_iff_add_one_eq]
  omega

/-- The Hasse diagram of `ℕ`, the ray, is a tree: every walk between adjacent vertices crosses
the edge joining them. -/
private theorem isTree_hasse_nat : (SimpleGraph.hasse ℕ).IsTree := by
  refine ⟨⟨SimpleGraph.preconnected_hasse_of_succOrder ℕ⟩,
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.2 fun u v huv => ?_⟩
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  rcases le_total u v with h | h
  · have hd : (⟨(u, v), huv⟩ : (SimpleGraph.hasse ℕ).Dart) ∈ p.darts :=
      SimpleGraph.Walk.mem_darts_hasse_of_ge_of_le_of_le ℕ p le_rfl h le_rfl
    exact SimpleGraph.Walk.edge_mem_edges_of_mem_darts hd
  · have hd : (⟨(v, u), huv.symm⟩ : (SimpleGraph.hasse ℕ).Dart) ∈ p.reverse.darts :=
      SimpleGraph.Walk.mem_darts_hasse_of_ge_of_le_of_le ℕ p.reverse le_rfl h le_rfl
    have he := SimpleGraph.Walk.edge_mem_edges_of_mem_darts hd
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    simpa [Sym2.eq_swap] using he

/-- The cover graph of `(ℕ, ≤)` is a marked tree: the ray with its end `0` marked. -/
example : coverGraphCode chain ∈ markedTreeClass := by
  refine mem_markedTreeClass.2 ⟨fun u v h => ?_, fun v h => ?_,
    markedGraph_coverGraphCode_chain ▸ isTree_hasse_nat, 0, (isMarked_coverGraphCode_chain 0).2 rfl,
    fun v hv => (isMarked_coverGraphCode_chain v).1 hv⟩
  · rw [codeRel_coverGraphCode_chain] at h ⊢
    exact h.symm
  · rw [codeRel_coverGraphCode_chain] at h
    omega

end TauCeti.Examples.MarkedTree
