/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.CutTree

/-!
# Relabelling cut trees

A vertex equivalence relabels a weighted tree and its set function without changing the
minimum-cut certificates. In particular it carries fundamental partitions to fundamental
partitions, not just pairwise minimum-cut values. This allows a cut tree constructed on one
finite carrier to answer cut queries on an isomorphic carrier.

The transport results use a graph isomorphism and separate compatibility hypotheses for the
set functions and edge weights. Weight compatibility is required only on actual tree edges;
weights on non-edges are irrelevant. Neither symmetry nor submodularity is needed.

The underlying relabelling results are `SimpleGraph.Iso.map_edgeSide` and
`TauCeti.TerminalCut.pairMinimumValue_map`.
-/

public section

namespace TauCeti.TerminalCut

open Finset SimpleGraph

variable {V W K : Type*} [Zero K] [LinearOrder K]
    {f : Finset V → K} {g : Finset W → K}
    {T : SimpleGraph V} {T' : SimpleGraph W} {w : Sym2 V → K} {w' : Sym2 W → K}

section FlowEquivalent

variable [Finite V] [Finite W]

/-- Relabelling a weighted tree and its set function preserves flow-equivalence. Only weights
of actual tree edges need to agree. -/
theorem IsFlowEquivalentTree.map (hT : IsFlowEquivalentTree f T w) (e : T ≃g T')
    (hfg : ∀ S, g (S.map e.toEquiv.toEmbedding) = f S)
    (hw : ∀ a ∈ T.edgeSet, w' (a.map e) = w a) : IsFlowEquivalentTree g T' w' := by
  have hval (s t : V) : pairMinimumValue g (e s) (e t) = pairMinimumValue f s t := by
    simpa only [RelIso.coe_fn_toEquiv] using pairMinimumValue_map f e.toEquiv g hfg s t
  have pullback {s t : V} {p : T'.Walk (e s) (e t)} (hp : p.IsPath) :
      ∃ q : T.Walk s t, q.IsPath ∧ q.edges.map (Sym2.map e) = p.edges := by
    let q : T.Walk s t := (p.map e.symm.toHom).copy
      (e.symm_apply_apply s) (e.symm_apply_apply t)
    refine ⟨q, ?_, ?_⟩
    · simpa [q] using hp.map (f := e.symm.toHom) e.symm.injective
    · simp [q, List.map_map, Sym2.map_map, Function.comp_def]
  refine ⟨e.isTree_iff.mp hT.isTree, ?_, ?_⟩
  · intro s' t' p hp a ha
    obtain ⟨s, rfl⟩ := e.surjective s'
    obtain ⟨t, rfl⟩ := e.surjective t'
    obtain ⟨q, hq, he⟩ := pullback hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (he ▸ ha)
    rw [hw b (q.edges_subset_edgeSet hb), hval]
    exact hT.le_weight hq hb
  · intro s' t' hst p hp
    obtain ⟨s, rfl⟩ := e.surjective s'
    obtain ⟨t, rfl⟩ := e.surjective t'
    obtain ⟨q, hq, he⟩ := pullback hp
    obtain ⟨b, hb, hbw⟩ := hT.exists_weight_eq (fun h ↦ hst (congrArg e h)) hq
    refine ⟨b.map e, he ▸ List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [hw b (q.edges_subset_edgeSet hb), hbw, hval]

/-- Flow-equivalence is invariant under compatible relabelling of vertices and edge weights. -/
theorem isFlowEquivalentTree_map_iff (e : T ≃g T')
    (hfg : ∀ S, g (S.map e.toEquiv.toEmbedding) = f S)
    (hw : ∀ a ∈ T.edgeSet, w' (a.map e) = w a) :
    IsFlowEquivalentTree g T' w' ↔ IsFlowEquivalentTree f T w := by
  refine ⟨fun hT ↦ hT.map e.symm ?_ ?_, fun hT ↦ hT.map e hfg hw⟩
  · intro S
    simpa [Finset.map_map] using (hfg (S.map e.symm.toEquiv.toEmbedding)).symm
  · intro a ha
    have h := hw (a.map e.symm) (e.symm.map_mem_edgeSet_iff.mpr ha)
    simpa [Sym2.map_map, Function.comp_def] using h.symm

end FlowEquivalent

section CutTree

variable [Fintype V] [Fintype W]

/-- Relabelling preserves a cut tree together with its fundamental minimum-cut partitions. -/
theorem IsCutTree.map (hT : IsCutTree f T w) (e : T ≃g T')
    (hfg : ∀ S, g (S.map e.toEquiv.toEmbedding) = f S)
    (hw : ∀ a ∈ T.edgeSet, w' (a.map e) = w a) : IsCutTree g T' w' := by
  refine { hT.toIsFlowEquivalentTree.map e hfg hw with isMinimum_edgeSide := ?_ }
  intro u' v' huv
  obtain ⟨u, rfl⟩ := e.surjective u'
  obtain ⟨v, rfl⟩ := e.surjective v'
  have hmin := (isMinimum_map_iff e.toEquiv hfg).mpr
    (hT.isMinimum_edgeSide (e.map_adj_iff.mp huv))
  simpa only [Finset.map_singleton, e.map_edgeSide, RelIso.coe_toEmbedding] using hmin

/-- The cut-tree property, including its minimum-cut witnesses, is invariant under compatible
relabelling. -/
theorem isCutTree_map_iff (e : T ≃g T')
    (hfg : ∀ S, g (S.map e.toEquiv.toEmbedding) = f S)
    (hw : ∀ a ∈ T.edgeSet, w' (a.map e) = w a) :
    IsCutTree g T' w' ↔ IsCutTree f T w := by
  refine ⟨fun hT ↦ hT.map e.symm ?_ ?_, fun hT ↦ hT.map e hfg hw⟩
  · intro S
    simpa [Finset.map_map] using (hfg (S.map e.symm.toEquiv.toEmbedding)).symm
  · intro a ha
    have h := hw (a.map e.symm) (e.symm.map_mem_edgeSet_iff.mpr ha)
    simpa [Sym2.map_map, Function.comp_def] using h.symm

end CutTree

end TauCeti.TerminalCut
