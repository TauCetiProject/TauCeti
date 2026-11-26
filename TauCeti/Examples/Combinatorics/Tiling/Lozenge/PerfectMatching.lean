/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.PerfectMatching

/-!
# Checks: tilings are perfect matchings

* `R = ∅`: the empty tiling is the only tiling, and it corresponds to the empty perfect matching
  of the empty graph, which is its only perfect matching.
* `R = {W(0)}`: neither side of `tilingSubgraph_bijOn` has an element: a single face has no tiling
  (both faces of an edge of a tiling lie in the region), and a graph with one vertex has no
  perfect matching.
-/

public section

namespace TauCeti.Examples.LozengePerfectMatchingChecks

open TauCeti

/-! ### The empty region -/

/-- The empty tiling is the only tiling of the empty region. -/
example {M : Set TriEdge} : IsTiling ∅ M ↔ M = ∅ := isTiling_empty_iff

/-- The empty tiling corresponds to a perfect matching of the empty graph. -/
example : (tilingSubgraph ∅ ∅).IsPerfectMatching :=
  (tilingSubgraph_bijOn ∅).mapsTo (isTiling_empty_iff.2 rfl)

/-- The empty graph has exactly one perfect matching, the image of the empty tiling. -/
example : {P : (SimpleGraph.induce (∅ : Set TriFace) hexGraph).Subgraph | P.IsPerfectMatching} =
    {tilingSubgraph ∅ ∅} := by
  have hsub : Subsingleton (SimpleGraph.induce (∅ : Set TriFace) hexGraph).Subgraph :=
    ⟨fun P Q => SimpleGraph.Subgraph.ext (Set.eq_of_subset_of_subset (fun v => isEmptyElim v)
      fun v => isEmptyElim v) (funext fun v => isEmptyElim v)⟩
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸
    (tilingSubgraph_bijOn ∅).mapsTo (isTiling_empty_iff.2 rfl)⟩

/-- The perfect matching of the empty graph has no edges. -/
example : (tilingSubgraph ∅ ∅).edgeSet = ∅ :=
  Set.eq_empty_of_isEmpty _

/-! ### A single face -/

/-- The white face `W(0)`. -/
abbrev whiteZero : TriFace := ⟨(0, 0), true⟩

/-- A single face has no tiling: an edge of a tiling of `{W(0)}` would have both of its faces equal
to `W(0)`. -/
theorem not_isTiling_whiteZero (M : Set TriEdge) : ¬IsTiling {whiteZero} M := by
  intro h
  obtain ⟨e, ⟨he, -⟩, -⟩ := h.existsUnique (Set.mem_singleton whiteZero)
  have hw : e.whiteFace = whiteZero := h.whiteFace_mem he
  have hb : e.blackFace = whiteZero := h.blackFace_mem he
  exact e.whiteFace_ne_blackFace (hw.trans hb.symm)

/-- The graph with the single vertex `W(0)` has no perfect matching: by `tilingSubgraph_bijOn` it
would come from a tiling of `{W(0)}`. -/
example (P : (SimpleGraph.induce ({whiteZero} : Set TriFace) hexGraph).Subgraph) :
    ¬P.IsPerfectMatching := fun hP => by
  obtain ⟨M, hM, -⟩ := (tilingSubgraph_bijOn _).surjOn hP
  exact not_isTiling_whiteZero M hM

end TauCeti.Examples.LozengePerfectMatchingChecks
