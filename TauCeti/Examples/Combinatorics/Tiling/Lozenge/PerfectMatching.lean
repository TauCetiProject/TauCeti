/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.PerfectMatching
public import TauCeti.Examples.Combinatorics.Tiling.Lozenge.Tiling
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Checks: tilings are perfect matchings

* `R = ∅`: the empty tiling is the only tiling, and it corresponds to the empty perfect matching
  of the empty graph, which is its only perfect matching.
* `R = {W(0)}`: neither side of `tilingSubgraph_bijOn` has an element: a single face has no tiling
  (both faces of an edge of a tiling lie in the region), and a graph with one vertex has no
  perfect matching.
* The unit hexagon `R₆`: it has two tilings, `T_a` and `T_b`, and its dual graph
  `SimpleGraph.induce R₆ hexGraph` is a 6-cycle with exactly two perfect matchings, the images of
  `T_a` and `T_b`.
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

/-! ### The unit hexagon -/

open LozengeTiling in
/-- The faces of the unit hexagon in cyclic order round `0`: `W(0)`, `B(0)`, `W(−e₁)`, `B(−e₃)`,
`W(−e₃)`, `B(−e₂)`. -/
def hexagonFace : Fin 6 → TriFace :=
  ![⟨(0, 0), true⟩, ⟨(0, 0), false⟩, ⟨(-1, 0), true⟩, ⟨(-1, -1), false⟩, ⟨(-1, -1), true⟩,
    ⟨(0, -1), false⟩]

open LozengeTiling in
/-- Each `hexagonFace i` is a face of the unit hexagon. -/
theorem hexagonFace_mem (i : Fin 6) : hexagonFace i ∈ hexagon := by
  fin_cases i <;> simp [hexagonFace, vertexFaces_def]

/-- The six faces `hexagonFace i` are distinct. -/
theorem hexagonFace_injective : Function.Injective hexagonFace := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hexagonFace]

open LozengeTiling in
/-- Every face of the unit hexagon is some `hexagonFace i`. -/
theorem exists_hexagonFace_eq {f : TriFace} (hf : f ∈ hexagon) : ∃ i, hexagonFace i = f := by
  simp only [hexagon, vertexFaces_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩, ⟨1, rfl⟩, ⟨5, rfl⟩, ⟨3, rfl⟩]

open LozengeTiling in
/-- **The dual graph of the unit hexagon is a 6-cycle.** -/
theorem nonempty_cycleGraph_iso_induce_hexagon :
    Nonempty (SimpleGraph.cycleGraph 6 ≃g SimpleGraph.induce hexagon hexGraph) := by
  refine ⟨⟨Equiv.ofBijective (fun i => ⟨hexagonFace i, hexagonFace_mem i⟩)
    ⟨fun i j h => hexagonFace_injective (congrArg Subtype.val h), fun f => ?_⟩, ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_hexagonFace_eq f.property
    exact ⟨i, Subtype.ext hi⟩
  · intro i j
    change hexGraph.Adj (hexagonFace i) (hexagonFace j) ↔ (SimpleGraph.cycleGraph 6).Adj i j
    rw [← SimpleGraph.mem_neighborSet, SimpleGraph.cycleGraph_adj]
    fin_cases i <;> fin_cases j <;>
      simp +decide [hexagonFace, hexGraph_neighborSet_mk_true, hexGraph_neighborSet_mk_false,
        -SimpleGraph.mem_neighborSet]

open LozengeTiling in
/-- The tilings of the unit hexagon are `T_a` and `T_b`. -/
theorem setOf_isTiling_hexagon : {M | IsTiling hexagon M} = {tilingA, tilingB} :=
  Set.ext fun _ => isTiling_hexagon_iff

open LozengeTiling in
/-- The perfect matchings of the dual graph of the unit hexagon are the images of `T_a` and
`T_b`. -/
theorem setOf_isPerfectMatching_hexagon :
    {P : (SimpleGraph.induce hexagon hexGraph).Subgraph | P.IsPerfectMatching} =
      {tilingSubgraph hexagon tilingA, tilingSubgraph hexagon tilingB} := by
  rw [← (tilingSubgraph_bijOn hexagon).image_eq, setOf_isTiling_hexagon, Set.image_pair]

open LozengeTiling in
/-- **The dual graph of the unit hexagon has exactly two perfect matchings.** -/
theorem ncard_setOf_isPerfectMatching_hexagon :
    {P : (SimpleGraph.induce hexagon hexGraph).Subgraph | P.IsPerfectMatching}.ncard = 2 := by
  rw [setOf_isPerfectMatching_hexagon, Set.ncard_pair]
  exact fun h => tilingA_ne_tilingB ((tilingSubgraph_bijOn hexagon).injOn
    (by simp [setOf_isTiling_hexagon]) (by simp [setOf_isTiling_hexagon]) h)

end TauCeti.Examples.LozengePerfectMatchingChecks
