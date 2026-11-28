/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.EdgeColoring
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.Graph.Union

/-!
# Examples of bipartite multigraph edge-colourings

These examples illustrate the extremal and boundary cases of Kőnig's edge-colouring theorem
using the matching-decomposition and regular-completion interfaces.

* Two vertices carrying `k` parallel edges form a `k`-regular bipartite multigraph. Its
  edges split into `k` perfect matchings and admit a proper colouring by `Fin k`, while the
  incidence bound shows that no smaller finite colour type suffices. For an arbitrary finite
  palette `C`, they are properly coloured, equivalently partitioned into `C`-indexed matchings,
  exactly when `k ≤ Nat.card C`; every colouring is injective on the parallel edge identities, and
  transporting along `Option.some` gives a colouring with an empty colour class.
* The three-vertex path is irregular, but its regular-completion theorem embeds it in a finite
  `2`-regular bipartite multigraph. A perfect-matching decomposition of the completion gives a
  two-colouring which restricts to the original path.
* An isolated vertex has no perfect matching. Nevertheless its edgeless graph, and the empty
  graph, have empty perfect-matching decompositions and proper edge-colourings by `Fin 0`. They are
  also coloured by the empty palette `Empty`, which colours no graph with an edge.

The examples retain actual edge identities, so the parallel-edge example is genuinely a
multigraph example rather than a statement about its simplification.
-/

public section

open Finset Function Set
open scoped Graph

namespace TauCeti.Examples.BipartiteEdgeColoring

/-! ## Parallel edges -/

section Parallel

variable (k : ℕ)

/-- The multigraph on `Bool` with `k` distinct parallel edges between its vertices. -/
abbrev parallelGraph : Graph Bool (Fin k) :=
  Graph.banana false true Set.univ

private abbrev parallelLeft : Finset V(parallelGraph k) :=
  {⟨false, by simp [parallelGraph]⟩}

private abbrev parallelRight : Finset V(parallelGraph k) :=
  {⟨true, by simp [parallelGraph]⟩}

private theorem parallel_bipartition :
    (parallelGraph k).IsBipartition (parallelLeft k) (parallelRight k) := by
  refine ⟨by simp [parallelLeft, parallelRight], ?_, ?_⟩
  · rintro ⟨x, hx⟩
    cases x <;> simp [parallelLeft, parallelRight]
  · intro e x y he
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    rcases he.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [parallelLeft, parallelRight]

private theorem parallel_regular : (parallelGraph k).IsRegularOfDegree k := by
  rw [Graph.isRegularOfDegree_iff_incidenceCount_eq]
  · intro x hx
    rcases x with ⟨false | true, hx⟩
    · simp [parallelGraph]
    · rw [parallelGraph, Graph.banana_comm false true]
      simp
  · exact fun _ _ ↦ Set.toFinite _

/-- A nonempty banana graph with `k` parallel edges has a decomposition into `k` perfect
matchings and a sharp proper edge-colouring by `Fin k`. -/
theorem parallel_edges_have_sharp_coloring :
    ∃ M : Fin k → Set E(parallelGraph k),
      (∀ i, (parallelGraph k).IsPerfectMatching (M i)) ∧
        Pairwise (Disjoint on M) ∧ ⋃ i, M i = Set.univ ∧
        Nonempty ((parallelGraph k).EdgeColoring (Fin k)) ∧
        ∀ (C : Type*) [Finite C], Nonempty ((parallelGraph k).EdgeColoring C) → k ≤ Nat.card C := by
  obtain ⟨M, hM, hdisj, hcover⟩ :=
    (parallel_bipartition k).exists_perfectMatching_decomposition (parallel_regular k)
  have := (parallel_bipartition k).loopless
  have hcolor : Nonempty ((parallelGraph k).EdgeColoring (Fin k)) :=
    Graph.nonempty_edgeColoring_iff_exists_matchings.2
      ⟨M, fun i ↦ (Graph.isPerfectMatching_def.mp (hM i)).1, hdisj, hcover⟩
  refine ⟨M, hM, hdisj, hcover, hcolor, ?_⟩
  intro C _ ⟨c⟩
  simpa [parallelGraph] using
    c.incidenceCount_le_card (x := false)

-- Proper colourings of the complete line graph preserve the parallel-edge identities.
example {C : Type*} (c : (parallelGraph k).EdgeColoring C) : Function.Injective c := by
  have htop : (parallelGraph k).lineGraph = ⊤ := by simp [parallelGraph]
  refine SimpleGraph.Hom.injective_of_top_hom (G' := (⊤ : SimpleGraph C)) ⟨c, ?_⟩
  intro e f hef
  exact c.map_adj (by simpa only [htop] using hef)

/-- The palette bound is sharp for `k` parallel edges: they are properly edge-coloured by a finite
palette `C` exactly when `k ≤ Nat.card C`. -/
theorem parallel_nonempty_edgeColoring_iff (C : Type*) [Finite C] :
    Nonempty ((parallelGraph k).EdgeColoring C) ↔ k ≤ Nat.card C := by
  rw [(parallel_bipartition k).nonempty_edgeColoring_iff_forall_incidenceCount_le]
  refine ⟨fun h ↦ ?_, fun h x hx ↦ ((parallel_regular k).incidenceCount_eq hx).trans_le h⟩
  simpa [(parallel_regular k).incidenceCount_eq (x := false) (by simp)] using
    h false (by simp)

-- The same sharp bound in the matching-partition form, with matchings indexed by a palette `C`.
example (C : Type*) [Finite C] :
    (∃ M : C → Set E(parallelGraph k), (∀ i, (parallelGraph k).IsMatching (M i)) ∧
      (Pairwise fun i j ↦ Disjoint (M i) (M j)) ∧ ⋃ i, M i = Set.univ) ↔ k ≤ Nat.card C := by
  rw [(parallel_bipartition k).exists_matching_partition_iff_forall_incidenceCount_le,
    ← (parallel_bipartition k).nonempty_edgeColoring_iff_forall_incidenceCount_le,
    parallel_nonempty_edgeColoring_iff]

-- With a palette of `k + 1` colours, one colour class of `k` parallel edges is empty.
example : ∃ c : (parallelGraph k).EdgeColoring (Option (Fin k)),
    c.colorClass none = ∅ := by
  let c₀ := ((parallel_nonempty_edgeColoring_iff k (Fin k)).2 (by simp)).some
  let c := (parallelGraph k).lineGraph.recolorOfEmbedding
    ⟨Option.some, Option.some_injective _⟩ c₀
  refine ⟨c, Set.eq_empty_of_forall_notMem fun e he ↦ ?_⟩
  have : c e = none := he
  simp [c] at this

end Parallel

/-! ## An irregular graph and its regular completion -/

private abbrev PathVertex := Fin 3
private abbrev PathEdge := Fin 2

private def pathLeftEdge : Graph PathVertex PathEdge :=
  Graph.banana 0 1 {0}

private def pathRightEdge : Graph PathVertex PathEdge :=
  Graph.banana 1 2 {1}

private theorem path_edgeSets_disjoint : Disjoint E(pathLeftEdge) E(pathRightEdge) := by
  simp [pathLeftEdge, pathRightEdge]

-- The three-vertex path `0 — 1 — 2`, with its two edges retaining distinct identities.
private def pathGraph : Graph PathVertex PathEdge :=
  (Graph.Compatible.of_disjoint_edgeSet path_edgeSets_disjoint).union

private abbrev pathZero : V(pathGraph) := ⟨0, by simp [pathGraph, pathLeftEdge]⟩
private abbrev pathOne : V(pathGraph) := ⟨1, by simp [pathGraph, pathLeftEdge]⟩
private abbrev pathTwo : V(pathGraph) := ⟨2, by simp [pathGraph, pathRightEdge]⟩

private abbrev pathLeft : Finset V(pathGraph) := {pathZero, pathTwo}
private abbrev pathRight : Finset V(pathGraph) := {pathOne}

private theorem path_bipartition : pathGraph.IsBipartition pathLeft pathRight := by
  refine ⟨by simp [pathLeft, pathRight], ?_, ?_⟩
  · rintro ⟨x, hx⟩
    fin_cases x <;> simp [pathLeft, pathRight, pathZero, pathOne, pathTwo]
  · intro e x y he
    have hleft (z : V(pathGraph)) : z ∈ pathLeft ↔ z.val = 0 ∨ z.val = 2 := by
      simp [pathLeft, pathZero, pathTwo, Subtype.ext_iff]
    have hright (z : V(pathGraph)) : z ∈ pathRight ↔ z.val = 1 := by
      simp [pathRight, pathOne, Subtype.ext_iff]
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [hleft, hright]
    fin_cases e <;> fin_cases x <;> fin_cases y <;>
      simp_all [pathGraph, pathLeftEdge, pathRightEdge]

private theorem path_incidenceCount_le_two (x : PathVertex) (_hx : x ∈ V(pathGraph)) :
    pathGraph.incidenceCount x ≤ 2 := by
  rw [Graph.incidenceCount_def]
  calc
    (pathGraph.incidenceSet x).ncard ≤ E(pathGraph).ncard :=
      Set.ncard_le_ncard (Graph.incidenceSet_subset_edgeSet x) (Set.toFinite _)
    _ ≤ (Set.univ : Set PathEdge).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = 2 := by simp

private theorem path_incidenceCounts :
    pathGraph.incidenceCount 0 = 1 ∧ pathGraph.incidenceCount 1 = 2 ∧
      pathGraph.incidenceCount 2 = 1 := by
  have hzero : pathGraph.incidenceSet 0 = {0} := by
    ext e
    fin_cases e <;> simp [pathGraph, pathLeftEdge, pathRightEdge]
  have hone : pathGraph.incidenceSet 1 = {0, 1} := by
    ext e
    fin_cases e <;> simp [pathGraph, pathLeftEdge, pathRightEdge]
  have htwo : pathGraph.incidenceSet 2 = {1} := by
    ext e
    fin_cases e <;> simp [pathGraph, pathLeftEdge, pathRightEdge]
  simp [Graph.incidenceCount_def, hzero, hone, htwo]

-- The irregular three-vertex path embeds in a finite `2`-regular bipartite multigraph. A
-- two-colouring obtained from the completion's perfect-matching decomposition restricts to a
-- proper two-colouring of the original edges.
example :
    ∃ (G' : Graph (PathVertex ⊕ ℕ) (PathEdge ⊕ ℕ)) (L' R' : Finset V(G'))
      (hC : pathGraph.IsRegularCompletion pathLeft pathRight 2 G' L' R')
      (c : G'.EdgeColoring (Fin 2)),
      pathGraph.incidenceCount 0 = 1 ∧ pathGraph.incidenceCount 1 = 2 ∧
        pathGraph.incidenceCount 2 = 1 ∧ Nonempty (pathGraph.EdgeColoring (Fin 2)) ∧
        ∀ e : E(pathGraph), hC.restrictEdgeColoring c e =
          c ⟨.inl e, (hC.inl_mem_edgeSet_iff e).2 e.property⟩ := by
  obtain ⟨G', L', R', hC⟩ := path_bipartition.exists_isRegularCompletion
    path_incidenceCount_le_two
  let _ : Finite E(G') := hC.finite_edgeSet
  obtain ⟨M, hM, hdisj, hcover⟩ :=
    hC.isBipartition.exists_perfectMatching_decomposition hC.isRegularOfDegree
  have := hC.isBipartition.loopless
  obtain ⟨c⟩ : Nonempty (G'.EdgeColoring (Fin 2)) :=
    Graph.nonempty_edgeColoring_iff_exists_matchings.2
      ⟨M, fun i ↦ (Graph.isPerfectMatching_def.mp (hM i)).1, hdisj, hcover⟩
  exact ⟨G', L', R', hC, c, path_incidenceCounts.1, path_incidenceCounts.2.1,
    path_incidenceCounts.2.2, ⟨hC.restrictEdgeColoring c⟩,
    fun e ↦ hC.restrictEdgeColoring_apply c e⟩

/-! ## The isolated-vertex boundary case -/

private abbrev isolatedGraph : Graph Unit Empty :=
  Graph.noEdge Set.univ Empty

private abbrev isolatedVertex : V(isolatedGraph) := ⟨(), Set.mem_univ ()⟩
private abbrev isolatedLeft : Finset V(isolatedGraph) := {isolatedVertex}
private abbrev isolatedRight : Finset V(isolatedGraph) := ∅

private theorem isolated_bipartition :
    isolatedGraph.IsBipartition isolatedLeft isolatedRight := by
  refine ⟨by simp, ?_, ?_⟩
  · intro x
    exact Or.inl (by simp [isolatedLeft, isolatedVertex, Subsingleton.elim x isolatedVertex])
  · intro e
    exact e.elim

private theorem isolated_regular : isolatedGraph.IsRegularOfDegree 0 := by
  simp [Graph.isRegularOfDegree_def, isolatedGraph]

private abbrev emptyGraph : Graph Empty Empty :=
  Graph.noEdge ∅ Empty

private abbrev emptyLeft : Finset V(emptyGraph) := ∅
private abbrev emptyRight : Finset V(emptyGraph) := ∅

private theorem empty_bipartition : emptyGraph.IsBipartition emptyLeft emptyRight := by
  refine ⟨Finset.disjoint_empty_left emptyRight, ?_, ?_⟩
  · intro x
    exact x.property.elim
  · intro e
    exact e.elim

private theorem empty_regular : emptyGraph.IsRegularOfDegree 0 := by
  simp [Graph.isRegularOfDegree_def, emptyGraph]

-- An isolated vertex has no perfect matching, but the edgeless graph has the empty
-- perfect-matching decomposition and a proper colouring by the empty colour type.
example :
    (¬ ∃ M : Set E(isolatedGraph), isolatedGraph.IsPerfectMatching M) ∧
      (∃ M : Fin 0 → Set E(isolatedGraph),
        (∀ i, isolatedGraph.IsPerfectMatching (M i)) ∧
          Pairwise (Disjoint on M) ∧ ⋃ i, M i = Set.univ) ∧
      Nonempty (isolatedGraph.EdgeColoring (Fin 0)) ∧
      (∃ M : Fin 0 → Set E(emptyGraph),
        (∀ i, emptyGraph.IsPerfectMatching (M i)) ∧
          Pairwise (Disjoint on M) ∧ ⋃ i, M i = Set.univ) ∧
      Nonempty (emptyGraph.EdgeColoring (Fin 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨M, hM⟩
    obtain ⟨e, -, -⟩ := (Graph.isPerfectMatching_def.mp hM).2 isolatedVertex
    exact e.val.elim
  · exact isolated_bipartition.exists_perfectMatching_decomposition isolated_regular
  · exact ⟨Graph.EdgeColoring.mk (fun e ↦ e.val.elim) fun e ↦ e.val.elim⟩
  · exact empty_bipartition.exists_perfectMatching_decomposition empty_regular
  · exact ⟨Graph.EdgeColoring.mk (fun e ↦ e.val.elim) fun e ↦ e.val.elim⟩

/-! ## The empty palette -/

-- Kőnig's theorem with the empty palette: the isolated vertex and the empty graph are coloured by
-- `Empty`, with an `Empty`-indexed matching partition, while `k + 1` parallel edges are not.
example (k : ℕ) :
    Nonempty (isolatedGraph.EdgeColoring Empty) ∧
      (∃ M : Empty → Set E(isolatedGraph), (∀ i, isolatedGraph.IsMatching (M i)) ∧
        (Pairwise fun i j ↦ Disjoint (M i) (M j)) ∧ ⋃ i, M i = Set.univ) ∧
      Nonempty (emptyGraph.EdgeColoring Empty) ∧
      IsEmpty ((parallelGraph (k + 1)).EdgeColoring Empty) := by
  have hiso : ∀ x ∈ V(isolatedGraph), isolatedGraph.incidenceCount x ≤ Nat.card Empty := by
    simp [Graph.incidenceCount_def, isolatedGraph]
  refine ⟨isolated_bipartition.nonempty_edgeColoring_iff_forall_incidenceCount_le.2 hiso,
    isolated_bipartition.exists_matching_partition_iff_forall_incidenceCount_le.2 hiso,
    empty_bipartition.nonempty_edgeColoring_iff_forall_incidenceCount_le.2 ?_, ?_⟩
  · simp [emptyGraph]
  · rw [← not_nonempty_iff, parallel_nonempty_edgeColoring_iff]
    simp

end TauCeti.Examples.BipartiteEdgeColoring
