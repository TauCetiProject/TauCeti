/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Graph
public import TauCeti.Combinatorics.Hypergraph.Triadic.SparseCounting
public import TauCeti.Combinatorics.Regularity.Graph.InducedCount
import TauCeti.Order.Partition.Pi
import Mathlib.Tactic.Linarith

/-!
# The triadic complex of a graph

A triadic complex carries a lower skeleton (vertex cells and a coloring of the distinct pairs) and
selected polyads above it. Its two-dimensional shadow is the lower skeleton. This file compares
that shadow with the graph regularity API, by viewing a finite simple graph `G` with vertex cells
`P` as the triadic complex `G.toTriadicComplex3 P`: its two pair colors are `1` on the edges of `G`
and `0` on the nonedges, and it selects every polyad.

* Its selected polyads decompose the injective triples, and its vertex cells are controlled at
  `t₀` exactly when `P` is an equipartition with at least `t₀` parts.
* If its lower skeleton is regular for a schedule `F`, then `P` is a uniform partition of `G`
  in the sense of Szemerédi's regularity lemma at every parameter above `F (#P.parts + 2)`
  (`TauCeti.PairSkeleton3.LowerSkeletonRegular.isUniform`).
* A graph `J` on the vertices of a pattern defines a route `φ.graphRoute J` over every placement
  `φ`, coloring each canonical pair by adjacency in `J`. Summed over all placements, the maps
  realizing these routes are the labelled induced copies of `J` in `G`
  (`SimpleGraph.sum_lowerRouteCountAt_graphRoute`), and the lower-route predictions of the
  transversal placements add up to the coarse induced-count prediction
  `J.coarseInducedGraphEstimate G P` of the graph counting lemma
  (`SimpleGraph.sum_expectedLowerRouteCountAt_graphRoute`).
* Consequently controlled vertex cells and a regular lower skeleton give the induced counting
  lemma for three-vertex graphs
  (`SimpleGraph.abs_inducedGraphCount3_sub_coarseInducedGraphEstimate_le_of_lowerSkeletonRegular`).

## Main definitions

* `SimpleGraph.toTriadicComplex3`: the triadic complex of a graph over given vertex cells.
* `TauCeti.PatternPlacement3.graphRoute`: the route of a graph on the pattern vertices.

## Main results

* `SimpleGraph.vertexCellsControlled_toTriadicComplex3_iff`: controlled cells are equipartitions.
* `TauCeti.PairSkeleton3.LowerSkeletonRegular.isUniform`: a regular lower skeleton gives a
  uniform partition.
* `TauCeti.mem_lowerRouteMaps_graphRoute`: the maps realizing the route of `J` are the induced
  copies of `J` in the assigned cells.
* `SimpleGraph.sum_lowerRouteCountAt_graphRoute`: the lower-route counts add up to the number of
  labelled induced copies of `J` in `G`.
* `SimpleGraph.sum_expectedLowerRouteCountAt_graphRoute`: the transversal lower-route predictions
  add up to the coarse induced-count prediction.
* `SimpleGraph.abs_inducedGraphCount3_sub_coarseInducedGraphEstimate_le_of_lowerSkeletonRegular`:
  induced counting of three-vertex graphs from controlled cells and a regular lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (the graph counting lemma).
-/

public section

open Finset Function TauCeti

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finpartition (univ : Finset V))

/-! ### The complex -/

/-- The triadic complex of a graph `G` over the vertex cells `P`: the pair palette `Fin 2` colors
the edges of `G` by `1` and its nonedges by `0`, and every polyad is selected. -/
-- This is reducible so that the palette `Fin (G.toTriadicComplex3 P).pairColorCount` reduces to
-- `Fin 2` and the vertex cells to `P`, which the statements below need in order to name the colors
-- and to compare placements with maps to the parts of `P`.
noncomputable abbrev toTriadicComplex3 : TriadicComplex3 V where
  pairColorCount := 2
  skeleton := ⟨P, G.toPairColorSystem.relabel finTwoEquiv.symm⟩
  polyads := univ

@[simp]
theorem toTriadicComplex3_pairColorCount : (G.toTriadicComplex3 P).pairColorCount = 2 :=
  (rfl)

@[simp]
theorem toTriadicComplex3_vertexPart : (G.toTriadicComplex3 P).skeleton.vertexPart = P :=
  (rfl)

@[simp]
theorem toTriadicComplex3_polyads : (G.toTriadicComplex3 P).polyads = univ :=
  (rfl)

/-- A distinct pair has the color of `b : Bool` exactly when its adjacency in `G` is `b`. -/
theorem colorOfPair_toTriadicComplex3_eq_some_iff (u v : V) (b : Bool) :
    (G.toTriadicComplex3 P).skeleton.pairColors.colorOfPair u v = some (finTwoEquiv.symm b) ↔
      u ≠ v ∧ (G.Adj u v ↔ b = true) := by
  rw [PairColorSystem.colorOfPair_relabel, Option.map_eq_some_iff]
  simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
    PairColorSystem.colorOfPair_eq_some_iff, toPairColorSystem_color]
  cases b <;> simp

/-- Between distinct cells, the color of `decide e` has the pattern density of `G`: the edge
density if `e` holds and the nonedge density otherwise. -/
theorem pairColorDensity_toTriadicComplex3 {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hAB : A ≠ B) (e : Prop) [Decidable e] :
    (pairColorDensity (G.toTriadicComplex3 P).skeleton.pairColors (finTwoEquiv.symm (decide e))
      A B : ℝ) = G.patternDensity e A B := by
  rw [pairColorDensity_relabel, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact G.pairColorDensity_toPairColorSystem_decide e (P.nonempty_of_mem_parts hA)
    (P.nonempty_of_mem_parts hB) (P.disjoint hA hB hAB)

/-- The polyads of the triadic complex of a graph decompose the injective triples. -/
theorem isPolyadDecomposition_toTriadicComplex3 :
    (G.toTriadicComplex3 P).IsPolyadDecomposition :=
  TriadicComplex3.isPolyadDecomposition_of_polyads_eq_univ _ (toTriadicComplex3_polyads G P)

/-- The vertex cells of the triadic complex of a graph are controlled at `t₀` exactly when they
form an equipartition with at least `t₀` parts. -/
@[simp]
theorem vertexCellsControlled_toTriadicComplex3_iff {t₀ : ℕ} :
    (G.toTriadicComplex3 P).VertexCellsControlled t₀ ↔ P.IsEquipartition ∧ t₀ ≤ #P.parts := by
  rw [TriadicComplex3.vertexCellsControlled_iff, toTriadicComplex3_vertexPart]

end SimpleGraph

namespace TauCeti.PairSkeleton3

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)} {F : ℕ → ℝ} {ε : ℝ}

/-- If the lower skeleton of the triadic complex of a graph `G` with vertex cells `P` is regular
for the schedule `F`, then `P` is a uniform partition of `G` at every parameter larger than
`F (#P.parts + 2)`. -/
theorem LowerSkeletonRegular.isUniform
    (h : (G.toTriadicComplex3 P).skeleton.LowerSkeletonRegular F) (hε : F (#P.parts + 2) < ε) :
    P.IsUniform G ε := by
  -- The lower skeleton of the complex is the skeleton of `G` with the palette relabelled along
  -- `Bool ≃ Fin 2`.
  have heq : (⟨P, G.toPairColorSystem⟩ : PairSkeleton3 Bool V).relabel finTwoEquiv.symm =
      ⟨P, G.toPairColorSystem.relabel finTwoEquiv.symm⟩ :=
    congrArg₂ PairSkeleton3.mk (relabel_vertexPart _) (relabel_pairColors _)
  have h' : ((⟨P, G.toPairColorSystem⟩ : PairSkeleton3 Bool V).relabel
      finTwoEquiv.symm).LowerSkeletonRegular F := heq ▸ h
  rw [lowerSkeletonRegular_relabel_iff, lowerSkeletonRegular_iff, Fintype.card_bool] at h'
  exact h'.isUniform hε

end TauCeti.PairSkeleton3

/-! ### Routes of a graph on the pattern vertices -/

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)} {κ : Type*} {F : FiniteColored3Pattern κ}

/-- The route over a placement `φ` into the triadic complex of `G` of a graph `J` on the pattern
vertices: each canonical pattern pair `i < j` gets the edge color if `J.Adj i j` and the nonedge
color otherwise. -/
def PatternPlacement3.graphRoute (φ : PatternPlacement3 (G.toTriadicComplex3 P) F)
    (J : SimpleGraph (Fin F.k)) [DecidableRel J.Adj] : PairColorPlacement3 φ where
  pairColor p := finTwoEquiv.symm (decide (J.Adj p.val.1 p.val.2))
  ofData_mem _ _ _ _ _ := mem_univ _

variable (J : SimpleGraph (Fin F.k)) [DecidableRel J.Adj]

@[simp]
theorem PatternPlacement3.graphRoute_pairColor (φ : PatternPlacement3 (G.toTriadicComplex3 P) F)
    (p : {p : Fin F.k × Fin F.k // p.1 < p.2}) :
    (φ.graphRoute J).pairColor p = finTwoEquiv.symm (decide (J.Adj p.val.1 p.val.2)) :=
  (rfl)

/-- An injective map realizes the route of `J` exactly when it carries adjacency in `J` to
adjacency in `G` in both directions. -/
private theorem forall_colorOfPair_graphRoute_iff
    {φ : PatternPlacement3 (G.toTriadicComplex3 P) F} {g : Fin F.k → V} (hg : Injective g) :
    (∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        (G.toTriadicComplex3 P).skeleton.pairColors.colorOfPair (g p.val.1) (g p.val.2) =
          some ((φ.graphRoute J).pairColor p)) ↔
      ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j) := by
  -- The color of the route on a canonical pair is the color of `decide (J.Adj i j)`.
  have key : ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      (G.toTriadicComplex3 P).skeleton.pairColors.colorOfPair (g p.val.1) (g p.val.2) =
          some ((φ.graphRoute J).pairColor p) ↔
        (J.Adj p.val.1 p.val.2 ↔ G.Adj (g p.val.1) (g p.val.2)) := fun p ↦
    (G.colorOfPair_toTriadicComplex3_eq_some_iff P _ _ (decide (J.Adj p.val.1 p.val.2))).trans <| by
      rw [decide_eq_true_eq]
      exact ⟨fun h ↦ h.2.symm, fun h ↦ ⟨hg.ne p.property.ne, h.symm⟩⟩
  rw [forall_congr' key]
  simp only [Subtype.forall, Prod.forall]
  refine ⟨fun h i j ↦ ?_, fun h i j _ ↦ h i j⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h i j hij
  · simp
  · rw [J.adj_comm, G.adj_comm]
    exact h j i hij

/-- The maps realizing the route of `J` over a placement are the maps into its cells that carry
adjacency in `J` to adjacency in `G` in both directions, that is, the labelled induced copies of
`J` in `G` with vertices in the assigned cells. -/
theorem mem_lowerRouteMaps_graphRoute {φ : PatternPlacement3 (G.toTriadicComplex3 P) F}
    {g : Fin F.k → V} :
    g ∈ lowerRouteMaps φ (φ.graphRoute J) ↔
      Injective g ∧ (∀ i, g i ∈ φ.vertexCell i) ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j) := by
  rw [mem_lowerRouteMaps]
  exact ⟨fun ⟨hg, hcell, h⟩ ↦ ⟨hg, hcell, (forall_colorOfPair_graphRoute_iff J hg).1 h⟩,
    fun ⟨hg, hcell, h⟩ ↦ ⟨hg, hcell, (forall_colorOfPair_graphRoute_iff J hg).2 h⟩⟩

/-- At a transversal placement into the triadic complex of `G`, the lower-route prediction of the
route of `J` is the cell-size product times, for each canonical pair `i < j`, the edge density
between the assigned cells if `J.Adj i j` and the nonedge density otherwise. -/
theorem expectedLowerRouteCountAt_graphRoute {φ : PatternPlacement3 (G.toTriadicComplex3 P) F}
    (hφ : φ.Transversal) :
    expectedLowerRouteCountAt φ (φ.graphRoute J) =
      (∏ i, (#(φ.vertexCell i) : ℝ)) * ∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        G.patternDensity (J.Adj p.val.1 p.val.2) (φ.vertexCell p.val.1) (φ.vertexCell p.val.2) := by
  rw [expectedLowerRouteCountAt_def]
  congr 1
  refine prod_congr rfl fun p _ ↦ ?_
  exact G.pairColorDensity_toTriadicComplex3 P (φ.vertexCell_mem _) (φ.vertexCell_mem _)
    ((φ.transversal_iff.1 hφ).ne p.property.ne) _

end TauCeti

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)}

section Routes

variable {κ : Type*} {F : FiniteColored3Pattern κ} (J : SimpleGraph (Fin F.k)) [DecidableRel J.Adj]

/-- **Lower-route counts of a graph.** Summed over all placements into the triadic complex of `G`,
the numbers of maps realizing the routes of `J` count the labelled induced copies of `J` in `G`:
the injective maps carrying adjacency in `J` to adjacency in `G` in both directions. For three
vertices this is `SimpleGraph.inducedGraphCount3`. -/
theorem sum_lowerRouteCountAt_graphRoute :
    ∑ φ : PatternPlacement3 (G.toTriadicComplex3 P) F, lowerRouteCountAt φ (φ.graphRoute J) =
      #{g : Fin F.k → V | Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} := by
  have h := P.sum_card_filter_piFinset_parts (ι := Fin F.k)
    fun g ↦ Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Fintype.sum_equiv PatternPlacement3.equivFun _ _ fun φ ↦ ?_
  rw [lowerRouteCountAt_def]
  congr 1
  ext g
  rw [mem_lowerRouteMaps_graphRoute, mem_filter, Fintype.mem_piFinset]
  simp only [PatternPlacement3.coe_equivFun_apply]
  tauto

open Classical in
/-- **Lower-route predictions of a graph.** Summed over the transversal placements into the
triadic complex of `G`, the lower-route predictions of the routes of `J` give the coarse
induced-count prediction `J.coarseInducedGraphEstimate G P`. -/
theorem sum_expectedLowerRouteCountAt_graphRoute :
    ∑ φ : PatternPlacement3 (G.toTriadicComplex3 P) F with φ.Transversal,
        expectedLowerRouteCountAt φ (φ.graphRoute J) = J.coarseInducedGraphEstimate G P := by
  rw [coarseInducedGraphEstimate_def]
  refine sum_equiv PatternPlacement3.equivFun (fun φ ↦ ?_) fun φ hφ ↦ ?_
  · simp only [mem_filter, mem_univ, true_and]
    exact (PatternPlacement3.injective_equivFun_iff φ).symm
  · rw [expectedLowerRouteCountAt_graphRoute J (mem_filter.1 hφ).2]
    simp only [PatternPlacement3.coe_equivFun_apply]

end Routes

/-! ### Induced counting from the lower skeleton -/

/-- **Induced counting from a regular lower skeleton.** Let `J` be a graph on three vertices. If
the triadic complex of `G` with vertex cells `P` has vertex cells controlled at `t₀ > 0` and a
lower skeleton regular for the schedule `F`, then for every `τ > F (#P.parts + 2)` the labelled
induced copies of `J` in `G` differ from the coarse prediction `J.coarseInducedGraphEstimate G P`
by at most `15 τ |V| ^ 3 + 3 (|V| / t₀ + 1) |V| ^ 2`. -/
theorem abs_inducedGraphCount3_sub_coarseInducedGraphEstimate_le_of_lowerSkeletonRegular
    (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj] {F : ℕ → ℝ} {t₀ : ℕ} (ht₀ : 0 < t₀)
    (hcells : (G.toTriadicComplex3 P).VertexCellsControlled t₀)
    (hreg : (G.toTriadicComplex3 P).skeleton.LowerSkeletonRegular F) {τ : ℝ}
    (hτ : F (#P.parts + 2) < τ) :
    |(J.inducedGraphCount3 G : ℝ) - J.coarseInducedGraphEstimate G P| ≤
      15 * τ * Fintype.card V ^ 3 +
        3 * ((Fintype.card V / t₀ + 1 : ℕ) : ℝ) * Fintype.card V ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · -- On the empty host there are no cells and no copies.
    have : IsEmpty P.parts := ⟨fun A ↦ isEmptyElim (P.nonempty_of_mem_parts A.property).choose⟩
    simp [inducedGraphCount3_def, coarseInducedGraphEstimate_def, Fintype.card_eq_zero]
  have hτ₀ : 0 < τ := by
    have h₀ := (PairSkeleton3.lowerSkeletonRegular_iff.1 hreg).nonneg
    simp only [Fintype.card_fin] at h₀
    exact h₀.trans_lt hτ
  have hP := (G.vertexCellsControlled_toTriadicComplex3_iff P).1 hcells
  have hm : ∀ A ∈ P.parts, #A ≤ Fintype.card V / t₀ + 1 := fun _ hA ↦ hcells.card_le ht₀ hA
  have hu := hreg.isUniform hτ
  have h₁ := J.inducedGraphCount3_le_coarseInducedGraphEstimate_add G hP.1 hτ₀ hu hm
  have h₂ := J.coarseInducedGraphEstimate_sub_le_inducedGraphCount3 G hP.1 hτ₀ hu
  have h₃ : 0 ≤ 3 * ((Fintype.card V / t₀ + 1 : ℕ) : ℝ) * Fintype.card V ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

end SimpleGraph
