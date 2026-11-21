/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Graph
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
public import TauCeti.Combinatorics.Regularity.Graph.InducedCount

/-!
# Induced graph counting on the two-dimensional shadow of a triadic complex

Select a reversal-invariant set of lower pair colors to obtain a simple graph. If the lower
skeleton is regular and the vertex cells are controlled, the induced three-vertex graph count
is estimated by the coarse graph prediction on those cells. Neither the selected polyads nor
the colors of triples enter this graph estimate.
-/

public section

open Finset

namespace TauCeti.TriadicComplex3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced count of any three-vertex graph in a color-selected shadow lies between the
coarse prediction minus the graph uniformity error and the prediction plus that error and the
contribution from repeated cells. The graph tolerance must exceed the scheduled pair-color
error times the number of selected colors. -/
theorem inducedGraphCount3_colorGraph_bounds (C : TriadicComplex3 V) (J : SimpleGraph (Fin 3))
    [DecidableRel J.Adj] {F : ℕ → ℝ} {t₀ : ℕ} {τ : ℝ}
    (hlower : C.skeleton.LowerSkeletonRegular F) (hcells : C.VertexCellsControlled t₀)
    (ht₀ : 0 < t₀) (hτ : 0 < τ) (K : Finset (Fin C.pairColorCount))
    (hK : ∀ c ∈ K, C.skeleton.pairColors.rev c ∈ K)
    (hbound : (#K : ℝ) * F (#C.skeleton.vertexPart.parts + C.pairColorCount) < τ) :
    let G := C.skeleton.pairColors.colorGraph K hK
    let Q := C.skeleton.vertexPart
    let n := Fintype.card V
    J.coarseInducedGraphEstimate G Q - 15 * τ * n ^ 3 ≤ J.inducedGraphCount3 G ∧
      (J.inducedGraphCount3 G : ℝ) ≤ J.coarseInducedGraphEstimate G Q +
        15 * τ * n ^ 3 + 3 * (↑(n / t₀ + 1) : ℝ) * n ^ 2 := by
  dsimp only
  have hU := hlower.isUniform_colorGraph (K := K) (hK := hK) (by simpa using hbound)
  have heq := (vertexCellsControlled_iff.1 hcells).1
  exact ⟨J.coarseInducedGraphEstimate_sub_le_inducedGraphCount3 _ heq hτ hU,
    J.inducedGraphCount3_le_coarseInducedGraphEstimate_add _ heq hτ hU
      (fun _ hA ↦ hcells.card_le ht₀ hA)⟩

end TauCeti.TriadicComplex3
