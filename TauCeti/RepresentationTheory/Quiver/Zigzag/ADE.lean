/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Center
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Dimension

/-!
# Zigzag algebras of `D₄`, `E₈`, and affine `E₈`

This file constructs the three ADE graphs used as named zigzag examples from Tau Ceti's standard
Cartan-matrix and affine-diagram APIs. The finite graphs are the diagrams of the Bourbaki-numbered
Cartan matrices, while affine `E₈` is the already constructed tree `T_{2,3,6}`. Their tree
structures determine their edge counts, and the general dimension and centre theorems then give

```text
                     D₄    E₈    affine E₈
dim Z(G)             14    30        34
dim centre Z(G)       5     9        10.
```

The definitions retain the established node labels: finite nodes use the indices of
`TauCeti.DynkinType.cartanMatrix`, and the affine nodes use
`TauCeti.AffineDynkinType.graph`.

## Main definitions

* `TauCeti.zigzagD4Graph`, `TauCeti.zigzagE8Graph`, and `TauCeti.zigzagAffineE8Graph`: the three
  named graphs.

## Main results

* `TauCeti.isTree_zigzagD4Graph`, `TauCeti.isTree_zigzagE8Graph`, and
  `TauCeti.isTree_zigzagAffineE8Graph`: the graphs are trees.
* `TauCeti.finrank_zigzagAlgebra_D4`, `TauCeti.finrank_zigzagAlgebra_E8`, and
  `TauCeti.finrank_zigzagAlgebra_affineE8`: the three zigzag dimensions.
* `TauCeti.finrank_center_zigzagAlgebra_D4`, `TauCeti.finrank_center_zigzagAlgebra_E8`, and
  `TauCeti.finrank_center_zigzagAlgebra_affineE8`: the three centre dimensions.

## References

This file implements the named-example dimension and centre targets in
`TauCetiRoadmap/ZigzagPreprojective/README.md`, following the prototype graph presentations in
`TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`.

The zigzag conventions and invariant formulas follow Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2. The affine `E₈ = T_{2,3,6}` labelling follows Kac, *Infinite dimensional Lie
algebras*, Chapter 4.
-/

public section

namespace TauCeti

/-- The `D₄` graph, read from its Bourbaki-numbered standard Cartan matrix. -/
abbrev zigzagD4Graph : SimpleGraph (Fin 4) :=
  diagramGraph (DynkinType.D 4).cartanMatrix

/-- The `E₈` graph, read from its Bourbaki-numbered standard Cartan matrix. -/
abbrev zigzagE8Graph : SimpleGraph (Fin 8) :=
  diagramGraph DynkinType.E8.cartanMatrix

/-- The affine `E₈` graph `T_{2,3,6}`, with the affine-diagram numbering. -/
abbrev zigzagAffineE8Graph : SimpleGraph (Fin 9) :=
  AffineDynkinType.E8.graph

instance : DecidableRel zigzagD4Graph.Adj :=
  inferInstanceAs (DecidableRel (diagramGraph (DynkinType.D 4).cartanMatrix).Adj)

instance : DecidableRel zigzagE8Graph.Adj :=
  inferInstanceAs (DecidableRel (diagramGraph DynkinType.E8.cartanMatrix).Adj)

instance : DecidableRel zigzagAffineE8Graph.Adj :=
  AffineDynkinType.E8.instDecidableRelFinNodesAdjGraph

/-! ### Graph structure -/

/-- The `D₄` graph is connected. -/
theorem connected_zigzagD4Graph : zigzagD4Graph.Connected :=
  DynkinType.connected_diagramGraph_cartanMatrix (by simp)

/-- The `E₈` graph is connected. -/
theorem connected_zigzagE8Graph : zigzagE8Graph.Connected :=
  DynkinType.connected_diagramGraph_cartanMatrix (by simp)

/-- The affine `E₈` graph is connected. -/
theorem connected_zigzagAffineE8Graph : zigzagAffineE8Graph.Connected :=
  AffineDynkinType.graph_connected (by simp)

/-- The `D₄` graph is a tree. -/
theorem isTree_zigzagD4Graph : zigzagD4Graph.IsTree := by
  rw [zigzagD4Graph, DynkinType.cartanMatrix_D]
  have hconn : (diagramGraph (CartanMatrix.D 4)).Connected := by
    rw [← DynkinType.cartanMatrix_D]
    exact connected_zigzagD4Graph
  exact (isFiniteType_cartanMatrix_D 4).isTree_diagramGraph hconn

/-- The `E₈` graph is a tree. -/
theorem isTree_zigzagE8Graph : zigzagE8Graph.IsTree :=
  DynkinType.isFiniteType_cartanMatrix_E8.isTree_diagramGraph connected_zigzagE8Graph

/-- The affine `E₈` graph has eight edges. -/
@[simp]
theorem card_edgeFinset_zigzagAffineE8Graph : zigzagAffineE8Graph.edgeFinset.card = 8 := by
  have h := zigzagAffineE8Graph.two_mul_card_edgeFinset
  let edgePairs : List (ℕ × ℕ) :=
    [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)]
  have hfilter :
      (Finset.univ.filter fun x : Fin 9 × Fin 9 ↦
        AffineDynkinType.E8.graph.Adj x.1 x.2) =
      Finset.univ.filter fun x : Fin 9 × Fin 9 ↦
        (min (x.1 : ℕ) (x.2 : ℕ), max (x.1 : ℕ) (x.2 : ℕ)) ∈ edgePairs := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [edgePairs] using AffineDynkinType.graph_E8_adj x.1 x.2
  have hcard :
      (Finset.univ.filter fun x : Fin 9 × Fin 9 ↦
        (min (x.1 : ℕ) (x.2 : ℕ), max (x.1 : ℕ) (x.2 : ℕ)) ∈ edgePairs).card = 16 := by
    decide
  have h' : 2 * zigzagAffineE8Graph.edgeFinset.card =
      (Finset.univ.filter fun x : Fin 9 × Fin 9 ↦
        AffineDynkinType.E8.graph.Adj x.1 x.2).card := by
    simpa only [zigzagAffineE8Graph] using h
  rw [hfilter, hcard] at h'
  omega

/-- The affine `E₈ = T_{2,3,6}` graph is a tree. -/
theorem isTree_zigzagAffineE8Graph : zigzagAffineE8Graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨connected_zigzagAffineE8Graph, by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      card_edgeFinset_zigzagAffineE8Graph, Nat.card_fin]⟩

/-- The `D₄` graph has three edges. -/
@[simp]
theorem card_edgeFinset_zigzagD4Graph : zigzagD4Graph.edgeFinset.card = 3 := by
  have h := isTree_zigzagD4Graph.card_edgeFinset
  norm_num at h ⊢
  omega

/-- The `E₈` graph has seven edges. -/
@[simp]
theorem card_edgeFinset_zigzagE8Graph : zigzagE8Graph.edgeFinset.card = 7 := by
  have h := isTree_zigzagE8Graph.card_edgeFinset
  norm_num at h ⊢
  omega

/-! ### Zigzag dimensions -/

/-- The zigzag algebra of `D₄` has dimension `14`. -/
theorem finrank_zigzagAlgebra_D4 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (zigzagAlgebra k zigzagD4Graph) = 14 := by
  rw [finrank_zigzagAlgebra]
  norm_num

/-- The zigzag algebra of `E₈` has dimension `30`. -/
theorem finrank_zigzagAlgebra_E8 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (zigzagAlgebra k zigzagE8Graph) = 30 := by
  rw [finrank_zigzagAlgebra]
  norm_num

/-- The zigzag algebra of affine `E₈` has dimension `34`. -/
theorem finrank_zigzagAlgebra_affineE8 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (zigzagAlgebra k zigzagAffineE8Graph) = 34 := by
  rw [finrank_zigzagAlgebra]
  norm_num

/-! ### Centre dimensions -/

/-- The centre of the zigzag algebra of `D₄` has dimension `5`. -/
@[simp]
theorem finrank_center_zigzagAlgebra_D4 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (Subalgebra.center k (zigzagAlgebra k zigzagD4Graph)) = 5 := by
  rw [finrank_center_zigzagAlgebra_of_connected k zigzagD4Graph connected_zigzagD4Graph]
  norm_num

/-- The centre of the zigzag algebra of `E₈` has dimension `9`. -/
@[simp]
theorem finrank_center_zigzagAlgebra_E8 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (Subalgebra.center k (zigzagAlgebra k zigzagE8Graph)) = 9 := by
  rw [finrank_center_zigzagAlgebra_of_connected k zigzagE8Graph connected_zigzagE8Graph]
  norm_num

/-- The centre of the zigzag algebra of affine `E₈` has dimension `10`. -/
@[simp]
theorem finrank_center_zigzagAlgebra_affineE8 (k : Type*) [CommRing k] [Nontrivial k] :
    Module.finrank k (Subalgebra.center k (zigzagAlgebra k zigzagAffineE8Graph)) = 10 := by
  rw [finrank_center_zigzagAlgebra_of_connected k zigzagAffineE8Graph
    connected_zigzagAffineE8Graph]
  norm_num

end TauCeti
