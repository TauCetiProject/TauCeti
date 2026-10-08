/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Product
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.Data.Finsupp.OrderedCoupling

/-!
# Coordinate projections of a realized ordered product

The staircase triangulation of a product has a canonical continuous map to the product of the
factor realizations, obtained by adding barycentric weights along each coordinate fibre.
This map is injective: on each staircase the nonnegative weights have chain support, so they
are uniquely determined by their marginals. For finite vertex types it is a closed embedding.

Surjectivity, and hence the identification with the entire product, requires existence of a
chain-supported coupling with prescribed marginals and is not asserted here.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (the staircase triangulation of products).
-/

public section

noncomputable section

namespace AbstractSimplicialComplex

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- The coordinate projections of the staircase triangulation, realized continuously.
Each coordinate adds barycentric weights over a fibre of the corresponding vertex projection. -/
def orderedProdRealizationMap (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) :
    C(Realization (K.orderedProd L), Realization K × Realization L) :=
  let fst := PreAbstractSimplicialComplex.SimplicialMap.orderedProdFst
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex
  let snd := PreAbstractSimplicialComplex.SimplicialMap.orderedProdSnd
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex
  -- Transport only the face proofs so that the vertex functions retain their computation rules.
  let fst' : PreAbstractSimplicialComplex.SimplicialMap
      (K.orderedProd L).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex :=
    ⟨fst, fun _ h ↦ fst.map_face
      (by simpa only [orderedProd_toPreAbstractSimplicialComplex] using h)⟩
  let snd' : PreAbstractSimplicialComplex.SimplicialMap
      (K.orderedProd L).toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex :=
    ⟨snd, fun _ h ↦ snd.map_face
      (by simpa only [orderedProd_toPreAbstractSimplicialComplex] using h)⟩
  fst'.realizationMap.prodMk snd'.realizationMap

/-- The first marginal of the barycentric coordinates. -/
@[simp]
theorem orderedProdRealizationMap_fst_val (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) (x : Realization (K.orderedProd L)) :
    (K.orderedProdRealizationMap L x).1.1 = Finsupp.mapDomain Prod.fst x.1 := by
  simp [orderedProdRealizationMap]

/-- The second marginal of the barycentric coordinates. -/
@[simp]
theorem orderedProdRealizationMap_snd_val (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) (x : Realization (K.orderedProd L)) :
    (K.orderedProdRealizationMap L x).2.1 = Finsupp.mapDomain Prod.snd x.1 := by
  simp [orderedProdRealizationMap]

/-- A product vertex projects to its two factor vertices. -/
@[simp]
theorem orderedProdRealizationMap_vertex (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) (a : α) (b : β) :
    K.orderedProdRealizationMap L (vertex (K.orderedProd L) (a, b)) =
      (vertex K a, vertex L b) := by
  simp [orderedProdRealizationMap]

/-- The coordinate projections uniquely determine a point of the staircase triangulation. -/
theorem orderedProdRealizationMap_injective (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) : Function.Injective (K.orderedProdRealizationMap L) := by
  intro x y h
  apply Subtype.ext
  apply Finsupp.eq_of_mapDomain_eq_of_isChain_support x.1 y.1
    (Realization.nonneg _ x) (Realization.nonneg _ y)
    (isChain_of_mem_orderedProd (support_mem _ x))
    (isChain_of_mem_orderedProd (support_mem _ y))
  · simpa only [orderedProdRealizationMap_fst_val] using congrArg (fun p => p.1.1) h
  · simpa only [orderedProdRealizationMap_snd_val] using congrArg (fun p => p.2.1) h

/-- With finite vertex types the projection identifies the realized staircase triangulation
with a closed subspace of the product of realizations. -/
theorem isClosedEmbedding_orderedProdRealizationMap [Finite α] [Finite β]
    (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β) :
    Topology.IsClosedEmbedding (K.orderedProdRealizationMap L) := by
  exact (K.orderedProdRealizationMap L).continuous.isClosedEmbedding
    (K.orderedProdRealizationMap_injective L)

end AbstractSimplicialComplex
