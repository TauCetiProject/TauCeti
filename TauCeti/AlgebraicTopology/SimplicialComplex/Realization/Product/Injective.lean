/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Product.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.Data.Finsupp.OrderedCoupling.Uniqueness

/-!
# Coordinate projections of a realized ordered product

The staircase triangulation of a product has a canonical continuous map to the product of the
factor realizations, obtained by adding barycentric weights along each coordinate fibre.
This map is injective: on each staircase the nonnegative weights have chain support, so they
are uniquely determined by their marginals. If the product has finitely many faces, it is a
closed embedding.

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

/-- With finitely many faces the projection identifies the realized staircase triangulation
with a closed subspace of the product of realizations. -/
theorem isClosedEmbedding_orderedProdRealizationMap
    (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β)
    (hprod : (K.orderedProd L).faces.Finite) :
    Topology.IsClosedEmbedding (K.orderedProdRealizationMap L) := by
  have : CompactSpace (Realization (K.orderedProd L)) :=
    (K.orderedProd L).compactSpace_realization_of_finite_faces hprod
  exact (K.orderedProdRealizationMap L).continuous.isClosedEmbedding
    (K.orderedProdRealizationMap_injective L)

end AbstractSimplicialComplex
