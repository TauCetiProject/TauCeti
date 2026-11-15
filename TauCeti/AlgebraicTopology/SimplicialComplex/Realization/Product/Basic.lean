/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Product
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Coordinate projections of a realized ordered product

The staircase triangulation has a continuous map to the product of its factor realizations.
Its coordinates add barycentric weights along the corresponding vertex projection.
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
  let fst' : PreAbstractSimplicialComplex.SimplicialMap
      (K.orderedProd L).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex :=
    (PreAbstractSimplicialComplex.SimplicialMap.orderedProdFst
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex).domainRestrict
        (by rw [orderedProd_toPreAbstractSimplicialComplex])
  let snd' : PreAbstractSimplicialComplex.SimplicialMap
      (K.orderedProd L).toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex :=
    (PreAbstractSimplicialComplex.SimplicialMap.orderedProdSnd
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex).domainRestrict
        (by rw [orderedProd_toPreAbstractSimplicialComplex])
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

end AbstractSimplicialComplex
