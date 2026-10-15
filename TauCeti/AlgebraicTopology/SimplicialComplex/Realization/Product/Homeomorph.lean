/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Product.Injective
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Product.Existence

/-!
# Realizing finite ordered products

When the staircase product has finitely many faces, its realization is homeomorphic to the
product of the weak realizations of its factors. The homeomorphism is the canonical marginal
map on barycentric coordinates. Its inverse is the unique nonnegative, chain-supported
coupling of the two coordinate vectors.

Finiteness is imposed on the product's face collection, rather than on ambient vertex types.
It makes the realized product compact, so the already continuous, injective marginal map is a
closed embedding. Existence of staircase couplings supplies surjectivity. This identification
is used to realize simplicial cylinders as topological cylinders.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (triangulating products of polyhedra).
-/

public section

noncomputable section

namespace AbstractSimplicialComplex

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
  (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β)
  (hprod : (K.orderedProd L).faces.Finite)

/-- The canonical homeomorphism from a finite realized staircase product to the product of
its factor realizations. In particular, this applies when both factors have finitely many faces. -/
def orderedProdRealizationHomeomorph :
    Realization (K.orderedProd L) ≃ₜ Realization K × Realization L :=
  (K.isClosedEmbedding_orderedProdRealizationMap L hprod).toIsEmbedding.toHomeomorphOfSurjective (by
      intro p
      obtain ⟨z, hz₁, hz₂⟩ := K.exists_realization_orderedProd L p.1 p.2
      refine ⟨z, Prod.ext ?_ ?_⟩
      · apply Subtype.ext
        simpa only [orderedProdRealizationMap_fst_val,
          PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
          PreAbstractSimplicialComplex.SimplicialMap.coe_domainRestrict,
          PreAbstractSimplicialComplex.SimplicialMap.coe_orderedProdFst]
          using congrArg Subtype.val hz₁
      · apply Subtype.ext
        simpa only [orderedProdRealizationMap_snd_val,
          PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
          PreAbstractSimplicialComplex.SimplicialMap.coe_domainRestrict,
          PreAbstractSimplicialComplex.SimplicialMap.coe_orderedProdSnd]
          using congrArg Subtype.val hz₂)

/-- The homeomorphism uses the existing continuous marginal map. -/
@[simp]
theorem orderedProdRealizationHomeomorph_apply (x : Realization (K.orderedProd L)) :
    K.orderedProdRealizationHomeomorph L hprod x = K.orderedProdRealizationMap L x :=
  (rfl)

/-- The inverse's first barycentric marginal is the first prescribed coordinate vector. -/
@[simp]
theorem orderedProdRealizationHomeomorph_symm_fst_val
    (p : Realization K × Realization L) :
    Finsupp.mapDomain Prod.fst
      ((K.orderedProdRealizationHomeomorph L hprod).symm p).1 = p.1.1 := by
  have h := congrArg (fun q => q.1.1)
    ((K.orderedProdRealizationHomeomorph L hprod).apply_symm_apply p)
  simpa only [orderedProdRealizationHomeomorph_apply,
    orderedProdRealizationMap_fst_val] using h

/-- The inverse's second barycentric marginal is the second prescribed coordinate vector. -/
@[simp]
theorem orderedProdRealizationHomeomorph_symm_snd_val
    (p : Realization K × Realization L) :
    Finsupp.mapDomain Prod.snd
      ((K.orderedProdRealizationHomeomorph L hprod).symm p).1 = p.2.1 := by
  have h := congrArg (fun q => q.2.1)
    ((K.orderedProdRealizationHomeomorph L hprod).apply_symm_apply p)
  simpa only [orderedProdRealizationHomeomorph_apply,
    orderedProdRealizationMap_snd_val] using h

end AbstractSimplicialComplex
