/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.OrderedCoupling.Existence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Product
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Lifting points to an ordered simplicial product

Every pair of points in the realizations of two ordered simplicial complexes admits a lift
to their staircase product. Its barycentric coordinates are nonnegative joint weights with
the prescribed marginals, and its carrier is a chain in the coordinatewise order.

This is the existence part of identifying the realization of an ordered simplicial product
with the product of realizations. In particular, it applies to the simplicial cylinder. No
finiteness hypothesis on the vertex types or complexes is required: each pair of points has
finite support.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (triangulating products of polyhedra).
-/

public section

namespace AbstractSimplicialComplex

open TauCeti.SetLike PreAbstractSimplicialComplex.SimplicialMap

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Every pair of realization points has a lift to the ordered product under the two
canonical realization projections. -/
theorem exists_realization_orderedProd (K : AbstractSimplicialComplex α)
    (L : AbstractSimplicialComplex β) (x : Realization K) (y : Realization L) :
    ∃ z : Realization (orderedProd K L),
      (orderedProdFst K.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex |>.domainRestrict
          (by rw [orderedProd_toPreAbstractSimplicialComplex])).realizationMap z = x ∧
      (orderedProdSnd K.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex |>.domainRestrict
          (by rw [orderedProd_toPreAbstractSimplicialComplex])).realizationMap z = y := by
  obtain ⟨w, hw, hchain, hwx, hwy⟩ := Finsupp.exists_nonneg_isChain_mapDomain x.1 y.1
    (Realization.nonneg K x) (Realization.nonneg L y)
    ((Realization.sum_eq_one K x).trans (Realization.sum_eq_one L y).symm)
  have hface : w.support ∈ orderedProd K L := by
    rw [mem_orderedProd_iff]
    refine ⟨?_, ?_, hchain⟩
    · rw [← Finsupp.support_mapDomain_of_nonneg hw, hwx]
      exact support_mem K x
    · rw [← Finsupp.support_mapDomain_of_nonneg hw, hwy]
      exact support_mem L y
  have hmass : w.sum (fun _ r => r) = 1 := by
    have h := Finsupp.sum_mapDomain_index (s := w) (f := Prod.fst)
      (h := fun _ (r : ℝ) => r) (fun _ => rfl) (fun _ _ _ => rfl)
    rw [hwx, Realization.sum_eq_one K x] at h
    exact h.symm
  have hwmem : w ∈ (standardGeometricComplex (orderedProd K L)).space := by
    refine mem_realization_iff.mpr ⟨w.support, hface, ?_⟩
    simpa only [Finset.coe_image] using
      (mem_standardSimplex_iff (σ := w.support)).mpr ⟨hw, hmass, Finset.Subset.refl _⟩
  refine ⟨⟨w, hwmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    simpa only [PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_domainRestrict, coe_orderedProdFst] using hwx
  · apply Subtype.ext
    simpa only [PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_domainRestrict, coe_orderedProdSnd] using hwy

end AbstractSimplicialComplex
