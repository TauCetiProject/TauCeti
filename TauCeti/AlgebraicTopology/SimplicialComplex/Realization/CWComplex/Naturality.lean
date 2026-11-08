/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.InducedChainMap
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex

/-!
# Naturality of cellular and ordered simplicial chains

A simplicial map induces a map of ordered simplicial chain complexes
(`TauCeti.orderedSimplicialChainComplexMap`). When the simplicial map is strictly increasing on
each simplex, this chain map sends each oriented simplex to its image with the same coefficient.
The hypothesis is simplexwise: the map need not be injective or increasing on all vertices. This
includes the label maps between countable joins induced by arbitrary group homomorphisms.

For such maps, the comparison `TauCeti.cellularChainComplexRealizationIso` intertwines the
ordered chain map with the cellular chain map of the realization. Thus the identification of
ordered simplicial chains with cellular chains is natural, not merely an objectwise isomorphism.
In particular, translation actions and maps between joins can be computed on ordered chains
while retaining their geometric cellular interpretation.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 2.2 (simplicial and cellular chains).
-/

public section

noncomputable section

open CategoryTheory Finsupp Set Topology
open AbstractSimplicialComplex PreAbstractSimplicialComplex.SimplicialMap

universe u v

namespace TauCeti.OrderedSimplicialChain

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ} {R : Type v} [Ring R]
  (f : PreAbstractSimplicialComplex.SimplicialMap
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)

/-- A simplicial map increasing on a cell sends a multiple of that cell to the same multiple of
its image cell, without a change of sign. -/
theorem map_single_of_strictMonoOn {n : ℕ} (c : RealizationCell K n)
    (hc : StrictMonoOn f (↑c.1.1 : Set ι)) (r : R) :
    map R f n (single c r) = single (c.map f hc.injOn) r := by
  rw [map_single, ← RealizationCell.vertexEmbedding_map c f hc, tupleChain_vertexEmbedding,
    smul_single, smul_eq_mul, mul_one]

end TauCeti.OrderedSimplicialChain

namespace PreAbstractSimplicialComplex.SimplicialMap

open TauCeti

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
  (hf : ∀ n (c : RealizationCell K n), StrictMonoOn f (↑c.1.1 : Set ι))
  (R : Type u) [Ring R]

include hf

/-- The identification of cellular chains with ordered chains intertwines the cellular map of
a realization with the map of ordered chains, in each degree. -/
theorem cellularChainRealizationLinearEquiv_naturality (n : ℕ) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    (cellularChainRealizationLinearEquiv L R n).toLinearMap ∘ₗ
        (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) n).hom =
      OrderedSimplicialChain.map R f n ∘ₗ
        (cellularChainRealizationLinearEquiv K R n).toLinearMap := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  refine (cellularChainBasis _ R n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv K n).symm.surjective i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cellularChainGroupMap_realization_cellularChainBasis R f c (hf n c),
    cellularChainRealizationLinearEquiv_cellularChainBasis,
    cellularChainRealizationLinearEquiv_cellularChainBasis,
    OrderedSimplicialChain.map_single_of_strictMonoOn f c (hf n c)]

/-- **Cellular chains are naturally ordered simplicial chains.** Under the comparison
isomorphisms, the cellular chain map of a simplexwise increasing simplicial map is the map
sending each ordered simplex to its image. -/
@[reassoc]
theorem cellularChainComplexRealizationIso_hom_naturality :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainComplexMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) ≫
        (cellularChainComplexRealizationIso L R).hom =
      (cellularChainComplexRealizationIso K R).hom ≫
        orderedSimplicialChainComplexMap R f := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularChainComplexRealizationIso_hom_f, orderedSimplicialChainComplexMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h : cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) n ≫
        (cellularChainRealizationLinearEquiv L R n).toModuleIso.hom =
      (cellularChainRealizationLinearEquiv K R n).toModuleIso.hom ≫
        ModuleCat.ofHom (OrderedSimplicialChain.map R f n) :=
    ModuleCat.hom_ext (f.cellularChainRealizationLinearEquiv_naturality hf R n)
  congr 1
  simp only [← Category.assoc]
  rw [h]

end PreAbstractSimplicialComplex.SimplicialMap
