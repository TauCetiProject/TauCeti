/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex

/-!
# Naturality of cellular and ordered simplicial chains

A simplicial map that is strictly increasing on each simplex induces a map of ordered
simplicial chain complexes, sending each oriented simplex to its image with the same
coefficient. The hypothesis is simplexwise: the map need not be injective or increasing on
all vertices. This includes the label maps between countable joins induced by arbitrary
group homomorphisms.

The comparison `TauCeti.cellularChainComplexRealizationIso` intertwines this chain map with
the cellular chain map of the realization. Thus the identification of ordered simplicial
chains with cellular chains is natural, not merely an objectwise isomorphism. In particular,
translation actions and maps between joins can be computed on ordered chains while retaining
their geometric cellular interpretation.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 2.2 (simplicial and cellular chains).
-/

public section

noncomputable section

open CategoryTheory Finsupp Set Topology
open AbstractSimplicialComplex PreAbstractSimplicialComplex.SimplicialMap

universe u v

namespace TauCeti

variable {ι κ τ : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder τ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  {P : AbstractSimplicialComplex τ}
  (R : Type v) [Ring R]
  (f : PreAbstractSimplicialComplex.SimplicialMap
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
  (hf : ∀ n (c : RealizationCell K n), StrictMonoOn f (↑c.1.1 : Set ι))

namespace OrderedSimplicialChain

/-- The map on ordered chains induced by a simplicial map increasing on each simplex. -/
def map (n : ℕ) : OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n :=
  lmapDomain R R (fun c ↦ c.map f (hf n c).injOn)

/-- A simplex is sent to its image, with its coefficient unchanged. -/
@[simp]
theorem map_single {n : ℕ} (c : RealizationCell K n) (r : R) :
    map R f hf n (single c r) = single (c.map f (hf n c).injOn) r := by
  simp [map]

/-- The identity simplicial map acts as the identity on ordered chains. -/
@[simp]
theorem map_id (n : ℕ) :
    map R (PreAbstractSimplicialComplex.SimplicialMap.id K.toPreAbstractSimplicialComplex)
      (strictMonoOn_id_realizationCell K) n = LinearMap.id := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

/-- Mapping ordered chains along a composite agrees with successive mapping. -/
theorem map_comp
    (g : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex)
    (hg : ∀ n (c : RealizationCell L n), StrictMonoOn g (↑c.1.1 : Set κ)) (n : ℕ) :
    map R (g.comp f) (f.strictMonoOn_comp_realizationCell hf g hg) n =
      map R g hg n ∘ₗ map R f hf n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, lsingle_apply, map_single]
  congr 1
  exact (RealizationCell.map_map c f (hf n c).injOn g (by
    simpa only [RealizationCell.coe_map_face, Finset.coe_image] using
      (hg n (c.map f (hf n c).injOn)).injOn)).symm

/-- Increasing simplexwise maps commute with the alternating boundary. -/
theorem boundary_comp_map (n : ℕ) :
    boundary R n ∘ₗ map R f hf (n + 1) = map R f hf n ∘ₗ boundary R n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, lsingle_apply, map_single, boundary_single,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RealizationCell.face_map c f (hf (n + 1) c) j]

end OrderedSimplicialChain

/-- The map of ordered simplicial chain complexes induced by a simplicial map increasing on
each simplex. It sends an oriented simplex to its image without a change of sign. -/
def orderedSimplicialChainComplexMap :
    orderedSimplicialChainComplex K R ⟶ orderedSimplicialChainComplex L R where
  f n := eqToHom (orderedSimplicialChainComplex_X R n) ≫
    ModuleCat.ofHom (OrderedSimplicialChain.map R f hf n) ≫
      eqToHom (orderedSimplicialChainComplex_X R n).symm
  comm' i j h := by
    subst i
    simp only [orderedSimplicialChainComplex_d, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    congr 1
    simp only [← Category.assoc]
    congr 1
    exact ModuleCat.hom_ext (OrderedSimplicialChain.boundary_comp_map R f hf j)

/-- The degreewise map is the linear extension of the map on simplices. -/
@[simp]
theorem orderedSimplicialChainComplexMap_f (n : ℕ) :
    (orderedSimplicialChainComplexMap R f hf).f n =
      eqToHom (orderedSimplicialChainComplex_X R n) ≫
        ModuleCat.ofHom (OrderedSimplicialChain.map R f hf n) ≫
          eqToHom (orderedSimplicialChainComplex_X R n).symm :=
  (rfl)

/-- The identity simplicial map induces the identity chain map. -/
@[simp]
theorem orderedSimplicialChainComplexMap_id :
    orderedSimplicialChainComplexMap R
        (PreAbstractSimplicialComplex.SimplicialMap.id K.toPreAbstractSimplicialComplex)
        (strictMonoOn_id_realizationCell K) = 𝟙 _ := by
  ext n : 1
  simp [OrderedSimplicialChain.map_id]

/-- Composing simplexwise increasing simplicial maps composes their chain maps. -/
theorem orderedSimplicialChainComplexMap_comp
    (g : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex)
    (hg : ∀ n (c : RealizationCell L n), StrictMonoOn g (↑c.1.1 : Set κ)) :
    orderedSimplicialChainComplexMap R (g.comp f)
        (f.strictMonoOn_comp_realizationCell hf g hg) =
      orderedSimplicialChainComplexMap R f hf ≫ orderedSimplicialChainComplexMap R g hg := by
  ext n : 1
  simp only [orderedSimplicialChainComplexMap_f, HomologicalComplex.comp_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  rw [← Category.assoc, cancel_mono, ← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom]
  exact OrderedSimplicialChain.map_comp R f hf g hg n

end TauCeti

namespace PreAbstractSimplicialComplex.SimplicialMap

open TauCeti

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
  (hf : ∀ n (c : RealizationCell K n), StrictMonoOn f (↑c.1.1 : Set ι))
  (R : Type u) [Ring R]

/-- The identification of cellular chains with ordered chains intertwines the cellular map of
a realization with the map of ordered chains, in each degree. -/
theorem cellularChainRealizationLinearEquiv_naturality (n : ℕ) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    (cellularChainRealizationLinearEquiv L R n).toLinearMap ∘ₗ
        (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) n).hom =
      OrderedSimplicialChain.map R f hf n ∘ₗ
        (cellularChainRealizationLinearEquiv K R n).toLinearMap := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  refine (cellularChainBasis _ R n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv K n).symm.surjective i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cellularChainGroupMap_realization_cellularChainBasis R f c (hf n c),
    cellularChainRealizationLinearEquiv_cellularChainBasis,
    cellularChainRealizationLinearEquiv_cellularChainBasis, OrderedSimplicialChain.map_single]

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
        orderedSimplicialChainComplexMap R f hf := by
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
        ModuleCat.ofHom (OrderedSimplicialChain.map R f hf n) :=
    ModuleCat.hom_ext (f.cellularChainRealizationLinearEquiv_naturality hf R n)
  congr 1
  simp only [← Category.assoc]
  rw [h]

end PreAbstractSimplicialComplex.SimplicialMap
