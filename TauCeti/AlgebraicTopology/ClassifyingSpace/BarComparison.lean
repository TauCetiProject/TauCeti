/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.GeometricNaturality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups

/-!
# Group (co)homology from Milnor's cellular resolution and comparison with the standard resolution

Milnor's countable join `universalGSpace G` carries a free cellular `G`-action whose geometric
cellular chains form the projective resolution `TauCeti.universalGSpaceCellularResolution k G` of
the trivial representation `k`, while Mathlib's `Rep.standardResolution k G` resolves `k`
algebraically by tuples of group elements. In
`TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains` and
`TauCeti.AlgebraicTopology.ClassifyingSpace.GeometricNaturality`, these two resolutions are linked
by the `G`-equivariant chain homotopy equivalence
`TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv`: its forward map `.hom` is explicit,
strictly natural in group homomorphisms `φ : G →* H`, and (when `k` is nontrivial) not an
isomorphism of chain complexes, while its homotopy inverse comes from `ProjectiveResolution.lift`
and is natural up to equivariant chain homotopy.

Because `TauCeti.universalGSpaceCellularResolution k G` has underlying complex
`TauCeti.universalGSpaceCellularComplex k G` by definition, Mathlib's
`groupHomologyIso A n (universalGSpaceCellularResolution k G)` and
`groupCohomologyIso A n (universalGSpaceCellularResolution k G)` identify `groupHomology A n` and
`groupCohomology A n` directly with the homology of `(A ⊗ C_•^{cell}(EG))_G` and the cohomology of
`Hom_G(C_•^{cell}(EG), A)`, and the generic projective-resolution coefficient-naturality and
connecting-morphism lemmas apply without transport. This file connects that geometric computation
to `Rep.standardResolution` and to change-of-groups functoriality:

* `TauCeti.groupHomologyIso_universalGSpaceCellular_hom_comp_homologyMap_standardResolution` and
  `TauCeti.groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular`
  prove that the explicit geometric cellular-to-bar map
  `(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries the cellular-resolution
  computation to Mathlib's `Rep.standardResolution` computation on `(A ⊗ -)_G` homology, and
  conversely carries the `Rep.standardResolution` computation to the cellular-resolution
  computation on `Hom_G(-, A)` cohomology.
* Along any group homomorphism `φ : G →* H` (with no injectivity assumption) and compatible
  coefficient morphism,
  `MonoidHom.coinvariantsTensorChainMap_comp_universalGSpaceCellularRepStandardHomotopyEquiv_hom`
  and `MonoidHom.map_universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_linearYonedaObjMap`
  intertwine the induced cellular and standard change-of-group chain/cochain maps, and
  `MonoidHom.groupHomologyIso_universalGSpaceCellular_hom_naturality` and
  `MonoidHom.groupCohomologyIso_universalGSpaceCellular_hom_naturality` identify the resulting
  geometric change-of-group maps on homology and cohomology with Mathlib's `groupHomology.map` and
  `groupCohomology.map`.

## Main results

* `TauCeti.groupHomologyIso_universalGSpaceCellular_hom_comp_homologyMap_standardResolution`,
  `TauCeti.homologyMap_universalGSpaceCellular_comp_groupHomologyIso_standardResolution_inv`:
  the explicit geometric cellular-to-standard comparison carries the cellular computation of
  `groupHomology A n` to the `Rep.standardResolution` computation.
* `TauCeti.groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular`,
  `TauCeti.homologyMap_standardResolution_comp_groupCohomologyIso_universalGSpaceCellular_inv`:
  precomposing with the explicit geometric cellular-to-standard comparison carries the
  `Rep.standardResolution` computation of `groupCohomology A n` to the cellular computation.
* `MonoidHom.coinvariantsTensorChainMap_comp_universalGSpaceCellularRepStandardHomotopyEquiv_hom`,
  `MonoidHom.map_universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_linearYonedaObjMap`:
  naturality of the cellular-to-standard chain and cochain comparisons along any `φ : G →* H`.
* `MonoidHom.groupHomologyIso_universalGSpaceCellular_hom_naturality`,
  `MonoidHom.groupHomologyIso_universalGSpaceCellular_inv_naturality`,
  `MonoidHom.groupCohomologyIso_universalGSpaceCellular_inv_naturality`,
  `MonoidHom.groupCohomologyIso_universalGSpaceCellular_hom_naturality`: naturality of the cellular
  group (co)homology identifications along any `φ : G →* H`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapters I.7, II.4, and III.8.

The standard complex, `groupHomology`, and `groupCohomology` are Mathlib's constructions by Amelia
Livingston; projective-resolution comparisons build on Mathlib's `ProjectiveResolution` API by Kim
Morrison and Joël Riou.
-/

public section

noncomputable section

open CategoryTheory Opposite

namespace TauCeti

universe u

section Comparison

variable (k : Type u) [CommRing k] (G : Type u) [Group G] (A : Rep.{u} k G)

/-- **Topological-to-algebraic group homology comparison.** The map on tensor-coinvariant homology
induced by the explicit geometric cellular-to-bar comparison
`(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries the geometric cellular
computation of `Hₙ(G, A)` to Mathlib's `Rep.standardResolution` computation. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellular_hom_comp_homologyMap_standardResolution
    (n : ℕ) :
    (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n =
      (groupHomologyIso A n (Rep.standardResolution k G)).hom :=
  A.groupHomologyIso_hom_comp_homologyMap
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
    (HomologicalComplex.congr_hom (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G) 0) n

/-- Inverse form of
`groupHomologyIso_universalGSpaceCellular_hom_comp_homologyMap_standardResolution`. -/
@[reassoc]
theorem homologyMap_universalGSpaceCellular_comp_groupHomologyIso_standardResolution_inv
    (n : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n ≫
      (groupHomologyIso A n (Rep.standardResolution k G)).inv =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv :=
  A.homologyMap_comp_groupHomologyIso_inv
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
    (HomologicalComplex.congr_hom (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G) 0) n

/-- **Algebraic-to-topological group cohomology comparison.** Precomposing equivariant cochains
with the explicit geometric cellular-to-bar comparison
`(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries Mathlib's
`Rep.standardResolution` computation of `Hⁿ(G, A)` to the geometric cellular computation. -/
@[reassoc]
theorem groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular
    (n : ℕ) :
    (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).hom :=
  A.groupCohomologyIso_hom_comp_homologyMap
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
    (HomologicalComplex.congr_hom (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G) 0) n

/-- Inverse form of
`groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular`. -/
@[reassoc]
theorem homologyMap_standardResolution_comp_groupCohomologyIso_universalGSpaceCellular_inv
    (n : ℕ) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n ≫
      (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (Rep.standardResolution k G)).inv :=
  A.homologyMap_comp_groupCohomologyIso_inv
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
    (HomologicalComplex.congr_hom (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G) 0) n

end Comparison

end TauCeti

namespace MonoidHom

open CategoryTheory Opposite TauCeti

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

section Homology

variable {A : Rep.{u} k G} {B : Rep.{u} k H}

/-- **Chain-level change-of-group naturality of the geometric cellular-to-standard comparison on
tensor coinvariants.** Along any group homomorphism `φ : G →* H` and compatible coefficient map
`ξ : A ⟶ Rep.res φ B`, `coinvariantsTensorChainMap` intertwines the cellular and standard chain
maps via `universalGSpaceCellularRepStandardHomotopyEquiv`. -/
@[reassoc]
theorem coinvariantsTensorChainMap_comp_universalGSpaceCellularRepStandardHomotopyEquiv_hom
    (φ : G →* H) (ξ : A ⟶ Rep.res φ B) :
    φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap ≫
        (((Rep.coinvariantsTensor k H).obj B).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        φ.coinvariantsTensorChainMap ξ φ.standardComplexMap := by
  rw [coinvariantsTensorChainMap_comp_mapHomologicalComplex_map,
    mapHomologicalComplex_map_comp_coinvariantsTensorChainMap,
    φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality]

/-- **Group homology computed from Milnor's geometric cellular chains is natural in the group.**
For any `φ : G →* H` and `ξ : A ⟶ Rep.res φ B`, `groupHomologyIso` on
`universalGSpaceCellularResolution` carries Mathlib's `groupHomology.map φ ξ n` to the map induced
on homology by `φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap`. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellular_hom_naturality
    (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    groupHomology.map φ ξ n ≫
        (groupHomologyIso B n (universalGSpaceCellularResolution k H)).hom =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n :=
  φ.groupHomologyIso_hom_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularComplexMap
    φ.universalGSpaceCellularComplexMap_f_zero_comp_π n

/-- Inverse form of `MonoidHom.groupHomologyIso_universalGSpaceCellular_hom_naturality`. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellular_inv_naturality
    (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n ≫
      (groupHomologyIso B n (universalGSpaceCellularResolution k H)).inv =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv ≫
        groupHomology.map φ ξ n :=
  φ.groupHomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularComplexMap
    φ.universalGSpaceCellularComplexMap_f_zero_comp_π n

end Homology

section Cohomology

variable {A : Rep.{u} k H} {B : Rep.{u} k G}

/-- **Cochain-level change-of-group naturality of the geometric cellular-to-standard comparison on
equivariant morphism complexes.** Along any group homomorphism `φ : G →* H` and compatible
coefficient map `ξ : Rep.res φ A ⟶ B`, `linearYonedaObjMap` intertwines the cellular and standard
cochain maps via `universalGSpaceCellularRepStandardHomotopyEquiv`. -/
@[reassoc]
theorem map_universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_linearYonedaObjMap
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) :
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op ≫
      φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap =
      φ.linearYonedaObjMap ξ φ.standardComplexMap ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k B).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op :=
  let L_H : (Rep.standardComplex k H).linearYonedaObj k A ⟶
      (universalGSpaceCellularComplex k H).linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op
  let L_G : (Rep.standardComplex k G).linearYonedaObj k B ⟶
      (universalGSpaceCellularComplex k G).linearYonedaObj k B :=
    (TauCeti.ChainComplex.linearYonedaFunctor k B).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op
  calc L_H ≫ φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap
      = φ.linearYonedaObjMap ξ (φ.universalGSpaceCellularComplexMap ≫
          ((Rep.resFunctor φ).mapHomologicalComplex _).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom) :=
        φ.linearYonedaFunctor_map_comp_linearYonedaObjMap ξ
          φ.universalGSpaceCellularComplexMap
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom
    _ = φ.linearYonedaObjMap ξ
          ((universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap) :=
        congrArg (φ.linearYonedaObjMap ξ ·)
          (φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (k := k))
    _ = φ.linearYonedaObjMap ξ φ.standardComplexMap ≫ L_G :=
        (φ.linearYonedaObjMap_comp_linearYonedaFunctor_map ξ φ.standardComplexMap
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).symm

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the group**,
inverse form: for any `φ : G →* H` and `ξ : Rep.res φ A ⟶ B`, `groupCohomologyIso` on
`universalGSpaceCellularResolution` carries the map induced on cohomology by
`φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap` to Mathlib's
`groupCohomology.map φ ξ n`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellular_inv_naturality
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n ≫
      (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).inv ≫
        groupCohomology.map φ ξ n :=
  φ.groupCohomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularComplexMap
    φ.universalGSpaceCellularComplexMap_f_zero_comp_π n

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the group.**
For any `φ : G →* H` and `ξ : Rep.res φ A ⟶ B`, `groupCohomologyIso` on
`universalGSpaceCellularResolution` carries Mathlib's `groupCohomology.map φ ξ n` to the map
induced on cohomology by `φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellular_hom_naturality
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).hom =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).hom ≫
        HomologicalComplex.homologyMap
          (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n :=
  φ.groupCohomologyIso_hom_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularComplexMap
    φ.universalGSpaceCellularComplexMap_f_zero_comp_π n

end Cohomology

end MonoidHom
