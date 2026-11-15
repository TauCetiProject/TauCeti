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
by the explicit `G`-equivariant chain homotopy equivalence
`TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv`, which is strictly natural in group
homomorphisms `φ : G →* H` and is a genuine homotopy equivalence rather than an isomorphism of
chain complexes.

This file connects that equivariant cellular-to-standard comparison directly to Mathlib's group
homology `groupHomology A n` and group cohomology `groupCohomology A n` for arbitrary coefficient
representations `A : Rep k G`:

* `TauCeti.universalGSpaceCellularGroupHomologyIso` and
  `TauCeti.universalGSpaceCellularGroupCohomologyIso` identify `groupHomology A n` and
  `groupCohomology A n` with the homology of `(A ⊗ C_•^{cell}(EG))_G` and the cohomology of
  `Hom_G(C_•^{cell}(EG), A)`, typed directly on `TauCeti.universalGSpaceCellularComplex k G`.
* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap` and
  `TauCeti.groupCohomologyIso_standardResolution_hom_comp_homologyMap` prove that the map induced
  on `(A ⊗ -)_G` homology and `Hom_G(-, A)` cohomology by the explicit geometric cellular-to-bar
  map `(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries the topological
  cellular-resolution computation to Mathlib's algebraic `Rep.standardResolution` computation.
* Along any group homomorphism `φ : G →* H` (with no injectivity assumption) and compatible
  coefficient morphism, `MonoidHom.coinvariantsTensorChainMap_universalGSpaceCellularComplexMap`
  and `MonoidHom.linearYonedaObjMap_universalGSpaceCellularComplexMap` intertwine the induced
  cellular and standard change-of-group chain/cochain maps, and
  `MonoidHom.universalGSpaceCellularGroupHomologyIso_hom_naturality` and
  `MonoidHom.universalGSpaceCellularGroupCohomologyIso_hom_naturality` identify the resulting
  geometric change-of-group maps on homology and cohomology with Mathlib's `groupHomology.map` and
  `groupCohomology.map`.

## Main definitions

* `TauCeti.universalGSpaceCellularGroupHomologyIso`: `Hₙ(G, A) ≅ Hₙ((A ⊗ C_•^{cell}(EG))_G)`.
* `TauCeti.universalGSpaceCellularGroupCohomologyIso`: `Hⁿ(G, A) ≅ Hⁿ(Hom_G(C_•^{cell}(EG), A))`.

## Main results

* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap`,
  `TauCeti.homologyMap_comp_groupHomologyIso_standardResolution_inv`: the explicit geometric
  cellular-to-standard comparison intertwines the cellular and standard computations of
  `groupHomology A n`.
* `TauCeti.groupCohomologyIso_standardResolution_hom_comp_homologyMap`,
  `TauCeti.homologyMap_comp_universalGSpaceCellularGroupCohomologyIso_inv`: the explicit geometric
  cellular-to-standard comparison intertwines the cellular and standard computations of
  `groupCohomology A n`.
* `MonoidHom.coinvariantsTensorChainMap_universalGSpaceCellularComplexMap`,
  `MonoidHom.linearYonedaObjMap_universalGSpaceCellularComplexMap`: naturality of the
  cellular-to-standard chain and cochain comparisons along any `φ : G →* H`.
* `MonoidHom.universalGSpaceCellularGroupHomologyIso_hom_naturality`,
  `MonoidHom.universalGSpaceCellularGroupCohomologyIso_hom_naturality`: naturality of the cellular
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

variable (k : Type u) [CommRing k] (G : Type u) [Group G] (A : Rep.{u} k G)

/-- The explicit geometric cellular-to-standard comparison typed between the underlying complexes
of `universalGSpaceCellularResolution` and `Rep.standardResolution`. -/
def universalGSpaceCellularResolutionToStandard :
    (universalGSpaceCellularResolution k G).complex ⟶ (Rep.standardResolution k G).complex :=
  eqToHom (universalGSpaceCellularResolution_complex k G) ≫
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom

/-- `universalGSpaceCellularResolutionToStandard` factors inside functor maps as the forward map
of `universalGSpaceCellularRepStandardHomotopyEquiv` after
`universalGSpaceCellularResolution_complex`. -/
theorem universalGSpaceCellularResolutionToStandard_def :
    universalGSpaceCellularResolutionToStandard k G =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom :=
  (rfl)

/-- `universalGSpaceCellularResolutionToStandard` preserves the resolution augmentations in degree
zero. -/
@[reassoc]
theorem universalGSpaceCellularResolutionToStandard_f_zero_comp_π :
    (universalGSpaceCellularResolutionToStandard k G).f 0 ≫
        (Rep.standardResolution k G).π.f 0 =
      (universalGSpaceCellularResolution k G).π.f 0 :=
  -- Proved at chain-map level in term mode so `(standardResolution k G).complex` matches
  -- `standardComplex k G` by unfolding.
  HomologicalComplex.congr_hom
    ((Category.assoc _ _ _).trans <|
      (congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
        (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G)).trans
        (universalGSpaceCellularResolution_π k G).symm) 0

/-- **Group homology computed from the geometric cellular chains of Milnor's join.** Identifies
Mathlib's `groupHomology A n` directly with the `n`-th homology of the tensor-coinvariant complex
`(A ⊗ universalGSpaceCellularComplex k G)_G`. -/
def universalGSpaceCellularGroupHomologyIso (n : ℕ) :
    groupHomology A n ≅ ((universalGSpaceCellularComplex k G).coinvariantsTensorObj A).homology n :=
  groupHomologyIso A n (universalGSpaceCellularResolution k G) ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).mapIso
        (eqToIso (universalGSpaceCellularResolution_complex k G)))

/-- Forward map of `universalGSpaceCellularGroupHomologyIso`. -/
theorem universalGSpaceCellularGroupHomologyIso_hom (n : ℕ) :
    (universalGSpaceCellularGroupHomologyIso k G A n).hom =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (eqToHom (universalGSpaceCellularResolution_complex k G))) n :=
  (rfl)

/-- Inverse map of `universalGSpaceCellularGroupHomologyIso`. -/
theorem universalGSpaceCellularGroupHomologyIso_inv (n : ℕ) :
    (universalGSpaceCellularGroupHomologyIso k G A n).inv =
      HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (eqToHom (universalGSpaceCellularResolution_complex k G).symm)) n ≫
        (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv :=
  (rfl)

/-- **Topological-to-algebraic group homology comparison.** The map on tensor-coinvariant homology
induced by the explicit geometric cellular-to-bar comparison
`(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries the geometric cellular
computation of `Hₙ(G, A)` to Mathlib's `Rep.standardResolution` computation. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap (n : ℕ) :
    (universalGSpaceCellularGroupHomologyIso k G A n).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n =
      (groupHomologyIso A n (Rep.standardResolution k G)).hom := by
  rw [universalGSpaceCellularGroupHomologyIso_hom, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
  exact _root_.Rep.groupHomologyIso_hom_comp_homologyMap A
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularResolutionToStandard k G)
    (universalGSpaceCellularResolutionToStandard_f_zero_comp_π k G) n

/-- Inverse form of `universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_groupHomologyIso_standardResolution_inv (n : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n ≫
      (groupHomologyIso A n (Rep.standardResolution k G)).inv =
      (universalGSpaceCellularGroupHomologyIso k G A n).inv :=
  -- Proved in term mode: `(standardResolution k G).complex` agrees with `standardComplex k G`
  -- by unfolding rather than at implicit transparency.
  (Iso.comp_inv_eq _).2 <|
    (Iso.inv_hom_id_assoc (universalGSpaceCellularGroupHomologyIso k G A n) _).symm.trans
      (congrArg ((universalGSpaceCellularGroupHomologyIso k G A n).inv ≫ ·)
        (universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap k G A n))

/-- **Group cohomology computed from the geometric cellular chains of Milnor's join.** Identifies
Mathlib's `groupCohomology A n` directly with the `n`-th cohomology of the equivariant cochain
complex `Hom_G(universalGSpaceCellularComplex k G, A)`. -/
def universalGSpaceCellularGroupCohomologyIso (n : ℕ) :
    groupCohomology A n ≅ ((universalGSpaceCellularComplex k G).linearYonedaObj k A).homology n :=
  groupCohomologyIso A n (universalGSpaceCellularResolution k G) ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((TauCeti.ChainComplex.linearYonedaFunctor k A).mapIso
        (eqToIso (universalGSpaceCellularResolution_complex k G).symm).op)

/-- Forward map of `universalGSpaceCellularGroupCohomologyIso`. -/
theorem universalGSpaceCellularGroupCohomologyIso_hom (n : ℕ) :
    (universalGSpaceCellularGroupCohomologyIso k G A n).hom =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (eqToHom (universalGSpaceCellularResolution_complex k G).symm).op) n :=
  (rfl)

/-- Inverse map of `universalGSpaceCellularGroupCohomologyIso`. -/
theorem universalGSpaceCellularGroupCohomologyIso_inv (n : ℕ) :
    (universalGSpaceCellularGroupCohomologyIso k G A n).inv =
      HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (eqToHom (universalGSpaceCellularResolution_complex k G)).op) n ≫
        (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).inv :=
  (rfl)

/-- **Algebraic-to-topological group cohomology comparison.** Precomposing equivariant cochains
with the explicit geometric cellular-to-bar comparison
`(universalGSpaceCellularRepStandardHomotopyEquiv k G).hom` carries Mathlib's
`Rep.standardResolution` computation of `Hⁿ(G, A)` to the geometric cellular computation. -/
@[reassoc]
theorem groupCohomologyIso_standardResolution_hom_comp_homologyMap (n : ℕ) :
    (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n =
      (universalGSpaceCellularGroupCohomologyIso k G A n).hom := by
  have h := A.groupCohomologyIso_hom_comp_homologyMap
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularResolutionToStandard k G)
    (universalGSpaceCellularResolutionToStandard_f_zero_comp_π k G) n
  have heq : eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
      universalGSpaceCellularResolutionToStandard k G =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (eqToHom_trans _ _)).trans (Category.id_comp _)
  have hcomp :
      HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (universalGSpaceCellularResolutionToStandard k G).op) n ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (eqToHom (universalGSpaceCellularResolution_complex k G).symm).op) n =
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (((TauCeti.ChainComplex.linearYonedaFunctor k A).map_comp
          (universalGSpaceCellularResolutionToStandard k G).op
          (eqToHom (universalGSpaceCellularResolution_complex k G).symm).op).symm)).trans <|
        congrArg (fun f : universalGSpaceCellularComplex k G ⟶ Rep.standardComplex k G ↦
          HomologicalComplex.homologyMap
            ((TauCeti.ChainComplex.linearYonedaFunctor k A).map f.op) n) heq
  -- Assemble in term mode so `linearYonedaFunctor` object unfolding matches `linearYonedaObj`.
  exact (congrArg ((groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫ ·)
      hcomp.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h).trans (universalGSpaceCellularGroupCohomologyIso_hom k G A n).symm))

/-- Inverse form of `groupCohomologyIso_standardResolution_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_universalGSpaceCellularGroupCohomologyIso_inv (n : ℕ) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n ≫
      (universalGSpaceCellularGroupCohomologyIso k G A n).inv =
      (groupCohomologyIso A n (Rep.standardResolution k G)).inv :=
  -- Proved in term mode: `(linearYonedaFunctor k A).obj (op _)` agrees with `linearYonedaObj` by
  -- unfolding rather than at implicit transparency.
  (Iso.comp_inv_eq _).2 <|
    (Iso.inv_hom_id_assoc (groupCohomologyIso A n (Rep.standardResolution k G)) _).symm.trans
      (congrArg ((groupCohomologyIso A n (Rep.standardResolution k G)).inv ≫ ·)
        (groupCohomologyIso_standardResolution_hom_comp_homologyMap k G A n))

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
theorem coinvariantsTensorChainMap_universalGSpaceCellularComplexMap
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
For any `φ : G →* H` and `ξ : A ⟶ Rep.res φ B`, `universalGSpaceCellularGroupHomologyIso` carries
Mathlib's `groupHomology.map φ ξ n` to the map induced on homology by
`φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap`. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_hom_naturality
    (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    groupHomology.map φ ξ n ≫ (universalGSpaceCellularGroupHomologyIso k H B n).hom =
      (universalGSpaceCellularGroupHomologyIso k G A n).hom ≫
        HomologicalComplex.homologyMap
          (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n := by
  have hstd := φ.groupHomologyIso_hom_naturality ξ (Rep.standardResolution k G)
    (Rep.standardResolution k H) φ.standardComplexMap
    φ.standardComplexMap_f_zero_comp_standardResolution_π n
  let mG := HomologicalComplex.homologyMap
    ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n
  let mH := HomologicalComplex.homologyMap
    ((((Rep.coinvariantsTensor k H).obj B).mapHomologicalComplex _).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom) n
  let cCell := HomologicalComplex.homologyMap
    (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n
  let cStd := HomologicalComplex.homologyMap
    (φ.coinvariantsTensorChainMap ξ φ.standardComplexMap) n
  have hcomm : cCell ≫ mH = mG ≫ cStd :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (φ.coinvariantsTensorChainMap_universalGSpaceCellularComplexMap ξ)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  -- Assemble in term mode: `(standardResolution k _).complex` agrees with `standardComplex k _`
  -- by unfolding rather than at implicit transparency.
  refine (Iso.eq_comp_inv (universalGSpaceCellularGroupHomologyIso k H B n)).1 ?_
  symm
  exact (congrArg (((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ cCell) ≫ ·)
      (homologyMap_comp_groupHomologyIso_standardResolution_inv k H B n).symm).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg ((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ ·)
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hcomm))).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ (groupHomologyIso B n (Rep.standardResolution k H)).inv)
            (((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ cStd)
                (universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap k G A n))).trans
              hstd.symm)).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _)

/-- Inverse form of `universalGSpaceCellularGroupHomologyIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_inv_naturality
    (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n ≫
      (universalGSpaceCellularGroupHomologyIso k H B n).inv =
      (universalGSpaceCellularGroupHomologyIso k G A n).inv ≫ groupHomology.map φ ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    φ.universalGSpaceCellularGroupHomologyIso_hom_naturality ξ n, Iso.inv_hom_id_assoc]

end Homology

section Cohomology

variable {A : Rep.{u} k H} {B : Rep.{u} k G}

/-- **Cochain-level change-of-group naturality of the geometric cellular-to-standard comparison on
equivariant morphism complexes.** Along any group homomorphism `φ : G →* H` and compatible
coefficient map `ξ : Rep.res φ A ⟶ B`, `linearYonedaObjMap` intertwines the cellular and standard
cochain maps via `universalGSpaceCellularRepStandardHomotopyEquiv`. -/
@[reassoc]
theorem linearYonedaObjMap_universalGSpaceCellularComplexMap
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) :
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op ≫
      φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap =
      φ.linearYonedaObjMap ξ φ.standardComplexMap ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k B).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op :=
  (φ.linearYonedaFunctor_map_comp_linearYonedaObjMap ξ
    φ.universalGSpaceCellularComplexMap
    (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom).trans <|
    (congrArg (φ.linearYonedaObjMap ξ ·)
      (φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (k := k))).trans
      (φ.linearYonedaObjMap_comp_linearYonedaFunctor_map ξ φ.standardComplexMap
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).symm

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the group**,
inverse form: for any `φ : G →* H` and `ξ : Rep.res φ A ⟶ B`,
`universalGSpaceCellularGroupCohomologyIso` carries the map induced on cohomology by
`φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap` to Mathlib's
`groupCohomology.map φ ξ n`. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_inv_naturality
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n ≫
      (universalGSpaceCellularGroupCohomologyIso k G B n).inv =
      (universalGSpaceCellularGroupCohomologyIso k H A n).inv ≫ groupCohomology.map φ ξ n := by
  have hstd := φ.groupCohomologyIso_inv_naturality ξ (Rep.standardResolution k G)
    (Rep.standardResolution k H) φ.standardComplexMap
    φ.standardComplexMap_f_zero_comp_standardResolution_π n
  let mH := HomologicalComplex.homologyMap
    ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op) n
  let mG := HomologicalComplex.homologyMap
    ((TauCeti.ChainComplex.linearYonedaFunctor k B).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n
  let cCell := HomologicalComplex.homologyMap
    (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n
  let cStd := HomologicalComplex.homologyMap
    (φ.linearYonedaObjMap ξ φ.standardComplexMap) n
  have hcomm : mH ≫ cCell = cStd ≫ mG :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (φ.linearYonedaObjMap_universalGSpaceCellularComplexMap ξ)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  -- Assemble in term mode: `(linearYonedaFunctor k _).obj (op _)` agrees with `linearYonedaObj`
  -- by unfolding rather than at implicit transparency.
  refine (Iso.eq_inv_comp (universalGSpaceCellularGroupCohomologyIso k H A n)).2 ?_
  exact (congrArg (· ≫ (cCell ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).inv))
      (groupCohomologyIso_standardResolution_hom_comp_homologyMap k H A n).symm).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg ((groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫ ·)
        ((Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ _) hcomm).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (cStd ≫ ·)
                (homologyMap_comp_universalGSpaceCellularGroupCohomologyIso_inv k G B n)).trans
                hstd)).trans
        (Iso.hom_inv_id_assoc _ _)

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the group.**
For any `φ : G →* H` and `ξ : Rep.res φ A ⟶ B`, `universalGSpaceCellularGroupCohomologyIso` carries
Mathlib's `groupCohomology.map φ ξ n` to the map induced on cohomology by
`φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap`. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_hom_naturality
    (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    groupCohomology.map φ ξ n ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).hom =
      (universalGSpaceCellularGroupCohomologyIso k H A n).hom ≫
        HomologicalComplex.homologyMap
          (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc,
    ← φ.universalGSpaceCellularGroupCohomologyIso_inv_naturality ξ n,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Cohomology

end MonoidHom
