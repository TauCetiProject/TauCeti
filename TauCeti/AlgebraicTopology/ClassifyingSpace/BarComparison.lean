/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.GeometricNaturality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Coefficients
import Mathlib.Algebra.Homology.HomologySequenceLemmas

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

This file connects that equivariant cellular-to-standard comparison directly to Mathlib's group
homology `groupHomology A n` and group cohomology `groupCohomology A n` for arbitrary coefficient
representations `A : Rep k G`:

* `TauCeti.universalGSpaceCellularGroupHomologyIso` and
  `TauCeti.universalGSpaceCellularGroupCohomologyIso` identify `groupHomology A n` and
  `groupCohomology A n` with the homology of `(A ⊗ C_•^{cell}(EG))_G` and the cohomology of
  `Hom_G(C_•^{cell}(EG), A)`, typed directly on `TauCeti.universalGSpaceCellularComplex k G`.
* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_naturality`,
  `TauCeti.universalGSpaceCellularGroupCohomologyIso_hom_naturality`,
  `TauCeti.groupHomology_δ_comp_universalGSpaceCellularGroupHomologyIso_hom`, and
  `TauCeti.groupCohomology_δ_comp_universalGSpaceCellularGroupCohomologyIso_hom` prove that both
  identifications are natural in coefficient morphisms `f : A ⟶ B` and intertwine Mathlib's
  connecting morphisms `groupHomology.δ` and `groupCohomology.δ` with the connecting morphisms of
  `(A ⊗ C_•^{cell}(EG))_G` and `Hom_G(C_•^{cell}(EG), A)` for any short exact sequence of
  representations.
* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution` and
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
  `MonoidHom.universalGSpaceCellularGroupHomologyIso_hom_naturality` and
  `MonoidHom.universalGSpaceCellularGroupCohomologyIso_hom_naturality` identify the resulting
  geometric change-of-group maps on homology and cohomology with Mathlib's `groupHomology.map` and
  `groupCohomology.map`.

## Main definitions

* `TauCeti.universalGSpaceCellularGroupHomologyIso`: `Hₙ(G, A) ≅ Hₙ((A ⊗ C_•^{cell}(EG))_G)`.
* `TauCeti.universalGSpaceCellularGroupCohomologyIso`: `Hⁿ(G, A) ≅ Hⁿ(Hom_G(C_•^{cell}(EG), A))`.

## Main results

* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution`,
  `TauCeti.homologyMap_universalGSpaceCellular_comp_groupHomologyIso_standardResolution_inv`:
  the explicit geometric cellular-to-standard comparison carries the cellular computation of
  `groupHomology A n` to the `Rep.standardResolution` computation.
* `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_naturality`,
  `TauCeti.universalGSpaceCellularGroupHomologyIso_inv_naturality`,
  `TauCeti.groupHomology_δ_comp_universalGSpaceCellularGroupHomologyIso_hom`,
  `TauCeti.δ_comp_universalGSpaceCellularGroupHomologyIso_inv`: coefficient naturality and
  connecting-morphism compatibility of `universalGSpaceCellularGroupHomologyIso`.
* `TauCeti.groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular`,
  `TauCeti.homologyMap_standardResolution_comp_universalGSpaceCellularGroupCohomologyIso_inv`:
  precomposing with the explicit geometric cellular-to-standard comparison carries the
  `Rep.standardResolution` computation of `groupCohomology A n` to the cellular computation.
* `TauCeti.universalGSpaceCellularGroupCohomologyIso_hom_naturality`,
  `TauCeti.universalGSpaceCellularGroupCohomologyIso_inv_naturality`,
  `TauCeti.groupCohomology_δ_comp_universalGSpaceCellularGroupCohomologyIso_hom`,
  `TauCeti.δ_comp_universalGSpaceCellularGroupCohomologyIso_inv`: coefficient naturality and
  connecting-morphism compatibility of `universalGSpaceCellularGroupCohomologyIso`.
* `MonoidHom.coinvariantsTensorChainMap_comp_universalGSpaceCellularRepStandardHomotopyEquiv_hom`,
  `MonoidHom.map_universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_linearYonedaObjMap`:
  naturality of the cellular-to-standard chain and cochain comparisons along any `φ : G →* H`.
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

section DefinitionsAndComparison

variable (k : Type u) [CommRing k] (G : Type u) [Group G] (A : Rep.{u} k G)

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
theorem universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution
    (n : ℕ) :
    (universalGSpaceCellularGroupHomologyIso k G A n).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n =
      (groupHomologyIso A n (Rep.standardResolution k G)).hom := by
  rw [universalGSpaceCellularGroupHomologyIso_hom, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
  exact (congrArg (fun f : (universalGSpaceCellularResolution k G).complex ⟶
      (Rep.standardResolution k G).complex ↦
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map f) n)
    (universalGSpaceCellularResolutionToStandard_def k G).symm).trans
    (A.groupHomologyIso_hom_comp_homologyMap
      (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
      (universalGSpaceCellularResolutionToStandard k G)
      (universalGSpaceCellularResolutionToStandard_f_zero_comp_π k G) n)

/-- Inverse form of
`universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution`. -/
@[reassoc]
theorem homologyMap_universalGSpaceCellular_comp_groupHomologyIso_standardResolution_inv
    (n : ℕ) :
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
        (universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution k G A n))

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
theorem groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular
    (n : ℕ) :
    (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n =
      (universalGSpaceCellularGroupCohomologyIso k G A n).hom :=
  let h := A.groupCohomologyIso_hom_comp_homologyMap
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G)
    (universalGSpaceCellularResolutionToStandard k G)
    (universalGSpaceCellularResolutionToStandard_f_zero_comp_π k G) n
  have heq : eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
      universalGSpaceCellularResolutionToStandard k G =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom :=
    (congrArg (eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫ ·)
      (universalGSpaceCellularResolutionToStandard_def k G)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (eqToHom_trans _ _)).trans (Category.id_comp _)
  let mEquiv : (Rep.standardResolution k G).complex.linearYonedaObj k A ⟶
      (universalGSpaceCellularComplex k G).linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op
  let mRes : (Rep.standardResolution k G).complex.linearYonedaObj k A ⟶
      (universalGSpaceCellularResolution k G).complex.linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
      (universalGSpaceCellularResolutionToStandard k G).op
  let mEq : (universalGSpaceCellularResolution k G).complex.linearYonedaObj k A ⟶
      (universalGSpaceCellularComplex k G).linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
      (eqToHom (universalGSpaceCellularResolution_complex k G).symm).op
  have hmEquiv : mEquiv = mRes ≫ mEq :=
    (congrArg (fun f : universalGSpaceCellularComplex k G ⟶ Rep.standardComplex k G ↦
        (TauCeti.ChainComplex.linearYonedaFunctor k A).map f.op) heq.symm).trans
      ((TauCeti.ChainComplex.linearYonedaFunctor k A).map_comp
        (universalGSpaceCellularResolutionToStandard k G).op
        (eqToHom (universalGSpaceCellularResolution_complex k G).symm).op)
  -- Type-annotating `mEquiv`, `mRes`, `mEq` aligns `linearYonedaFunctor` objects with
  -- `linearYonedaObj` across every `calc` step.
  calc (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap mEquiv n
      = (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
          HomologicalComplex.homologyMap (mRes ≫ mEq) n :=
        congrArg ((groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
          HomologicalComplex.homologyMap · n) hmEquiv
    _ = ((groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
          HomologicalComplex.homologyMap mRes n) ≫
          HomologicalComplex.homologyMap mEq n :=
        (congrArg ((groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫ ·)
          (HomologicalComplex.homologyMap_comp mRes mEq n)).trans
          (Category.assoc _ _ _).symm
    _ = (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
          HomologicalComplex.homologyMap mEq n :=
        congrArg (· ≫ HomologicalComplex.homologyMap mEq n) h
    _ = (universalGSpaceCellularGroupCohomologyIso k G A n).hom :=
        (universalGSpaceCellularGroupCohomologyIso_hom k G A n).symm

/-- Inverse form of
`groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular`. -/
@[reassoc]
theorem homologyMap_standardResolution_comp_universalGSpaceCellularGroupCohomologyIso_inv
    (n : ℕ) :
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
        (groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular
          k G A n))

end DefinitionsAndComparison

section Coefficients

variable {k G : Type u} [CommRing k] [Group G]

/-- **Group homology computed from Milnor's geometric cellular chains is natural in the
coefficients.** For any morphism `f : A ⟶ B` in `Rep k G`, `universalGSpaceCellularGroupHomologyIso`
carries Mathlib's `groupHomology.map (MonoidHom.id G) f n` to the map induced on homology by
`((universalGSpaceCellularComplex k G).coinvariantsTensorFunctor).map f`. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_hom_naturality
    {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) f n ≫
        (universalGSpaceCellularGroupHomologyIso k G B n).hom =
      (universalGSpaceCellularGroupHomologyIso k G A n).hom ≫
        HomologicalComplex.homologyMap
          (((universalGSpaceCellularComplex k G).coinvariantsTensorFunctor).map f) n := by
  rw [universalGSpaceCellularGroupHomologyIso_hom, universalGSpaceCellularGroupHomologyIso_hom,
    TauCeti.groupHomology.groupHomologyIso_hom_naturality_assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map f) _).naturality]

/-- Inverse form of `TauCeti.universalGSpaceCellularGroupHomologyIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_inv_naturality
    {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((universalGSpaceCellularComplex k G).coinvariantsTensorFunctor).map f) n ≫
      (universalGSpaceCellularGroupHomologyIso k G B n).inv =
      (universalGSpaceCellularGroupHomologyIso k G A n).inv ≫
        groupHomology.map (MonoidHom.id G) f n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    universalGSpaceCellularGroupHomologyIso_hom_naturality f n, Iso.inv_hom_id_assoc]

/-- **Group homology computed from Milnor's geometric cellular chains respects the coefficient long
exact sequences.** For any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `Rep k G`,
`universalGSpaceCellularGroupHomologyIso` intertwines Mathlib's connecting morphism
`groupHomology.δ` with the connecting morphism of the short exact sequence of cellular
tensor-coinvariant complexes `(Xᵢ ⊗ universalGSpaceCellularComplex k G)_G`. -/
@[reassoc]
theorem groupHomology_δ_comp_universalGSpaceCellularGroupHomologyIso_hom
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (i j : ℕ) (hij : j + 1 = i) :
    groupHomology.δ hS i j hij ≫
        (universalGSpaceCellularGroupHomologyIso k G S.X₁ j).hom =
      (universalGSpaceCellularGroupHomologyIso k G S.X₃ i).hom ≫
        ((universalGSpaceCellularComplex k G).shortExact_map_coinvariantsTensorFunctor hS).δ
          i j hij := by
  let P := universalGSpaceCellularResolution k G
  let e : P.complex ⟶ universalGSpaceCellularComplex k G :=
    eqToHom (universalGSpaceCellularResolution_complex k G)
  let Φ : S.map P.complex.coinvariantsTensorFunctor ⟶
      S.map (universalGSpaceCellularComplex k G).coinvariantsTensorFunctor :=
    { τ₁ := (((Rep.coinvariantsTensor k G).obj S.X₁).mapHomologicalComplex _).map e
      τ₂ := (((Rep.coinvariantsTensor k G).obj S.X₂).mapHomologicalComplex _).map e
      τ₃ := (((Rep.coinvariantsTensor k G).obj S.X₃).mapHomologicalComplex _).map e
      comm₁₂ := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map S.f) _).naturality
        e
      comm₂₃ := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map S.g) _).naturality
        e }
  rw [universalGSpaceCellularGroupHomologyIso_hom, universalGSpaceCellularGroupHomologyIso_hom,
    P.groupHomology_δ_comp_groupHomologyIso_hom_assoc hS i j hij, Category.assoc]
  exact congrArg ((groupHomologyIso S.X₃ i P).hom ≫ ·)
    (HomologicalComplex.HomologySequence.δ_naturality Φ
      (P.complex.shortExact_map_coinvariantsTensorFunctor hS)
      ((universalGSpaceCellularComplex k G).shortExact_map_coinvariantsTensorFunctor hS) i j hij)

/-- Inverse form of `groupHomology_δ_comp_universalGSpaceCellularGroupHomologyIso_hom`. -/
@[reassoc]
theorem δ_comp_universalGSpaceCellularGroupHomologyIso_inv
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (i j : ℕ) (hij : j + 1 = i) :
    ((universalGSpaceCellularComplex k G).shortExact_map_coinvariantsTensorFunctor hS).δ
        i j hij ≫
      (universalGSpaceCellularGroupHomologyIso k G S.X₁ j).inv =
      (universalGSpaceCellularGroupHomologyIso k G S.X₃ i).inv ≫
        groupHomology.δ hS i j hij :=
  (CommSq.mk
    (groupHomology_δ_comp_universalGSpaceCellularGroupHomologyIso_hom hS i j hij)).vert_inv.w

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the
coefficients**, inverse form: for any morphism `f : A ⟶ B` in `Rep k G`, the inverses of
`universalGSpaceCellularGroupCohomologyIso` carry the map on cellular equivariant cohomology given
by postcomposition with `f` to Mathlib's `groupCohomology.map (MonoidHom.id G) f n`. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_inv_naturality
    {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((universalGSpaceCellularComplex k G).linearYonedaObjMap k f) n ≫
      (universalGSpaceCellularGroupCohomologyIso k G B n).inv =
      (universalGSpaceCellularGroupCohomologyIso k G A n).inv ≫
        groupCohomology.map (MonoidHom.id G) f n := by
  let P := universalGSpaceCellularResolution k G
  let e : P.complex ⟶ universalGSpaceCellularComplex k G :=
    eqToHom (universalGSpaceCellularResolution_complex k G)
  let eA : (universalGSpaceCellularComplex k G).linearYonedaObj k A ⟶
      P.complex.linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map e.op
  let eB : (universalGSpaceCellularComplex k G).linearYonedaObj k B ⟶
      P.complex.linearYonedaObj k B :=
    (TauCeti.ChainComplex.linearYonedaFunctor k B).map e.op
  have hcomm :
      HomologicalComplex.homologyMap
          ((universalGSpaceCellularComplex k G).linearYonedaObjMap k f) n ≫
        HomologicalComplex.homologyMap eB n =
      HomologicalComplex.homologyMap eA n ≫
        HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k f) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k e f)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  calc HomologicalComplex.homologyMap
        ((universalGSpaceCellularComplex k G).linearYonedaObjMap k f) n ≫
        (universalGSpaceCellularGroupCohomologyIso k G B n).inv
      = (HomologicalComplex.homologyMap
          ((universalGSpaceCellularComplex k G).linearYonedaObjMap k f) n ≫
        HomologicalComplex.homologyMap eB n) ≫
        (groupCohomologyIso B n P).inv :=
        (Category.assoc _ _ _).symm
    _ = HomologicalComplex.homologyMap eA n ≫
        (HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k f) n ≫
          (groupCohomologyIso B n P).inv) :=
        (congrArg (· ≫ (groupCohomologyIso B n P).inv) hcomm).trans (Category.assoc _ _ _)
    _ = HomologicalComplex.homologyMap eA n ≫
        ((groupCohomologyIso A n P).inv ≫ groupCohomology.map (MonoidHom.id G) f n) :=
        congrArg (HomologicalComplex.homologyMap eA n ≫ ·)
          (TauCeti.Rep.groupCohomologyIso_inv_naturality f P n)
    _ = (universalGSpaceCellularGroupCohomologyIso k G A n).inv ≫
          groupCohomology.map (MonoidHom.id G) f n :=
        (Category.assoc _ _ _).symm

/-- **Group cohomology computed from Milnor's geometric cellular chains is natural in the
coefficients.** For any morphism `f : A ⟶ B` in `Rep k G`,
`universalGSpaceCellularGroupCohomologyIso` carries Mathlib's
`groupCohomology.map (MonoidHom.id G) f n` to the map on cellular equivariant cohomology given by
postcomposition with `f`. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_hom_naturality
    {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (universalGSpaceCellularGroupCohomologyIso k G B n).hom =
      (universalGSpaceCellularGroupCohomologyIso k G A n).hom ≫
        HomologicalComplex.homologyMap
          ((universalGSpaceCellularComplex k G).linearYonedaObjMap k f) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    universalGSpaceCellularGroupCohomologyIso_inv_naturality]

/-- **Group cohomology computed from Milnor's geometric cellular chains respects the coefficient
long exact sequences**, inverse form: for any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in
`Rep k G`, the inverses of `universalGSpaceCellularGroupCohomologyIso` carry the connecting
morphism of `Hom_G(universalGSpaceCellularComplex k G, Xᵢ)` to Mathlib's `groupCohomology.δ`. -/
@[reassoc]
theorem δ_comp_universalGSpaceCellularGroupCohomologyIso_inv
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    ((universalGSpaceCellularComplex k G).shortExact_map_linearYonedaObjFunctor k hS).δ
        i j hij ≫
      (universalGSpaceCellularGroupCohomologyIso k G S.X₁ j).inv =
      (universalGSpaceCellularGroupCohomologyIso k G S.X₃ i).inv ≫
        groupCohomology.δ hS i j hij :=
  let P := universalGSpaceCellularResolution k G
  let e : P.complex ⟶ universalGSpaceCellularComplex k G :=
    eqToHom (universalGSpaceCellularResolution_complex k G)
  let e₁ : (universalGSpaceCellularComplex k G).linearYonedaObj k S.X₁ ⟶
      P.complex.linearYonedaObj k S.X₁ :=
    (TauCeti.ChainComplex.linearYonedaFunctor k S.X₁).map e.op
  let e₂ : (universalGSpaceCellularComplex k G).linearYonedaObj k S.X₂ ⟶
      P.complex.linearYonedaObj k S.X₂ :=
    (TauCeti.ChainComplex.linearYonedaFunctor k S.X₂).map e.op
  let e₃ : (universalGSpaceCellularComplex k G).linearYonedaObj k S.X₃ ⟶
      P.complex.linearYonedaObj k S.X₃ :=
    (TauCeti.ChainComplex.linearYonedaFunctor k S.X₃).map e.op
  let ψ : S.map ((universalGSpaceCellularComplex k G).linearYonedaObjFunctor k) ⟶
      S.map (P.complex.linearYonedaObjFunctor k) :=
    { τ₁ := e₁
      τ₂ := e₂
      τ₃ := e₃
      comm₁₂ := (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k e S.f).symm
      comm₂₃ := (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k e S.g).symm }
  let δCell : ((universalGSpaceCellularComplex k G).linearYonedaObj k S.X₃).homology i ⟶
      ((universalGSpaceCellularComplex k G).linearYonedaObj k S.X₁).homology j :=
    ((universalGSpaceCellularComplex k G).shortExact_map_linearYonedaObjFunctor k hS).δ i j hij
  let δP : (P.complex.linearYonedaObj k S.X₃).homology i ⟶
      (P.complex.linearYonedaObj k S.X₁).homology j :=
    (P.complex.shortExact_map_linearYonedaObjFunctor k hS).δ i j hij
  have hδ : δCell ≫ HomologicalComplex.homologyMap e₁ j =
      HomologicalComplex.homologyMap e₃ i ≫ δP :=
    HomologicalComplex.HomologySequence.δ_naturality ψ
      ((universalGSpaceCellularComplex k G).shortExact_map_linearYonedaObjFunctor k hS)
      (P.complex.shortExact_map_linearYonedaObjFunctor k hS) i j hij
  calc δCell ≫ (universalGSpaceCellularGroupCohomologyIso k G S.X₁ j).inv
      = (δCell ≫ HomologicalComplex.homologyMap e₁ j) ≫ (groupCohomologyIso S.X₁ j P).inv :=
        (Category.assoc _ _ _).symm
    _ = HomologicalComplex.homologyMap e₃ i ≫ (δP ≫ (groupCohomologyIso S.X₁ j P).inv) :=
        (congrArg (· ≫ (groupCohomologyIso S.X₁ j P).inv) hδ).trans (Category.assoc _ _ _)
    _ = HomologicalComplex.homologyMap e₃ i ≫
          ((groupCohomologyIso S.X₃ i P).inv ≫ groupCohomology.δ hS i j hij) :=
        congrArg (HomologicalComplex.homologyMap e₃ i ≫ ·)
          (TauCeti.Rep.δ_comp_groupCohomologyIso_inv hS P i j hij)
    _ = (universalGSpaceCellularGroupCohomologyIso k G S.X₃ i).inv ≫
          groupCohomology.δ hS i j hij :=
        (Category.assoc _ _ _).symm

/-- **Group cohomology computed from Milnor's geometric cellular chains respects the coefficient
long exact sequences.** For any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `Rep k G`,
`universalGSpaceCellularGroupCohomologyIso` intertwines Mathlib's connecting morphism
`groupCohomology.δ` with the connecting morphism of the short exact sequence of cellular
equivariant cochain complexes `Hom_G(universalGSpaceCellularComplex k G, Xᵢ)`. -/
@[reassoc]
theorem groupCohomology_δ_comp_universalGSpaceCellularGroupCohomologyIso_hom
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hS i j hij ≫
        (universalGSpaceCellularGroupCohomologyIso k G S.X₁ j).hom =
      (universalGSpaceCellularGroupCohomologyIso k G S.X₃ i).hom ≫
        ((universalGSpaceCellularComplex k G).shortExact_map_linearYonedaObjFunctor k hS).δ
          i j hij :=
  -- Proved in term mode: `i + 1 = j` is `(ComplexShape.up ℕ).Rel i j` only by unfolding.
  (Iso.inv_comp_eq _).1 <|
    (((Iso.comp_inv_eq _).1
      (δ_comp_universalGSpaceCellularGroupCohomologyIso_inv hS i j hij)).trans
      (Category.assoc _ _ _)).symm

end Coefficients

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
  let mG : ((universalGSpaceCellularComplex k G).coinvariantsTensorObj A).homology n ⟶
      ((Rep.standardResolution k G).complex.coinvariantsTensorObj A).homology n :=
    HomologicalComplex.homologyMap
      ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) n
  let mH : ((universalGSpaceCellularComplex k H).coinvariantsTensorObj B).homology n ⟶
      ((Rep.standardResolution k H).complex.coinvariantsTensorObj B).homology n :=
    HomologicalComplex.homologyMap
      ((((Rep.coinvariantsTensor k H).obj B).mapHomologicalComplex _).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom) n
  let cCell : ((universalGSpaceCellularComplex k G).coinvariantsTensorObj A).homology n ⟶
      ((universalGSpaceCellularComplex k H).coinvariantsTensorObj B).homology n :=
    HomologicalComplex.homologyMap
      (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularComplexMap) n
  let cStd : ((Rep.standardResolution k G).complex.coinvariantsTensorObj A).homology n ⟶
      ((Rep.standardResolution k H).complex.coinvariantsTensorObj B).homology n :=
    HomologicalComplex.homologyMap
      (φ.coinvariantsTensorChainMap ξ φ.standardComplexMap) n
  have hcomm : cCell ≫ mH = mG ≫ cStd :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (φ.coinvariantsTensorChainMap_comp_universalGSpaceCellularRepStandardHomotopyEquiv_hom
          ξ)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  -- Type-annotating `mG`, `mH`, `cStd` aligns `(standardResolution k _).complex` with
  -- `standardComplex k _` across every `calc` step.
  refine (Iso.eq_comp_inv (universalGSpaceCellularGroupHomologyIso k H B n)).1 ?_
  symm
  calc ((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ cCell) ≫
        (universalGSpaceCellularGroupHomologyIso k H B n).inv
      = (universalGSpaceCellularGroupHomologyIso k G A n).hom ≫
          (cCell ≫ mH) ≫ (groupHomologyIso B n (Rep.standardResolution k H)).inv :=
        (congrArg (((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ cCell) ≫ ·)
          (homologyMap_universalGSpaceCellular_comp_groupHomologyIso_standardResolution_inv
            k H B n).symm).trans <|
          (Category.assoc _ _ _).trans
            (congrArg ((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ ·)
              (Category.assoc _ _ _).symm)
    _ = ((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ mG) ≫
          (cStd ≫ (groupHomologyIso B n (Rep.standardResolution k H)).inv) :=
        (congrArg ((universalGSpaceCellularGroupHomologyIso k G A n).hom ≫ ·)
          ((congrArg (· ≫ _) hcomm).trans (Category.assoc _ _ _))).trans
          (Category.assoc _ _ _).symm
    _ = ((groupHomologyIso A n (Rep.standardResolution k G)).hom ≫ cStd) ≫
          (groupHomologyIso B n (Rep.standardResolution k H)).inv :=
        (congrArg (· ≫ _)
          (universalGSpaceCellularGroupHomologyIso_hom_comp_homologyMap_standardResolution
            k G A n)).trans
          (Category.assoc _ _ _).symm
    _ = (groupHomology.map φ ξ n ≫ (groupHomologyIso B n (Rep.standardResolution k H)).hom) ≫
          (groupHomologyIso B n (Rep.standardResolution k H)).inv :=
        congrArg (· ≫ _) hstd.symm
    _ = groupHomology.map φ ξ n :=
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _)

/-- Inverse form of `MonoidHom.universalGSpaceCellularGroupHomologyIso_hom_naturality`. -/
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
  let mH : ((Rep.standardResolution k H).complex.linearYonedaObj k A).homology n ⟶
      ((universalGSpaceCellularComplex k H).linearYonedaObj k A).homology n :=
    HomologicalComplex.homologyMap
      ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op) n
  let mG : ((Rep.standardResolution k G).complex.linearYonedaObj k B).homology n ⟶
      ((universalGSpaceCellularComplex k G).linearYonedaObj k B).homology n :=
    HomologicalComplex.homologyMap
      ((TauCeti.ChainComplex.linearYonedaFunctor k B).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op) n
  let cCell : ((universalGSpaceCellularComplex k H).linearYonedaObj k A).homology n ⟶
      ((universalGSpaceCellularComplex k G).linearYonedaObj k B).homology n :=
    HomologicalComplex.homologyMap
      (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularComplexMap) n
  let cStd : ((Rep.standardResolution k H).complex.linearYonedaObj k A).homology n ⟶
      ((Rep.standardResolution k G).complex.linearYonedaObj k B).homology n :=
    HomologicalComplex.homologyMap
      (φ.linearYonedaObjMap ξ φ.standardComplexMap) n
  have hcomm : mH ≫ cCell = cStd ≫ mG :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n)
        (φ.map_universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_linearYonedaObjMap
          ξ)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  -- Type-annotating `mH`, `mG`, `cCell`, `cStd` aligns `linearYonedaFunctor` objects and
  -- `(standardResolution k _).complex` across every `calc` step.
  refine (Iso.eq_inv_comp (universalGSpaceCellularGroupCohomologyIso k H A n)).2 ?_
  calc (universalGSpaceCellularGroupCohomologyIso k H A n).hom ≫
        (cCell ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).inv)
      = (groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫
          (mH ≫ cCell) ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).inv :=
        (congrArg (· ≫ (cCell ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).inv))
          (groupCohomologyIso_standardResolution_hom_comp_homologyMap_universalGSpaceCellular
            k H A n).symm).trans <|
          (Category.assoc _ _ _).trans
            (congrArg ((groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫ ·)
              (Category.assoc _ _ _).symm)
    _ = (groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫
          cStd ≫ (mG ≫ (universalGSpaceCellularGroupCohomologyIso k G B n).inv) :=
        congrArg ((groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫ ·)
          ((congrArg (· ≫ _) hcomm).trans (Category.assoc _ _ _))
    _ = (groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫
          (cStd ≫ (groupCohomologyIso B n (Rep.standardResolution k G)).inv) :=
        congrArg (fun t ↦ (groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫ (cStd ≫ t))
          (homologyMap_standardResolution_comp_universalGSpaceCellularGroupCohomologyIso_inv
            k G B n)
    _ = (groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫
          ((groupCohomologyIso A n (Rep.standardResolution k H)).inv ≫
            groupCohomology.map φ ξ n) :=
        congrArg ((groupCohomologyIso A n (Rep.standardResolution k H)).hom ≫ ·) hstd
    _ = groupCohomology.map φ ξ n :=
        Iso.hom_inv_id_assoc _ _

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
