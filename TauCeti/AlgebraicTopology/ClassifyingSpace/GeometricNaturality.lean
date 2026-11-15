/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.ChainComparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps, both on underlying module complexes (`universalGSpaceCellularChainComplexIso_naturality`)
and as chain maps of representations (`universalGSpaceCellularComplexIso_naturality`).
In particular this holds for noninjective homomorphisms: indices distinguish the
vertices within a simplex, so relabelling preserves dimension and orientation.

Composing this identification with the explicit join-to-standard and join-to-bar maps gives
equivariant chain homotopy equivalences from geometric cellular chains to Mathlib's homogeneous
standard complex and inhomogeneous bar complex whose forward maps are natural in group
homomorphisms (`universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality` and
`universalGSpaceCellularBarHomotopyEquiv_hom_naturality`).

Because the induced map `MonoidHom.universalGSpaceCellularResolutionMap` on the bundled geometric
cellular projective resolutions lies over the identity of `k`, Mathlib's `groupHomologyIso` and
`groupCohomologyIso` computed from `universalGSpaceCellularResolution` carry Mathlib's
change-of-group maps `groupHomology.map` and `groupCohomology.map` to the maps induced directly by
`MonoidHom.universalGSpaceMap` on geometric cellular chains, without passing through the bar
resolution or assuming restriction preserves projective representations.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology AbstractSimplicialComplex TauCeti

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- Reading permutation coefficients intertwines relabelling join chains with the induced
map of ordered simplicial chains. -/
@[reassoc]
theorem universalGSpaceChainComplexForget₂Iso_naturality (φ : G →* H) :
    (universalGSpaceChainComplexForget₂Iso k G).hom ≫
        orderedSimplicialChainComplexMap k φ.universalGSpaceSimplicialMap =
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceChainMap ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom ≫
        (universalGSpaceChainComplexForget₂Iso k H).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceChainComplexForget₂Iso_hom_f,
    orderedSimplicialChainComplexMap_f, Functor.mapHomologicalComplex_map_f,
    universalGSpaceChainMap_f, HomologicalComplex.repResForget₂Iso_hom_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply ModuleCat.hom_ext
  refine MonoidAlgebra.lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [universalGSpaceChainHom, universalGSpaceCellMap_def,
    OrderedSimplicialChain.map_single_of_strictMonoOn _ c
      (φ.universalGSpaceSimplicialMap_strictMonoOn c)]

/-- Cellular chains and ordered join chains are naturally identified under maps of groups.
Forgetting the restricted target action yields the usual underlying module complex. -/
@[reassoc]
theorem universalGSpaceCellularChainComplexIso_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularChainComplexIso k H).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceChainMap ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom := by
  have h := (φ.universalGSpaceSimplicialMap).cellularChainComplexRealizationIso_hom_naturality
    (fun _ c ↦ φ.universalGSpaceSimplicialMap_strictMonoOn c) k
  apply (cancel_mono (universalGSpaceChainComplexForget₂Iso k H).hom).mp
  simp only [universalGSpaceCellularChainComplexIso_def, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← φ.universalGSpaceChainComplexForget₂Iso_naturality]
  have hcell :
      cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) =
        cellularChainComplexMap univ univ
          (φ.universalGSpaceSimplicialMap).isCellular_realizationMap (ModuleCat.of k k) := by
    congr 1
    exact φ.universalGSpaceSimplicialMap_restrictPreimage.symm
  simpa only [Iso.inv_hom_id_assoc, hcell] using h

/-- **Equivariant naturality of the cellular-to-ordered join comparison.** As chain maps in
`Rep k G`, the equivariant cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularComplexIso` with the ordered-chain relabelling map
`MonoidHom.universalGSpaceChainMap`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  suffices hmap :
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (φ.universalGSpaceCellularComplexMap ≫
            ((Rep.resFunctor φ).mapHomologicalComplex _).map
              (universalGSpaceCellularComplexIso k H).hom) =
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          ((universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap) by
    ext n : 1
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom hmap n)
  apply (cancel_epi (universalGSpaceCellularComplexForget₂Iso k G).hom).mp
  apply (cancel_mono ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  have hnat :
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (((Rep.resFunctor φ).mapHomologicalComplex _).map
            (universalGSpaceCellularComplexIso k H).hom) ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom =
      ((universalGSpaceCellularComplex k H).repResForget₂Iso φ).hom ≫
        ((forget₂ (Rep k H) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom := by
    simpa only [HomologicalComplex.repResForget₂Iso_def, Iso.app_hom, Functor.comp_map] using
      ((Functor.mapHomologicalComplexCompIso
        (F := Rep.resFunctor φ) (G := forget₂ (Rep k G) (ModuleCat k))
        (H := forget₂ (Rep k H) (ModuleCat k)) (Iso.refl _) _).hom.naturality
          (universalGSpaceCellularComplexIso k H).hom)
  rw [hnat, ← φ.universalGSpaceCellularComplexForget₂Iso_naturality_assoc,
    universalGSpaceCellularComplexForget₂Iso_comp_map_universalGSpaceCellularComplexIso,
    universalGSpaceCellularComplexForget₂Iso_comp_map_universalGSpaceCellularComplexIso_assoc,
    ← φ.universalGSpaceCellularChainComplexIso_naturality]

end MonoidHom

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- Geometric cellular chains of Milnor's join are chain homotopy equivalent to the
underlying standard complex. The forward map is the cellular-to-ordered identification
followed by the explicit map that forgets the vertex indices. -/
def universalGSpaceCellularStandardHomotopyEquiv :
    HomotopyEquiv
      (cellularChainComplex (univ : Set (universalGSpace G)) (ModuleCat.of k k))
      (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (Rep.standardComplex k G)) :=
  (HomotopyEquiv.ofIso (universalGSpaceCellularChainComplexIso k G)).trans
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomotopyEquiv
      (universalGSpaceStandardHomotopyEquiv k G))

/-- The geometric-to-bar comparison factors through the ordered-chain comparison. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_hom :
    (universalGSpaceCellularStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceChainComplexToStandardComplex k G) := by
  simp [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv]

/-- The inverse comparison is the abstract projective lift back to ordered join chains,
followed by the inverse cellular-chain identification. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_inv :
    (universalGSpaceCellularStandardHomotopyEquiv k G).inv =
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
            (universalGSpaceResolution k G)) ≫
        (universalGSpaceCellularChainComplexIso k G).inv := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv, universalGSpaceStandardHomotopyEquiv_inv]
  -- The two projective lifts carry the definitionally equal augmentation targets of the
  -- join and standard resolutions. Reflexivity identifies these implicit object arguments.
  rfl

end TauCeti

namespace MonoidHom

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The explicit geometric cellular-to-bar comparison is natural for every group
homomorphism, with the cellular map induced by its actual continuous map on Milnor joins. -/
@[reassoc]
theorem universalGSpaceCellularStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularStandardHomotopyEquiv k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.standardComplexMap ≫
        ((Rep.standardComplex k H).repResForget₂Iso φ).hom := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv_hom, Category.assoc,
    universalGSpaceCellularChainComplexIso_naturality_assoc]
  simp only [HomologicalComplex.repResForget₂Iso_def, Iso.app_hom]
  rw [← (Functor.mapHomologicalComplexCompIso
    (F := Rep.resFunctor φ) (G := forget₂ (Rep k G) (ModuleCat k))
    (H := forget₂ (Rep k H) (ModuleCat k)) (Iso.refl _) _).hom.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Functor.map_comp_assoc]

/-- **Equivariant naturality of the geometric cellular-to-standard comparison.** As chain maps in
`Rep k G`, the cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularRepStandardHomotopyEquiv` with `MonoidHom.standardComplexMap`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    universalGSpaceCellularComplexIso_naturality_assoc,
    universalGSpaceChainComplexToStandardComplex_naturality, Category.assoc]

/-- **Equivariant naturality of the geometric cellular-to-bar comparison.** As chain maps in
`Rep k G`, the cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularBarHomotopyEquiv` with the bar relabelling map
`TauCeti.Rep.barComplex.resChainMap`. -/
@[reassoc]
theorem universalGSpaceCellularBarHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularBarHomotopyEquiv k H).hom =
      (universalGSpaceCellularBarHomotopyEquiv k G).hom ≫
        TauCeti.Rep.barComplex.resChainMap φ := by
  rw [universalGSpaceCellularBarHomotopyEquiv_hom_eq,
    universalGSpaceCellularBarHomotopyEquiv_hom_eq, Functor.map_comp,
    universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality_assoc,
    φ.barComplex_isoStandardComplex_inv_naturality, Category.assoc]

/-- The equivariant chain map on the bundled geometric cellular projective resolutions induced by
`MonoidHom.universalGSpaceMap`. -/
def universalGSpaceCellularResolutionMap (φ : G →* H) :
    (universalGSpaceCellularResolution k G).complex ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularResolution k H).complex :=
  eqToHom (universalGSpaceCellularResolution_complex k G) ≫
    φ.universalGSpaceCellularComplexMap ≫
    eqToHom (congrArg ((Rep.resFunctor φ).mapHomologicalComplex _).obj
      (universalGSpaceCellularResolution_complex k H).symm)

/-- `universalGSpaceCellularResolutionMap` is `universalGSpaceCellularComplexMap` transported
along `universalGSpaceCellularResolution_complex`. -/
theorem universalGSpaceCellularResolutionMap_eq (φ : G →* H) :
    φ.universalGSpaceCellularResolutionMap (k := k) =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        φ.universalGSpaceCellularComplexMap ≫
        eqToHom (congrArg ((Rep.resFunctor φ).mapHomologicalComplex _).obj
          (universalGSpaceCellularResolution_complex k H).symm) :=
  (rfl)

/-- The identity homomorphism induces the identity map on geometric cellular projective
resolutions. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_id :
    (MonoidHom.id G).universalGSpaceCellularResolutionMap (k := k) =
      𝟙 (universalGSpaceCellularResolution k G).complex :=
  -- Restriction along `MonoidHom.id G` fixes `universalGSpaceCellularComplex k G` at default
  -- transparency; term-mode `Eq.trans` avoids `rw`'s implicit-transparency check on the codomain.
  (congrArg (fun f ↦ eqToHom (universalGSpaceCellularResolution_complex k G) ≫ f ≫
      eqToHom (universalGSpaceCellularResolution_complex k G).symm)
    (universalGSpaceCellularComplexMap_id (k := k) (G := G))).trans <|
    (congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
      (Category.id_comp _)).trans <|
      (eqToHom_trans _ _).trans (eqToHom_refl _ _)

/-- Geometric cellular projective-resolution maps respect composition of group homomorphisms. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularResolutionMap (k := k) =
      φ.universalGSpaceCellularResolutionMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularResolutionMap := by
  simp only [universalGSpaceCellularResolutionMap_eq, universalGSpaceCellularComplexMap_comp,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  -- Unfolding `Rep.resFunctor` identifies restriction along `ψ.comp φ` with sequential
  -- restriction along `ψ` then `φ`, so the trailing `eqToHom` transports agree by proof
  -- irrelevance.
  rfl

/-- **The geometric cellular projective-resolution map lies over the identity of `k`.** No
hypothesis on restriction preserving projective objects is needed. -/
@[reassoc]
theorem universalGSpaceCellularResolutionMap_f_zero_comp_π (φ : G →* H) :
    (φ.universalGSpaceCellularResolutionMap (k := k)).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) =
      (universalGSpaceCellularResolution k G).π.f 0 := by
  let βG : (universalGSpaceCellularResolution k G).complex ⟶ Rep.barComplex k G :=
    eqToHom (universalGSpaceCellularResolution_complex k G) ≫
      (universalGSpaceCellularBarHomotopyEquiv k G).hom
  let βH : (universalGSpaceCellularResolution k H).complex ⟶ Rep.barComplex k H :=
    eqToHom (universalGSpaceCellularResolution_complex k H) ≫
      (universalGSpaceCellularBarHomotopyEquiv k H).hom
  have hsq : φ.universalGSpaceCellularResolutionMap ≫
      ((Rep.resFunctor φ).mapHomologicalComplex _).map βH =
        βG ≫ TauCeti.Rep.barComplex.resChainMap φ := by
    simp only [universalGSpaceCellularResolutionMap_eq, βG, βH, Functor.map_comp,
      eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      universalGSpaceCellularBarHomotopyEquiv_hom_naturality]
  have hπG : (universalGSpaceCellularResolution k G).π = βG ≫ (Rep.barResolution k G).π := by
    rw [universalGSpaceCellularResolution_π, ← universalGSpaceCellularBarHomotopyEquiv_comp_π]
    exact (Category.assoc _ _ _).symm
  have hπH : (universalGSpaceCellularResolution k H).π = βH ≫ (Rep.barResolution k H).π := by
    rw [universalGSpaceCellularResolution_π, ← universalGSpaceCellularBarHomotopyEquiv_comp_π]
    exact (Category.assoc _ _ _).symm
  have hπG₀ : (universalGSpaceCellularResolution k G).π.f 0 =
      βG.f 0 ≫ (Rep.barResolution k G).π.f 0 :=
    (HomologicalComplex.congr_hom hπG 0).trans (HomologicalComplex.comp_f _ _ 0)
  have hmapH : (Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) =
      (Rep.resFunctor φ).map (βH.f 0) ≫
        (Rep.resFunctor φ).map ((Rep.barResolution k H).π.f 0) :=
    (congrArg (Rep.resFunctor φ).map
      ((HomologicalComplex.congr_hom hπH 0).trans (HomologicalComplex.comp_f _ _ 0))).trans
      ((Rep.resFunctor φ).map_comp _ _)
  -- The restricted trivial representation of `H` agrees with the trivial representation of `G`
  -- by unfolding `Rep.resFunctor`, so the outer equality is assembled in term mode.
  exact (congrArg ((φ.universalGSpaceCellularResolutionMap (k := k)).f 0 ≫ ·) hmapH).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (Rep.resFunctor φ).map ((Rep.barResolution k H).π.f 0))
        ((HomologicalComplex.comp_f _ _ 0).symm.trans
          ((HomologicalComplex.congr_hom hsq 0).trans
            (HomologicalComplex.comp_f _ _ 0)))).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (βG.f 0 ≫ ·)
            (TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π φ)).trans
            hπG₀.symm

/-- Comparing from Mathlib's bar resolution before applying the geometric cellular chain map of
`MonoidHom.universalGSpaceMap` is equivariantly chain homotopic to first relabelling the bar
resolution and then comparing to geometric cellular chains. -/
def universalGSpaceCellularBarResolutionComparisonHomotopy (φ : G →* H) :
    Homotopy
      (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G)
          (universalGSpaceCellularResolution k G) ≫
        φ.universalGSpaceCellularResolutionMap)
      (TauCeti.Rep.barComplex.resChainMap φ ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H)
            (universalGSpaceCellularResolution k H))) :=
  φ.barResolutionComparisonHomotopy (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π

/-- **Group homology computed from the geometric cellular chains of Milnor's join is natural in the
group.** Mathlib's `groupHomologyIso` intertwines `groupHomology.map` with the map induced on
tensor coinvariants by `MonoidHom.universalGSpaceMap`. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_hom_naturality
    {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    groupHomology.map φ ξ n ≫
        (groupHomologyIso B n (universalGSpaceCellularResolution k H)).hom =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n :=
  φ.groupHomologyIso_hom_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- The inverse group-homology identifications for `universalGSpaceCellularResolution` are also
natural in the group. -/
@[reassoc]
theorem universalGSpaceCellularGroupHomologyIso_inv_naturality
    {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
      (groupHomologyIso B n (universalGSpaceCellularResolution k H)).inv =
    (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv ≫
      groupHomology.map φ ξ n :=
  φ.groupHomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- **Group cohomology computed from the geometric cellular chains of Milnor's join is natural in
the group.** Mathlib's `groupCohomologyIso` intertwines the map induced on equivariant cellular
cochains by `MonoidHom.universalGSpaceMap` with `groupCohomology.map`. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_inv_naturality
    {A : Rep.{u} k H} {B : Rep.{u} k G} (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
      (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).inv =
    (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).inv ≫
      groupCohomology.map φ ξ n :=
  φ.groupCohomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- The forward group-cohomology identifications for `universalGSpaceCellularResolution` are also
natural in the group. -/
@[reassoc]
theorem universalGSpaceCellularGroupCohomologyIso_hom_naturality
    {A : Rep.{u} k H} {B : Rep.{u} k G} (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).hom =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).hom ≫
        HomologicalComplex.homologyMap
          (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularResolutionMap) n :=
  φ.groupCohomologyIso_hom_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

end MonoidHom
