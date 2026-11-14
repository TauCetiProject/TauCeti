/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps. In particular this holds for noninjective homomorphisms: indices distinguish the
vertices within a simplex, so relabelling preserves dimension and orientation.

Composing this identification with the explicit join-to-bar map gives a chain homotopy
equivalence from geometric cellular chains to the underlying module complex of Mathlib's
standard complex, whose forward map is natural in group homomorphisms.
The cellular basis of a simplex maps to its increasing-index tuple of group labels,
multiplied by the orientation unit `realizationChainScale` in that dimension.

The geometric naturality square is the instance of
`SimplicialMap.cellularChainComplexRealizationIso_hom_naturality` for the relabelling
map `MonoidHom.universalGSpaceSimplicialMap`. Retaining the translation actions upgrades both
the cellular-to-ordered isomorphism (`MonoidHom.universalGSpaceCellularComplexIso_hom_naturality`)
and the cellular-to-bar homotopy equivalence
(`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality`,
`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquivInvNaturalityHomotopy`) to naturality in
`Rep k G`, identifying the topological cellular and algebraic standard computations of group
homology and group cohomology compatibly with change of groups.

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

end MonoidHom

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

section Ring

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- In each degree, the equivariant cellular-to-ordered representation isomorphism intertwines
the cellular chain map of `universalGSpaceCellularMap` with simplex relabelling. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_hom_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularChainHom (k := k) n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).hom =
      (universalGSpaceCellularRepIso k G n).hom ≫ φ.universalGSpaceChainHom n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ n).symm.surjective i
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Rep.resMap_hom_toLinearMap, universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe,
    Representation.IntertwiningMap.toLinearMap_apply]
  rw [φ.universalGSpaceCellularChainHom_hom_cellularChainBasis c,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    MulActionHom.toRepRes_hom_single]

/-- Inverse form of `MonoidHom.universalGSpaceCellularRepIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_inv_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceChainHom (k := k) n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).inv =
      (universalGSpaceCellularRepIso k G n).inv ≫ φ.universalGSpaceCellularChainHom n := by
  rw [← cancel_epi (universalGSpaceCellularRepIso k G n).hom, Iso.hom_inv_id_assoc,
    ← φ.universalGSpaceCellularRepIso_hom_naturality_assoc n, ← (Rep.resFunctor φ).map_comp,
    Iso.hom_inv_id, (Rep.resFunctor φ).map_id, Category.comp_id]

/-- Equivariant geometric cellular chains and ordered join chains are naturally isomorphic in
`Rep k G` along every group homomorphism. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularChainMap_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceChainMap_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  rw [_root_.Rep.resMap_comp, _root_.Rep.resMap_eqToHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg (eqToHom (universalGSpaceCellularComplex_X k G n) ≫ ·)
    (φ.universalGSpaceCellularRepIso_hom_naturality n)

/-- Inverse form of `MonoidHom.universalGSpaceCellularComplexIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_inv_naturality (φ : G →* H) :
    φ.universalGSpaceChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).inv =
      (universalGSpaceCellularComplexIso k G).inv ≫ φ.universalGSpaceCellularChainMap := by
  rw [← cancel_epi (universalGSpaceCellularComplexIso k G).hom, Iso.hom_inv_id_assoc,
    ← φ.universalGSpaceCellularComplexIso_hom_naturality_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The equivariant geometric cellular chain map commutes with the cellular augmentations into the
degree-`0` trivial complexes. -/
@[reassoc]
theorem universalGSpaceCellularChainMap_comp_augmentation (φ : G →* H) :
    φ.universalGSpaceCellularChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ((universalGSpaceCellularComplexIso k H).hom ≫ universalGSpaceAugmentation k H) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor φ) _ 0).hom.app
          (Rep.trivial k H k) =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [Functor.map_comp, Category.assoc,
    φ.universalGSpaceCellularComplexIso_hom_naturality_assoc,
    φ.universalGSpaceChainMap_comp_augmentation]
  rfl

end Ring

end MonoidHom

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- Forgetting the translation action expresses the forward map of
`universalGSpaceCellularRepStandardHomotopyEquiv` via
`universalGSpaceCellularStandardHomotopyEquiv`. -/
@[reassoc]
theorem map_universalGSpaceCellularRepStandardHomotopyEquiv_hom :
    ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularComplexForget₂Iso k G).inv ≫
        (universalGSpaceCellularStandardHomotopyEquiv k G).hom := by
  have h :=
    universalGSpaceCellularComplexForget₂Iso_hom_comp_map_universalGSpaceCellularComplexIso_hom k G
  rw [Iso.eq_inv_comp, universalGSpaceCellularRepStandardHomotopyEquiv_hom,
    CategoryTheory.Functor.map_comp, ← Category.assoc, h,
    universalGSpaceCellularStandardHomotopyEquiv_hom]

/-- Forgetting the translation action expresses the homotopy inverse of
`universalGSpaceCellularRepStandardHomotopyEquiv` via
`universalGSpaceCellularStandardHomotopyEquiv`. -/
@[reassoc]
theorem map_universalGSpaceCellularRepStandardHomotopyEquiv_inv :
    ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv =
      (universalGSpaceCellularStandardHomotopyEquiv k G).inv ≫
        (universalGSpaceCellularComplexForget₂Iso k G).hom := by
  rw [← Iso.comp_inv_eq]
  let F := (forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex (ComplexShape.down ℕ)
  have h := universalGSpaceCellularRepStandardHomotopyEquiv_inv k G
  have hinv :=
    map_universalGSpaceCellularComplexIso_inv_comp_universalGSpaceCellularComplexForget₂Iso_inv k G
  exact (congrArg (· ≫ _) (congrArg F.map h)).trans <|
    (congrArg (· ≫ _) (F.map_comp _ _)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) hinv).trans
          (universalGSpaceCellularStandardHomotopyEquiv_inv k G).symm

/-- Group homology computed from the geometric cellular resolution of Milnor's join agrees with
that computed from Mathlib's standard resolution via the explicit cellular-to-bar comparison. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_hom_comp_homologyMap
    (A : Rep.{u} k G) (n : ℕ) :
    (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
              (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)) n =
      (groupHomologyIso A n (Rep.standardResolution k G)).hom :=
  _root_.Rep.groupHomologyIso_hom_comp_homologyMap A (universalGSpaceCellularResolution k G)
    (Rep.standardResolution k G) _
    (universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- Inverse form of `groupHomologyIso_universalGSpaceCellularResolution_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_groupHomologyIso_standardResolution_inv
    (A : Rep.{u} k G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)) n ≫
      (groupHomologyIso A n (Rep.standardResolution k G)).inv =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv :=
  _root_.Rep.homologyMap_comp_groupHomologyIso_inv A (universalGSpaceCellularResolution k G)
    (Rep.standardResolution k G) _
    (universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- Group cohomology computed from the geometric cellular resolution of Milnor's join agrees with
that computed from Mathlib's standard resolution via precomposition with the explicit
cellular-to-bar comparison. -/
@[reassoc]
theorem groupCohomologyIso_standardResolution_hom_comp_homologyMap
    (A : Rep.{u} k G) (n : ℕ) :
    (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
              (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).op) n =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).hom :=
  _root_.Rep.groupCohomologyIso_hom_comp_homologyMap A
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- Inverse form of `groupCohomologyIso_standardResolution_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_groupCohomologyIso_universalGSpaceCellularResolution_inv
    (A : Rep.{u} k G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
          (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
            (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).op) n ≫
      (groupCohomologyIso A n (universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (Rep.standardResolution k G)).inv :=
  _root_.Rep.homologyMap_comp_groupCohomologyIso_inv A
    (universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

end TauCeti

namespace MonoidHom

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- **Equivariant geometric naturality of the Milnor-join-to-bar comparison.** For every group
homomorphism `φ : G →* H`, the explicit comparison from geometric cellular chains of Milnor's join
to Mathlib's standard resolution commutes strictly in `Rep k G` with the cellular chain map induced
by `φ.universalGSpaceCellularMap` and the relabelling map `φ.standardComplexMap`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom,
    universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    φ.universalGSpaceCellularComplexIso_hom_naturality_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Category.assoc]

/-- The homotopy inverse of `TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv` commutes up
to equivariant chain homotopy with the geometric cellular chain map of `universalGSpaceCellularMap`
and the relabelling map on the standard resolution. -/
def universalGSpaceCellularRepStandardHomotopyEquivInvNaturalityHomotopy (φ : G →* H) :
    Homotopy
      ((universalGSpaceCellularRepStandardHomotopyEquiv k G).inv ≫
        φ.universalGSpaceCellularChainMap)
      (φ.standardComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).inv) :=
  have hinv (K : Type u) [Group K] :
      (universalGSpaceCellularRepStandardHomotopyEquiv k K).inv =
        (universalGSpaceStandardHomotopyEquiv k K).inv ≫
          (universalGSpaceCellularComplexIso k K).inv := by
    rw [universalGSpaceCellularRepStandardHomotopyEquiv_inv,
      universalGSpaceStandardHomotopyEquiv_inv]
    rfl
  (Homotopy.ofEq <| by
    rw [hinv G, Category.assoc,
      ← φ.universalGSpaceCellularComplexIso_inv_naturality, Category.assoc]).trans <|
    ((φ.universalGSpaceStandardHomotopyEquivInvNaturalityHomotopy (k := k)).compRight
      (((Rep.resFunctor φ).mapHomologicalComplex _).map
        (universalGSpaceCellularComplexIso k H).inv)).trans <|
      Homotopy.ofEq <| by
        rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← hinv H]

/-- The equivariant geometric cellular chain map of `φ : G →* H`, viewed as a chain map on the
projective resolution `universalGSpaceCellularResolution`. -/
def universalGSpaceCellularResolutionMap (φ : G →* H) :
    (universalGSpaceCellularResolution k G).complex ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularResolution k H).complex :=
  eqToHom (universalGSpaceCellularResolution_complex k G) ≫
    φ.universalGSpaceCellularChainMap ≫
    eqToHom (by rw [universalGSpaceCellularResolution_complex])

/-- Unfolding `universalGSpaceCellularResolutionMap` in terms of `universalGSpaceCellularChainMap`
and the canonical complex transports. -/
theorem universalGSpaceCellularResolutionMap_def (φ : G →* H) :
    φ.universalGSpaceCellularResolutionMap (k := k) =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        φ.universalGSpaceCellularChainMap ≫
        eqToHom (by rw [universalGSpaceCellularResolution_complex]) :=
  (rfl)

/-- The identity homomorphism induces the identity chain map on
`universalGSpaceCellularResolution`. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_id :
    (MonoidHom.id G).universalGSpaceCellularResolutionMap (k := k) =
      𝟙 (universalGSpaceCellularResolution k G).complex := by
  rw [universalGSpaceCellularResolutionMap_def, universalGSpaceCellularChainMap_id]
  exact (congrArg (eqToHom _ ≫ ·) (Category.id_comp _)).trans
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- Induced chain maps on `universalGSpaceCellularResolution` respect composition. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularResolutionMap (k := k) =
      φ.universalGSpaceCellularResolutionMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularResolutionMap := by
  simp only [universalGSpaceCellularResolutionMap_def, universalGSpaceCellularChainMap_comp,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  exact congrArg (eqToHom _ ≫ ·) (Category.assoc _ _ _)

/-- `universalGSpaceCellularResolutionMap` commutes with the projective-resolution augmentations
into the degree-`0` trivial complexes. -/
@[reassoc]
theorem universalGSpaceCellularResolutionMap_comp_π (φ : G →* H) :
    φ.universalGSpaceCellularResolutionMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularResolution k H).π ≫
        (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor φ) _ 0).hom.app
          (Rep.trivial k H k) =
      (universalGSpaceCellularResolution k G).π := by
  rw [universalGSpaceCellularResolutionMap_def, universalGSpaceCellularResolution_π,
    universalGSpaceCellularResolution_π, Functor.map_comp, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    φ.universalGSpaceCellularChainMap_comp_augmentation]
  rfl

/-- In degree `0`, `universalGSpaceCellularResolutionMap` commutes with the projective-resolution
augmentations. -/
@[reassoc]
theorem universalGSpaceCellularResolutionMap_f_zero_comp_π (φ : G →* H) :
    (φ.universalGSpaceCellularResolutionMap (k := k)).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) =
      (universalGSpaceCellularResolution k G).π.f 0 := by
  have h := congrArg (fun f ↦ f.f 0) (φ.universalGSpaceCellularResolutionMap_comp_π (k := k))
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv] at h
  have h1 :
      (_root_.Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) ≫
        (_root_.Rep.resFunctor φ).map
          (𝟙 (((HomologicalComplex.single (_root_.Rep k H) (ComplexShape.down ℕ) 0).obj
            (_root_.Rep.trivial k H k)).X 0)) ≫
        𝟙 (((HomologicalComplex.single (_root_.Rep k G) (ComplexShape.down ℕ) 0).obj
          (_root_.Rep.res φ (_root_.Rep.trivial k H k))).X 0) =
      (_root_.Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) :=
    (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Category.comp_id _)
  exact (congrArg ((φ.universalGSpaceCellularResolutionMap).f 0 ≫ ·) h1.symm).trans h

/-- On tensor-coinvariant chain complexes, the explicit cellular-to-bar comparison intertwines
change of groups along `universalGSpaceCellularChainMap` and along `standardComplexMap`. -/
@[reassoc]
theorem coinvariantsTensorChainMap_universalGSpaceCellularRepStandardHomotopyEquiv_hom
    {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : G →* H) (ξ : A ⟶ Rep.res φ B) :
    φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularChainMap ≫
        (((Rep.coinvariantsTensor k H).obj B).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        φ.coinvariantsTensorChainMap ξ φ.standardComplexMap := by
  rw [φ.coinvariantsTensorChainMap_comp_mapHomologicalComplex_map,
    φ.mapHomologicalComplex_map_comp_coinvariantsTensorChainMap,
    φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality]

/-- On equivariant cochain complexes, precomposition with the explicit cellular-to-bar comparison
intertwines change of groups along `universalGSpaceCellularChainMap` and along
`standardComplexMap`. -/
@[reassoc]
theorem linearYonedaObjMap_universalGSpaceCellularRepStandardHomotopyEquiv_hom
    {A : Rep.{u} k H} {B : Rep.{u} k G} (φ : G →* H) (ξ : Rep.res φ A ⟶ B) :
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom.op ≫
      φ.linearYonedaObjMap ξ φ.universalGSpaceCellularChainMap =
      φ.linearYonedaObjMap ξ φ.standardComplexMap ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k B).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.op :=
  (φ.linearYonedaFunctor_map_comp_linearYonedaObjMap ξ φ.universalGSpaceCellularChainMap
    (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom).trans <|
    (congrArg (φ.linearYonedaObjMap ξ)
      φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality).trans
      (φ.linearYonedaObjMap_comp_linearYonedaFunctor_map ξ φ.standardComplexMap
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).symm

/-- **Group homology computed via the geometric cellular resolution of Milnor's join is natural in
the group.** For every `φ : G →* H` and compatible coefficient map `ξ : A ⟶ Res(φ)(B)`,
`groupHomologyIso` intertwines `groupHomology.map φ ξ` with the homology map induced on tensor
coinvariants by `φ.universalGSpaceCellularResolutionMap`. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_hom_naturality
    {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    groupHomology.map φ ξ n ≫
        (groupHomologyIso B n (universalGSpaceCellularResolution k H)).hom =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n :=
  φ.groupHomologyIso_hom_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- Inverse form of `MonoidHom.groupHomologyIso_universalGSpaceCellularResolution_hom_naturality`.
-/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_inv_naturality
    {A : Rep.{u} k G} {B : Rep.{u} k H} (φ : G →* H) (ξ : A ⟶ Rep.res φ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
      (groupHomologyIso B n (universalGSpaceCellularResolution k H)).inv =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv ≫
        groupHomology.map φ ξ n :=
  φ.groupHomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- **Group cohomology computed via the geometric cellular resolution of Milnor's join is natural
in the group.** For every `φ : G →* H` and compatible coefficient map `ξ : Res(φ)(A) ⟶ B`,
`groupCohomologyIso` intertwines `groupCohomology.map φ ξ` with the cohomology map induced on
equivariant cochains by `φ.universalGSpaceCellularResolutionMap`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellularResolution_inv_naturality
    {A : Rep.{u} k H} {B : Rep.{u} k G} (φ : G →* H) (ξ : Rep.res φ A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
      (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).inv ≫
        groupCohomology.map φ ξ n :=
  φ.groupCohomologyIso_inv_naturality ξ (universalGSpaceCellularResolution k G)
    (universalGSpaceCellularResolution k H) φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- Forward form of
`MonoidHom.groupCohomologyIso_universalGSpaceCellularResolution_inv_naturality`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellularResolution_hom_naturality
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
