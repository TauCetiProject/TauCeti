/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.ClassifyingSpace.ChainComparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Resolution

/-!
# Equivariant geometric cellular chains of Milnor's join

The cellular chains of `universalGSpace G`, with the simplicial CW structure, form a
projective resolution in `Rep k G`. The action is induced by actual translations of the
space, and the differential is the geometric cellular differential. This uses the original
simplicial characteristic maps, not a newly lifted CW structure.

The cellular-to-ordered chain comparison lifts to an isomorphism of complexes of
representations. Composing it with the explicit ordered join-to-bar comparison gives a
chain homotopy equivalence in `Rep k G`, before forgetting the action. Thus the inverse
and both chain homotopies are equivariant as well as the forward comparison, and the forward
map intertwines the `groupHomologyIso` and `groupCohomologyIso` identifications of
`universalGSpaceCellularResolution` and `Rep.standardResolution`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections I.4 and II.4.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

section ChainComplex

variable (k : Type u) [Ring k] (G : Type u) [Group G]

/-- The action on geometric cellular chains induced by translation of Milnor's join. -/
-- Exposed as a specialization of `cellularActionRepresentation` (whose own body remains hidden)
-- so downstream change-of-group maps instantiate `cellularActionRepresentationHom` directly.
@[expose]
def universalGSpaceCellularRepresentation (n : ℕ) :
    Representation k G
      (cellularChainGroup (univ : Set (universalGSpace G)) (ModuleCat.of k k) n : ModuleCat k) :=
  cellularActionRepresentation univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k n

/-- The representation acts by the actual cellular map of translation. -/
@[simp]
theorem universalGSpaceCellularRepresentation_apply (n : ℕ) (g : G) :
    universalGSpaceCellularRepresentation k G n g =
      (cellularChainGroupMap univ univ (isCellular_universalGSpaceCellularTranslation g)
        (ModuleCat.of k k) n).hom :=
  cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The geometric cellular differential is equivariant for translation. -/
def universalGSpaceCellularDifferential (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G (n + 1)) ⟶
      Rep.of (universalGSpaceCellularRepresentation k G n) :=
  cellularActionDifferential univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k n

/-- Forgetting equivariance gives the geometric cellular differential. -/
@[simp]
theorem universalGSpaceCellularDifferential_hom_toLinearMap (n : ℕ) :
    (universalGSpaceCellularDifferential k G n).hom.toLinearMap =
      (cellularDifferential (univ : Set (universalGSpace G)) (ModuleCat.of k k) n).hom := by
  unfold universalGSpaceCellularDifferential
  exact cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- Geometric cellular chains of Milnor's join, retaining the translation action. -/
-- Exposed as a specialization of `cellularActionComplex` (whose `ChainComplex.of` body remains
-- hidden) so change-of-group maps instantiate `cellularActionComplexMap` without transports.
@[expose]
def universalGSpaceCellularComplex : ChainComplex (Rep k G) ℕ :=
  cellularActionComplex univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k

/-- The terms are the geometric cellular chain groups with the translation action. -/
@[simp]
theorem universalGSpaceCellularComplex_X (n : ℕ) :
    (universalGSpaceCellularComplex k G).X n =
      Rep.of (universalGSpaceCellularRepresentation k G n) :=
  cellularActionComplex_X _ _ _ _ _ _ _

/-- The differential is the equivariant geometric cellular differential. -/
@[simp]
theorem universalGSpaceCellularComplex_d (n : ℕ) :
    (universalGSpaceCellularComplex k G).d (n + 1) n =
      eqToHom (universalGSpaceCellularComplex_X k G (n + 1)) ≫
        universalGSpaceCellularDifferential k G n ≫
      eqToHom (universalGSpaceCellularComplex_X k G n).symm := by
  unfold universalGSpaceCellularDifferential
  exact cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the translation action recovers the geometric cellular chain complex. -/
@[expose]
def universalGSpaceCellularComplexForget₂Iso :
    cellularChainComplex (univ : Set (universalGSpace G)) (ModuleCat.of k k) ≅
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (universalGSpaceCellularComplex k G) :=
  cellularActionComplexForget₂Iso univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k

/-- The forgetful identification uses the canonical term transports. -/
@[simp]
theorem universalGSpaceCellularComplexForget₂Iso_hom_f (n : ℕ) :
    (universalGSpaceCellularComplexForget₂Iso k G).hom.f n = eqToHom (by
      rw [Functor.mapHomologicalComplex_obj_X, universalGSpaceCellularComplex_X,
        cellularChainComplex_X]
      rfl) :=
  cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- The scaled cellular-basis comparison is an isomorphism of representations, not merely
of underlying modules. -/
def universalGSpaceCellularRepIso (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G n) ≅
      Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  Rep.mkIso
    { __ := universalGSpaceCellularChainLinearEquiv k G n
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          universalGSpaceCellularRepresentation_apply] using
          universalGSpaceCellularChainLinearEquiv_translation k g n x }

/-- The equivariant comparison has the existing scaled cellular-to-ordered linear map. -/
@[simp]
theorem universalGSpaceCellularRepIso_hom_toLinearMap (n : ℕ) :
    (universalGSpaceCellularRepIso k G n).hom.hom.toLinearMap =
      (universalGSpaceCellularChainLinearEquiv k G n).toLinearMap := (rfl)

/-- Geometric and ordered cellular chains are isomorphic before forgetting the action. -/
def universalGSpaceCellularComplexIso :
    universalGSpaceCellularComplex k G ≅ universalGSpaceChainComplex k G :=
  -- The source complex has a hidden body, so its term equality must remain explicit.
  -- The ordered target already exposes its terms, and needs no transport.
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (universalGSpaceCellularComplex_X k G n) ≪≫
      universalGSpaceCellularRepIso k G n)
    fun i j hij ↦ by
      subst i
      dsimp only [universalGSpaceChainComplex]
      simp only [universalGSpaceCellularComplex_d, ChainComplex.of_d,
        Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      apply (cancel_epi (eqToHom (universalGSpaceCellularComplex_X k G (j + 1)))).mpr
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
        universalGSpaceCellularRepIso_hom_toLinearMap,
        universalGSpaceCellularDifferential_hom_toLinearMap, ModuleCat.hom_comp,
        Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom, LinearEquiv.toModuleIso_hom] using
        congrArg ModuleCat.Hom.hom
          (universalGSpaceCellularChainLinearEquiv_comp_boundary k G j)

/-- The component of the chain comparison is the equivariant scaled basis comparison. -/
@[simp]
theorem universalGSpaceCellularComplexIso_hom_f (n : ℕ) :
    (universalGSpaceCellularComplexIso k G).hom.f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        (universalGSpaceCellularRepIso k G n).hom := (rfl)

/-- Forgetting the group action intertwines the equivariant cellular-to-ordered isomorphism
with the module-level cellular-to-ordered isomorphism. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_hom_comp_map_universalGSpaceCellularComplexIso :
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom := by
  ext n : 1
  have h : (forget₂ (_root_.Rep k G) (ModuleCat k)).map
      (universalGSpaceCellularRepIso k G n).hom =
      (universalGSpaceCellularChainLinearEquiv k G n).toModuleIso.hom := by
    apply ModuleCat.hom_ext
    simp [_root_.Rep.forget₂_moduleCat_map]
  rw [HomologicalComplex.comp_f, universalGSpaceCellularComplexForget₂Iso_hom_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceCellularChainComplexIso_hom_f]
  dsimp only [universalGSpaceChainComplex, Functor.mapHomologicalComplex_obj_X]
  rw [(forget₂ (_root_.Rep k G) (ModuleCat k)).map_comp, eqToHom_map, h]
  dsimp
  simp

/-- The equivariant geometric cellular augmentation in degree zero. -/
@[expose]
def universalGSpaceCellularAugmentationHom :
    Rep.of (universalGSpaceCellularRepresentation k G 0) ⟶ Rep.trivial k G k :=
  cellularActionAugmentation univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k

/-- Forgetting equivariance gives the degree-zero cellular augmentation. -/
@[simp]
theorem universalGSpaceCellularAugmentationHom_hom_toLinearMap :
    (universalGSpaceCellularAugmentationHom k G).hom.toLinearMap =
      (cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k)).hom :=
  cellularActionAugmentation_hom_toLinearMap _ _ _ _ _ _

/-- The equivariant geometric cellular augmentation of Milnor's join, induced directly by the
geometric cellular augmentation of its simplicial CW structure. -/
@[expose]
def universalGSpaceCellularAugmentation :
    universalGSpaceCellularComplex k G ⟶
      (ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k) :=
  cellularActionComplexAugmentation univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k

/-- In degree zero, `universalGSpaceCellularAugmentation` is the equivariant cellular
augmentation up to the canonical term transport. -/
@[simp]
theorem universalGSpaceCellularAugmentation_f_zero :
    (universalGSpaceCellularAugmentation k G).f 0 =
      eqToHom (universalGSpaceCellularComplex_X k G 0) ≫
        universalGSpaceCellularAugmentationHom k G :=
  cellularActionComplexAugmentation_f_zero _ _ _ _ _ _

/-- The equivariant cellular-to-ordered isomorphism intertwines the geometric cellular
augmentation with the ordered simplicial augmentation. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_hom_comp_universalGSpaceAugmentation :
    (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G =
      universalGSpaceCellularAugmentation k G := by
  refine ((universalGSpaceCellularComplex k G).toSingle₀Equiv _).injective <| Subtype.ext ?_
  simp only [ChainComplex.toSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
    universalGSpaceCellularComplexIso_hom_f, universalGSpaceAugmentation_f_zero,
    universalGSpaceCellularAugmentation_f_zero]
  change eqToHom (universalGSpaceCellularComplex_X k G 0) ≫
      (universalGSpaceCellularRepIso k G 0).hom ≫
        permutationAugmentation k G ((indexedJoin fun _ : ℕ => G).RealizationCell 0) =
    eqToHom (universalGSpaceCellularComplex_X k G 0) ≫
      universalGSpaceCellularAugmentationHom k G
  refine congrArg (eqToHom (universalGSpaceCellularComplex_X k G 0) ≫ ·) ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext ?_
  simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    universalGSpaceCellularRepIso_hom_toLinearMap,
    universalGSpaceCellularAugmentationHom_hom_toLinearMap,
    ModuleCat.hom_comp, LinearEquiv.toModuleIso_hom, Rep.forget₂_moduleCat_map,
    ModuleCat.hom_ofHom] using
    congrArg ModuleCat.Hom.hom
      (universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation k G)

end ChainComplex

section Resolution

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- Each geometric cellular chain representation is projective, via its isomorphism
with the free ordered-chain representation. -/
instance (n : ℕ) : Projective ((universalGSpaceCellularComplex k G).X n) :=
  Projective.of_iso (HomologicalComplex.Hom.isoApp
    (universalGSpaceCellularComplexIso k G) n).symm
    ((universalGSpaceResolution k G).projective n)

/-- Geometric cellular chains with their translation action resolve the trivial module.
The augmentation is the cellular augmentation, expressed via ordered chains. -/
def universalGSpaceCellularResolution : ProjectiveResolution (_root_.Rep.trivial k G k) where
  complex := universalGSpaceCellularComplex k G
  π := (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G

/-- The resolution uses the geometric cellular complex. -/
@[simp]
theorem universalGSpaceCellularResolution_complex :
    (universalGSpaceCellularResolution k G).complex = universalGSpaceCellularComplex k G := (rfl)

/-- Its augmentation is the ordered augmentation after the equivariant cellular comparison. -/
@[simp]
theorem universalGSpaceCellularResolution_π :
    (universalGSpaceCellularResolution k G).π =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G :=
  -- The reflexive transport reduces to the identity inside this defining module; clients
  -- need it in the statement because the projective resolution's body is hidden.
  (Category.id_comp _).symm

/-- In degree zero the augmentation is the geometric cellular augmentation, not just
an abstract map to the trivial representation. -/
theorem universalGSpaceCellularResolution_π_f_zero_hom_apply
    (x : (cellularChainGroup (univ : Set (universalGSpace G))
      (ModuleCat.of k k) 0 : ModuleCat k)) :
    ((eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
        (universalGSpaceCellularResolution k G).π).f 0).hom
      ((eqToHom (universalGSpaceCellularComplex_X k G 0).symm) x) =
      cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k) x := by
  -- Evaluation cancels the transports identifying the resolution's degree-zero term with
  -- its geometric cellular chain group.
  simp only [universalGSpaceCellularResolution_π, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, HomologicalComplex.comp_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceAugmentation_f_zero]
  dsimp only [universalGSpaceChainComplex]
  erw [← ConcreteCategory.comp_apply, ← Category.assoc, ← Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp]
  -- The augmentation's codomain still carries the single₀ term's module instance. Specify
  -- the concrete composite to normalize that instance before using the linear-map API.
  change (permutationAugmentation k G ((indexedJoin fun _ : ℕ => G).RealizationCell 0)).hom
      ((universalGSpaceCellularRepIso k G 0).hom.hom x) = _
  simpa only [← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
    _root_.Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] using
    ConcreteCategory.congr_hom
      (universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation k G) x

/-- The geometric cellular-to-bar comparison is a chain homotopy equivalence in `Rep k G`:
its inverse and both homotopies retain equivariance. -/
def universalGSpaceCellularRepStandardHomotopyEquiv :
    HomotopyEquiv (universalGSpaceCellularComplex k G) (_root_.Rep.standardComplex k G) :=
  (HomotopyEquiv.ofIso (universalGSpaceCellularComplexIso k G)).trans
    (universalGSpaceStandardHomotopyEquiv k G)

/-- The equivariant comparison is the geometric-to-ordered map followed by the explicit
map forgetting the indices of the vertices. -/
@[simp]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫
        universalGSpaceChainComplexToStandardComplex k G := by
  simp [universalGSpaceCellularRepStandardHomotopyEquiv,
    HomotopyEquiv.trans, HomotopyEquiv.ofIso]

/-- A geometric cellular basis vector maps to its increasing-index tuple of labels,
scaled by the orientation unit of the simplicial cellular comparison. This is not a simp
lemma because `cellularChainBasis_apply` expands its argument first. -/
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_hom_cellularChainBasis {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    ((universalGSpaceCellularRepStandardHomotopyEquiv k G).hom.f n).hom
        ((eqToHom (universalGSpaceCellularComplex_X k G n).symm)
          (cellularChainBasis (univ : Set (universalGSpace G)) k n
            ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c))) =
      MonoidAlgebra.single (universalGSpaceCellLabels c) (realizationChainScale k n : k) := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom]
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexIso_hom_f]
  dsimp only [universalGSpaceChainComplex]
  simp only [← ConcreteCategory.comp_apply, ← Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp]
  simp only [_root_.Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, ← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe]
  erw [universalGSpaceCellularChainLinearEquiv_cellularChainBasis]
  exact universalGSpaceChainComplexToStandardComplex_f_hom_single k G c
    (realizationChainScale k n : k)

/-- The geometric cellular-to-bar map preserves augmentation. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_comp_π :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        (_root_.Rep.standardResolution k G).π =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom]
  exact (Category.assoc _ _ _).trans
    (congrArg ((universalGSpaceCellularComplexIso k G).hom ≫ ·)
      (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G))

/-- The explicit geometric cellular-to-bar chain map commutes with the augmentations of
`universalGSpaceCellularResolution` and `Rep.standardResolution`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_π :
    (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom) ≫
      (_root_.Rep.standardResolution k G).π =
    (universalGSpaceCellularResolution k G).π :=
  (Category.assoc _ _ _).trans <|
    (congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
      (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G)).trans
      (universalGSpaceCellularResolution_π k G).symm

/-- In degree zero, the explicit geometric cellular-to-bar map commutes with the augmentations
of `universalGSpaceCellularResolution` and `Rep.standardResolution`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π :
    (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).f 0 ≫
      (_root_.Rep.standardResolution k G).π.f 0 =
    (universalGSpaceCellularResolution k G).π.f 0 :=
  (HomologicalComplex.comp_f _ _ 0).symm.trans <|
    congrArg (fun f ↦ f.f 0) (universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_π k G)

/-- The explicit geometric cellular-to-bar map agrees up to equivariant chain homotopy
with Mathlib's abstract comparison of the two projective resolutions. -/
def universalGSpaceCellularStandardComparisonHomotopy :
    Homotopy (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)
      (ProjectiveResolution.homotopyEquiv (universalGSpaceCellularResolution k G)
        (_root_.Rep.standardResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceCellularResolution k G)
    (_root_.Rep.standardResolution k G) _
    (universalGSpaceCellularRepStandardHomotopyEquiv_hom_comp_π k G)

end Resolution

end TauCeti

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- The explicit geometric cellular-to-bar homotopy equivalence intertwines the group homology
identifications of `TauCeti.universalGSpaceCellularResolution` and `Rep.standardResolution`. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_hom_comp_homologyMap (n : ℕ) :
    (groupHomologyIso A n (TauCeti.universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
            (eqToHom (TauCeti.universalGSpaceCellularResolution_complex k G) ≫
              (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)) n =
      (groupHomologyIso A n (Rep.standardResolution k G)).hom :=
  A.groupHomologyIso_hom_comp_homologyMap
    (TauCeti.universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- Inverse form of
`Rep.groupHomologyIso_universalGSpaceCellularResolution_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_groupHomologyIso_standardResolution_inv (n : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map
          (eqToHom (TauCeti.universalGSpaceCellularResolution_complex k G) ≫
            (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)) n ≫
        (groupHomologyIso A n (Rep.standardResolution k G)).inv =
      (groupHomologyIso A n (TauCeti.universalGSpaceCellularResolution k G)).inv :=
  A.homologyMap_comp_groupHomologyIso_inv
    (TauCeti.universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- The explicit geometric cellular-to-bar homotopy equivalence intertwines the group
cohomology identifications of `Rep.standardResolution` and
`TauCeti.universalGSpaceCellularResolution`. -/
@[reassoc]
theorem groupCohomologyIso_standardResolution_hom_comp_homologyMap (n : ℕ) :
    (groupCohomologyIso A n (Rep.standardResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
            (eqToHom (TauCeti.universalGSpaceCellularResolution_complex k G) ≫
              (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).op) n =
      (groupCohomologyIso A n (TauCeti.universalGSpaceCellularResolution k G)).hom :=
  A.groupCohomologyIso_hom_comp_homologyMap
    (TauCeti.universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

/-- Inverse form of
`Rep.groupCohomologyIso_standardResolution_hom_comp_homologyMap`. -/
@[reassoc]
theorem homologyMap_comp_groupCohomologyIso_universalGSpaceCellularResolution_inv (n : ℕ) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
          (eqToHom (TauCeti.universalGSpaceCellularResolution_complex k G) ≫
            (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).op) n ≫
        (groupCohomologyIso A n (TauCeti.universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (Rep.standardResolution k G)).inv :=
  A.homologyMap_comp_groupCohomologyIso_inv
    (TauCeti.universalGSpaceCellularResolution k G) (Rep.standardResolution k G) _
    (TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π k G) n

end Rep
