/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.ClassifyingSpace.CellMap
public import TauCeti.AlgebraicTopology.ClassifyingSpace.ChainComparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution

/-!
# Equivariant geometric cellular chains of Milnor's join

The cellular chains of `universalGSpace G`, with the simplicial CW structure, form a
projective resolution in `Rep k G`. The action is induced by actual translations of the
space, and the differential is the geometric cellular differential. This uses the original
simplicial characteristic maps, not a newly lifted CW structure.

The cellular-to-ordered chain comparison lifts to an isomorphism of complexes of
representations. Composing it with the explicit ordered join-to-bar comparison gives a
chain homotopy equivalence in `Rep k G`, before forgetting the action. Thus the inverse
and both chain homotopies are equivariant as well as the forward comparison. Every group
homomorphism induces an equivariant cellular chain map (`MonoidHom.universalGSpaceCellularChainMap`)
via its continuous map on Milnor joins.

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
        (ModuleCat.of k k) n).hom := by
  unfold universalGSpaceCellularRepresentation
  exact cellularActionRepresentation_apply _ _ _ _ _ _ _ _

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
def universalGSpaceCellularComplex : ChainComplex (Rep k G) ℕ :=
  cellularActionComplex univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k

/-- The terms are the geometric cellular chain groups with the translation action. -/
@[simp]
theorem universalGSpaceCellularComplex_X (n : ℕ) :
    (universalGSpaceCellularComplex k G).X n =
      Rep.of (universalGSpaceCellularRepresentation k G n) := by
  unfold universalGSpaceCellularComplex universalGSpaceCellularRepresentation
  exact cellularActionComplex_X _ _ _ _ _ _ _

/-- The differential is the equivariant geometric cellular differential. -/
@[simp]
theorem universalGSpaceCellularComplex_d (n : ℕ) :
    (universalGSpaceCellularComplex k G).d (n + 1) n =
      eqToHom (universalGSpaceCellularComplex_X k G (n + 1)) ≫
        universalGSpaceCellularDifferential k G n ≫
      eqToHom (universalGSpaceCellularComplex_X k G n).symm := by
  unfold universalGSpaceCellularComplex universalGSpaceCellularDifferential
  exact cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the translation action recovers the geometric cellular chain complex. -/
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
      rfl) := by
  unfold universalGSpaceCellularComplexForget₂Iso
  exact cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- Inverse components of the forgetful identification are the reverse term transports. -/
@[simp]
theorem universalGSpaceCellularComplexForget₂Iso_inv_f (n : ℕ) :
    (universalGSpaceCellularComplexForget₂Iso k G).inv.f n = eqToHom (by
      rw [Functor.mapHomologicalComplex_obj_X, universalGSpaceCellularComplex_X,
        cellularChainComplex_X]
      rfl) := by
  unfold universalGSpaceCellularComplexForget₂Iso
  exact cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

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

/-- The inverse equivariant comparison has the inverse scaled cellular-to-ordered linear map. -/
@[simp]
theorem universalGSpaceCellularRepIso_inv_toLinearMap (n : ℕ) :
    (universalGSpaceCellularRepIso k G n).inv.hom.toLinearMap =
      (universalGSpaceCellularChainLinearEquiv k G n).symm.toLinearMap := (rfl)

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

/-- The inverse component of the chain comparison is the inverse equivariant scaled basis
comparison followed by the reverse term transport. -/
@[simp]
theorem universalGSpaceCellularComplexIso_inv_f (n : ℕ) :
    (universalGSpaceCellularComplexIso k G).inv.f n =
      (universalGSpaceCellularRepIso k G n).inv ≫
        eqToHom (universalGSpaceCellularComplex_X k G n).symm := (rfl)

/-- Forgetting the group action identifies `universalGSpaceCellularComplexIso` with the
module-level cellular-to-ordered comparison `universalGSpaceCellularChainComplexIso`. -/
@[reassoc]
theorem
    universalGSpaceCellularComplexForget₂Iso_hom_comp_map_universalGSpaceCellularComplexIso_hom :
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexForget₂Iso_hom_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceCellularChainComplexIso_hom_f]
  -- Normalize the exposed ordered-chain terms before splitting the forgetful functor on `≫`.
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  rw [Functor.map_comp, eqToHom_map]
  simp only [eqToHom_trans_assoc, Rep.forget₂_moduleCat_map,
    universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.toModuleIso_hom]

/-- The inverse equivariant cellular-to-ordered comparison forgets to the inverse module-level
comparison. -/
@[reassoc]
theorem
    map_universalGSpaceCellularComplexIso_inv_comp_universalGSpaceCellularComplexForget₂Iso_inv :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        (universalGSpaceCellularComplexIso k G).inv ≫
      (universalGSpaceCellularComplexForget₂Iso k G).inv =
      (universalGSpaceCellularChainComplexIso k G).inv := by
  have h : (universalGSpaceCellularComplexForget₂Iso k G ≪≫
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).mapIso
        (universalGSpaceCellularComplexIso k G)) =
      universalGSpaceCellularChainComplexIso k G :=
    Iso.ext
      (universalGSpaceCellularComplexForget₂Iso_hom_comp_map_universalGSpaceCellularComplexIso_hom
        k G)
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using congrArg Iso.inv h

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
def universalGSpaceCellularResolution : ProjectiveResolution (Rep.trivial k G k) where
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
    Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] using
    ConcreteCategory.congr_hom
      (universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation k G) x

/-- The geometric cellular-to-bar comparison is a chain homotopy equivalence in `Rep k G`:
its inverse and both homotopies retain equivariance. -/
def universalGSpaceCellularRepStandardHomotopyEquiv :
    HomotopyEquiv (universalGSpaceCellularComplex k G) (Rep.standardComplex k G) :=
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

/-- The homotopy inverse of the equivariant cellular-to-bar comparison lifts the identity from
the standard resolution to the ordered join resolution and transports back to geometric cellular
chains. -/
@[simp]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_inv :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv =
      ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
          (universalGSpaceResolution k G) ≫
        (universalGSpaceCellularComplexIso k G).inv := by
  simp [universalGSpaceCellularRepStandardHomotopyEquiv,
    HomotopyEquiv.trans, HomotopyEquiv.ofIso]
  rfl

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
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, ← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe]
  erw [universalGSpaceCellularChainLinearEquiv_cellularChainBasis]
  exact universalGSpaceChainComplexToStandardComplex_f_hom_single k G c
    (realizationChainScale k n : k)

/-- The geometric cellular-to-bar map preserves augmentation. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_comp_π :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        (Rep.standardResolution k G).π =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom]
  exact (Category.assoc _ _ _).trans
    (congrArg ((universalGSpaceCellularComplexIso k G).hom ≫ ·)
      (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G))

/-- In degree `0`, the forward map of `universalGSpaceCellularRepStandardHomotopyEquiv` commutes
with the projective-resolution augmentations. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_zero_comp_π :
    (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom).f 0 ≫
      (Rep.standardResolution k G).π.f 0 =
      (universalGSpaceCellularResolution k G).π.f 0 :=
  (HomologicalComplex.comp_f _ _ 0).symm.trans <|
    congrArg (fun f ↦ f.f 0) <|
      (Category.assoc _ _ _).trans <|
        (congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
          (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G)).trans
          (universalGSpaceCellularResolution_π k G).symm

/-- In degree `0`, the homotopy inverse of `universalGSpaceCellularRepStandardHomotopyEquiv`
commutes with the projective-resolution augmentations. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_inv_f_zero_comp_π :
    ((universalGSpaceCellularRepStandardHomotopyEquiv k G).inv ≫
        eqToHom (universalGSpaceCellularResolution_complex k G).symm).f 0 ≫
      (universalGSpaceCellularResolution k G).π.f 0 =
      (Rep.standardResolution k G).π.f 0 := by
  have hπ : eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
      (universalGSpaceCellularResolution k G).π =
        (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
    rw [universalGSpaceCellularResolution_π, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hcomp : ((universalGSpaceCellularRepStandardHomotopyEquiv k G).inv ≫
      eqToHom (universalGSpaceCellularResolution_complex k G).symm) ≫
        (universalGSpaceCellularResolution k G).π =
      ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
          (universalGSpaceResolution k G) ≫
        (universalGSpaceResolution k G).π := by
    rw [Category.assoc, hπ, universalGSpaceCellularRepStandardHomotopyEquiv_inv]
    dsimp only [Rep.standardResolution, universalGSpaceResolution]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact (HomologicalComplex.comp_f _ _ 0).symm.trans <|
    (congrArg (fun f ↦ f.f 0) hcomp).trans <|
      (HomologicalComplex.comp_f _ _ 0).trans <|
        (ProjectiveResolution.lift_commutes_zero (𝟙 _)
          (Rep.standardResolution k G) (universalGSpaceResolution k G)).trans
          (Category.comp_id _)

/-- The explicit geometric cellular-to-bar map agrees up to equivariant chain homotopy
with Mathlib's abstract comparison of the two projective resolutions. -/
def universalGSpaceCellularStandardComparisonHomotopy :
    Homotopy (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom)
      (ProjectiveResolution.homotopyEquiv (universalGSpaceCellularResolution k G)
        (Rep.standardResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceCellularResolution k G)
    (Rep.standardResolution k G) _ (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
          (universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G)).trans
          (universalGSpaceCellularResolution_π k G).symm))

end Resolution


section CellularBasis

variable {k G H : Type u} [Ring k] [MulOne G] [MulOne H]

/-- The cellular map on Milnor's join induced by a homomorphism carries the cellular basis
vector of each simplex to that of its relabelled simplex, without an orientation sign. -/
theorem cellularChainGroupMap_universalGSpaceCellularMap_cellularChainBasis
    (φ : G →* H) {n : ℕ} (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) n
        (cellularChainBasis univ k n
          ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c)) =
      cellularChainBasis univ k n
        ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm
          (φ.universalGSpaceCellMap c)) :=
  cellularChainGroupMap_cellularChainBasis _ _ _ k
    (fun x _ hx ↦ φ.map_universalGSpaceCellularMap_realizationCellEquiv_symm c x hx)

end CellularBasis

end TauCeti

namespace MonoidHom

universe u

open TauCeti

attribute [local instance] universalGSpaceVertexOrder

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- The cellular map induced by a group homomorphism intertwines translations on the universal
subsets of Milnor's joins. -/
@[reassoc]
theorem universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap
    (φ : G →* H) (g : G) :
    universalGSpaceCellularTranslation g ≫ φ.universalGSpaceCellularMap =
      φ.universalGSpaceCellularMap ≫ universalGSpaceCellularTranslation (φ g) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  simp only [ConcreteCategory.comp_apply]
  exact (φ.universalGSpaceCellularMap_apply _).trans <|
    (congrArg φ.universalGSpaceMap (universalGSpaceCellularTranslation_apply g x)).trans <|
      (φ.universalGSpaceMap_smul g x.1).trans <|
        (congrArg (φ g • ·) (φ.universalGSpaceCellularMap_apply x).symm).trans
          (universalGSpaceCellularTranslation_apply (φ g) _).symm

/-- A group homomorphism induces an equivariant morphism on the geometric cellular chain
representations of Milnor's join, via its continuous cellular map on total spaces. -/
def universalGSpaceCellularChainHom (φ : G →* H) (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G n) ⟶
      Rep.res φ (Rep.of (universalGSpaceCellularRepresentation k H n)) :=
  cellularActionGroupMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap n

/-- Forgetting equivariance recovers the geometric cellular chain-group map of
`universalGSpaceCellularMap`. -/
@[simp]
theorem universalGSpaceCellularChainHom_hom_toLinearMap (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularChainHom (k := k) n).hom.toLinearMap =
      (cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) n).hom := by
  unfold universalGSpaceCellularChainHom
  exact cellularActionGroupMap_hom_toLinearMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- On a geometric cellular basis vector, `universalGSpaceCellularChainHom` relabels the
indexing simplex without introducing an orientation sign. -/
theorem universalGSpaceCellularChainHom_hom_cellularChainBasis (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (φ.universalGSpaceCellularChainHom (k := k) n).hom
        (cellularChainBasis univ k n
          ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c)) =
      cellularChainBasis univ k n
        ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm
          (φ.universalGSpaceCellMap c)) := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularChainHom_hom_toLinearMap]
  exact cellularChainGroupMap_universalGSpaceCellularMap_cellularChainBasis φ c

/-- The identity homomorphism induces the identity morphism on geometric cellular chain
representations. -/
@[simp]
theorem universalGSpaceCellularChainHom_id (n : ℕ) :
    (MonoidHom.id G).universalGSpaceCellularChainHom (k := k) n =
      𝟙 (Rep.of (universalGSpaceCellularRepresentation k G n)) := by
  unfold universalGSpaceCellularChainHom universalGSpaceCellularRepresentation
  exact (cellularActionGroupMap_congr _ _ _ _ _ _ _ _ _ _ _ (MonoidHom.id G)
    universalGSpaceCellularMap_id _ _ (isCellular_id univ)
    (fun g ↦ (Category.comp_id _).trans (Category.id_comp _).symm) n).trans
    (cellularActionGroupMap_id _ _ _ _ _ _ n)

/-- Induced morphisms on geometric cellular chain representations respect composition,
restricting the second morphism along the first homomorphism. -/
@[simp]
theorem universalGSpaceCellularChainHom_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) (n : ℕ) :
    (ψ.comp φ).universalGSpaceCellularChainHom (k := k) n =
      φ.universalGSpaceCellularChainHom n ≫
        (Rep.resFunctor φ).map (ψ.universalGSpaceCellularChainHom n) := by
  unfold universalGSpaceCellularChainHom universalGSpaceCellularRepresentation
  refine (cellularActionGroupMap_congr _ _ _ _ _ _ _ _ _ _ _ (ψ.comp φ)
    (universalGSpaceCellularMap_comp ψ φ) _ _
    (IsCellular.comp univ univ φ.isCellular_universalGSpaceCellularMap
      ψ.isCellular_universalGSpaceCellularMap)
    (fun g ↦ ?_) n).trans
    (cellularActionGroupMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n)
  rw [φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap_assoc,
    ψ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap, Category.assoc]
  rfl

/-- A group homomorphism induces a chain map of equivariant geometric cellular chain complexes
of Milnor's join, via its continuous cellular map on total spaces. -/
def universalGSpaceCellularChainMap (φ : G →* H) :
    universalGSpaceCellularComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularComplex k H) :=
  cellularActionComplexMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul k univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap

/-- Components of `universalGSpaceCellularChainMap` are `universalGSpaceCellularChainHom`
between the canonical geometric cellular-chain terms. -/
@[simp]
theorem universalGSpaceCellularChainMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularChainMap (k := k)).f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        φ.universalGSpaceCellularChainHom n ≫
        eqToHom (by rw [Functor.mapHomologicalComplex_obj_X,
          universalGSpaceCellularComplex_X]) := by
  unfold universalGSpaceCellularChainMap universalGSpaceCellularChainHom
    universalGSpaceCellularComplex universalGSpaceCellularRepresentation
  exact cellularActionComplexMap_f _ _ _ _ _ _ _ _ _ _ _ _ _ _ n

/-- The identity homomorphism induces the identity chain map on equivariant geometric cellular
chains. -/
@[simp]
theorem universalGSpaceCellularChainMap_id :
    (MonoidHom.id G).universalGSpaceCellularChainMap (k := k) =
      𝟙 (universalGSpaceCellularComplex k G) := by
  unfold universalGSpaceCellularChainMap universalGSpaceCellularComplex
  exact (cellularActionComplexMap_congr _ _ _ _ _ _ _ _ _ _ _ (MonoidHom.id G)
    universalGSpaceCellularMap_id _ _ (isCellular_id univ)
    (fun g ↦ (Category.comp_id _).trans (Category.id_comp _).symm)).trans
    (cellularActionComplexMap_id _ _ _ _ _ _)

/-- Equivariant geometric cellular chain maps respect composition, restricting the second chain
map along the first homomorphism. -/
@[simp]
theorem universalGSpaceCellularChainMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularChainMap (k := k) =
      φ.universalGSpaceCellularChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularChainMap := by
  unfold universalGSpaceCellularChainMap universalGSpaceCellularComplex
  refine (cellularActionComplexMap_congr _ _ _ _ _ _ _ _ _ _ _ (ψ.comp φ)
    (universalGSpaceCellularMap_comp ψ φ) _ _
    (IsCellular.comp univ univ φ.isCellular_universalGSpaceCellularMap
      ψ.isCellular_universalGSpaceCellularMap)
    (fun g ↦ ?_)).trans
    (cellularActionComplexMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  rw [φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap_assoc,
    ψ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap, Category.assoc]
  rfl

/-- Forgetting the group actions identifies `universalGSpaceCellularChainMap` with the ordinary
geometric cellular chain map of `universalGSpaceCellularMap`. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_hom_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) ≫
      (universalGSpaceCellularComplexForget₂Iso k H).hom =
      (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceCellularChainMap ≫
        ((universalGSpaceCellularComplex k H).repResForget₂Iso φ).hom := by
  unfold universalGSpaceCellularComplexForget₂Iso universalGSpaceCellularChainMap
    universalGSpaceCellularComplex
  exact cellularActionComplexForget₂Iso_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ _

end MonoidHom
