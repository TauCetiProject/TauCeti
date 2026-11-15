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
and both chain homotopies are equivariant as well as the forward comparison.

A group homomorphism `φ : G →* H` induces a cellular map `MonoidHom.universalGSpaceCellularMap`
intertwining the translation actions, hence an equivariant cellular chain map
`MonoidHom.universalGSpaceCellularComplexMap` to the restricted target complex. Each cellular
basis vector maps directly to the cellular basis vector of the relabelled simplex, without an
orientation sign.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections I.4 and II.4.
* A. Hatcher, *Algebraic Topology*, Section 2.2.
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

/-- The inverse equivariant comparison has the inverse scaled linear equivalence. -/
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

/-- The inverse component of the chain comparison is the inverse representation comparison
followed by the reverse term transport. -/
@[simp]
theorem universalGSpaceCellularComplexIso_inv_f (n : ℕ) :
    (universalGSpaceCellularComplexIso k G).inv.f n =
      (universalGSpaceCellularRepIso k G n).inv ≫
        eqToHom (universalGSpaceCellularComplex_X k G n).symm := (rfl)

/-- Forgetting the translation action intertwines the equivariant cellular-to-ordered chain
isomorphism with the underlying module-level comparison
`universalGSpaceCellularChainComplexIso`. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom :
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexForget₂Iso_hom_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceCellularChainComplexIso_hom_f, LinearEquiv.toModuleIso_hom]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  rw [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc]
  simp only [Rep.forget₂_moduleCat_map, universalGSpaceCellularRepIso_hom_toLinearMap]

/-- Isomorphism form of
`universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom`. -/
theorem universalGSpaceCellularComplexForget₂Iso_trans_mapIso_cellularComplexIso :
    universalGSpaceCellularComplexForget₂Iso k G ≪≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).mapIso
          (universalGSpaceCellularComplexIso k G) =
      universalGSpaceCellularChainComplexIso k G :=
  Iso.ext (universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom k G)

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

/-- The equivariant inverse comparison is the projective lift back to ordered join chains
followed by the inverse equivariant cellular comparison. -/
@[simp]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_inv :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv =
      ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
          (universalGSpaceResolution k G) ≫
        (universalGSpaceCellularComplexIso k G).inv := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, universalGSpaceStandardHomotopyEquiv_inv]
  -- The two projective lifts carry the definitionally equal augmentation targets of the
  -- join and standard resolutions. Reflexivity identifies these implicit object arguments.
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

end TauCeti

namespace MonoidHom

open AbstractSimplicialComplex TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

section Equivariance

variable {G H : Type u} [Group G] [Group H]

/-- The universal-subset cellular map of Milnor joins intertwines translation by `g` with
translation by `φ g`. -/
@[reassoc]
theorem universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap
    (φ : G →* H) (g : G) :
    universalGSpaceCellularTranslation g ≫ φ.universalGSpaceCellularMap =
      φ.universalGSpaceCellularMap ≫ universalGSpaceCellularTranslation (φ g) := by
  refine TopCat.ext fun x ↦ Subtype.ext ?_
  rw [TopCat.comp_app, TopCat.comp_app, φ.universalGSpaceCellularMap_apply,
    universalGSpaceCellularTranslation_apply, universalGSpaceCellularTranslation_apply,
    φ.universalGSpaceCellularMap_apply, φ.universalGSpaceMap_smul]

end Equivariance

section Ring

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- The morphism of geometric cellular chain representations induced by a group homomorphism,
with the target translation action restricted along the homomorphism. -/
def universalGSpaceCellularRepresentationMap (φ : G →* H) (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G n) ⟶
      Rep.res φ (Rep.of (universalGSpaceCellularRepresentation k H n)) :=
  cellularActionRepresentationMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap k n

/-- Forgetting equivariance recovers the geometric cellular chain-group map induced by the
continuous map of Milnor joins. -/
@[simp]
theorem universalGSpaceCellularRepresentationMap_hom_toLinearMap (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularRepresentationMap (k := k) n).hom.toLinearMap =
      (cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) n).hom := by
  unfold universalGSpaceCellularRepresentationMap
  exact cellularActionRepresentationMap_hom_toLinearMap _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The equivariant geometric cellular map sends each cellular basis vector to the cellular
basis vector of the relabelled simplex, with no orientation sign. -/
theorem universalGSpaceCellularRepresentationMap_cellularChainBasis (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (φ.universalGSpaceCellularRepresentationMap (k := k) n).hom
        (cellularChainBasis (univ : Set (universalGSpace G)) k n
          ((realizationCellEquiv _ n).symm c)) =
      cellularChainBasis (univ : Set (universalGSpace H)) k n
        ((realizationCellEquiv _ n).symm (φ.universalGSpaceCellMap c)) := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepresentationMap_hom_toLinearMap]
  refine cellularChainGroupMap_cellularChainBasis _ _ _ k fun x _ _ ↦ ?_
  rw [φ.universalGSpaceCellularMap_apply]
  simp only [map_realizationCellEquiv_symm]
  exact φ.universalGSpaceMap_characteristicMap c x

/-- Degreewise geometric cellular representation maps intertwine the equivariant cellular
differentials. -/
@[reassoc]
theorem universalGSpaceCellularRepresentationMap_comp_differential (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularRepresentationMap (k := k) (n + 1) ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularDifferential k H n) =
      universalGSpaceCellularDifferential k G n ≫
        φ.universalGSpaceCellularRepresentationMap n := by
  unfold universalGSpaceCellularRepresentationMap universalGSpaceCellularDifferential
  exact cellularActionRepresentationMap_comp_differential _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The identity homomorphism induces the identity on each geometric cellular chain
representation. -/
@[simp]
theorem universalGSpaceCellularRepresentationMap_id (n : ℕ) :
    (MonoidHom.id G).universalGSpaceCellularRepresentationMap (k := k) n = 𝟙 _ :=
  (cellularActionRepresentationMap_congr _ _ _ _ _ _ _ _ _ _
    (φ := MonoidHom.id G) _ _ k universalGSpaceCellularMap_id (isCellular_id _)
    (fun g ↦ by simp) n).trans
    (cellularActionRepresentationMap_id _ _ _ _ _ _ _ k n)

/-- Geometric cellular chain representation maps respect composition of group homomorphisms,
restricting the second map along the first homomorphism. -/
@[reassoc, simp]
theorem universalGSpaceCellularRepresentationMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) (n : ℕ) :
    (ψ.comp φ).universalGSpaceCellularRepresentationMap (k := k) n =
      φ.universalGSpaceCellularRepresentationMap n ≫
        (Rep.resFunctor φ).map (ψ.universalGSpaceCellularRepresentationMap n) := by
  unfold universalGSpaceCellularRepresentationMap universalGSpaceCellularRepresentation
  rw [cellularActionRepresentationMap_congr _ _ _ _ _ _ _ _ _ _ _ _ k
    (universalGSpaceCellularMap_comp ψ φ)
    (IsCellular.comp _ _ φ.isCellular_universalGSpaceCellularMap
      ψ.isCellular_universalGSpaceCellularMap)
    (fun g ↦ by
      rw [← universalGSpaceCellularMap_comp]
      exact (ψ.comp φ).universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap g)]
  exact cellularActionRepresentationMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k n

/-- The equivariant chain map on geometric cellular chains of Milnor's join induced by a
group homomorphism, with the target action restricted along the homomorphism. -/
def universalGSpaceCellularComplexMap (φ : G →* H) :
    universalGSpaceCellularComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularComplex k H) :=
  cellularActionComplexMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap k

/-- Components of the equivariant cellular chain map are the degreewise representation maps,
up to the canonical cellular-complex term transports. -/
@[simp]
theorem universalGSpaceCellularComplexMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularComplexMap (k := k)).f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        φ.universalGSpaceCellularRepresentationMap n ≫
        (Rep.resFunctor φ).map (eqToHom (universalGSpaceCellularComplex_X k H n).symm) := by
  unfold universalGSpaceCellularComplexMap universalGSpaceCellularRepresentationMap
  exact cellularActionComplexMap_f _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The identity homomorphism induces the identity equivariant cellular chain map. -/
@[simp]
theorem universalGSpaceCellularComplexMap_id :
    (MonoidHom.id G).universalGSpaceCellularComplexMap (k := k) =
      𝟙 (universalGSpaceCellularComplex k G) :=
  (cellularActionComplexMap_congr _ _ _ _ _ _ _ _ _ _
    (φ := MonoidHom.id G) _ _ k universalGSpaceCellularMap_id (isCellular_id _)
    (fun g ↦ by simp)).trans
    (cellularActionComplexMap_id _ _ _ _ _ _ _ k)

/-- Equivariant geometric cellular chain maps respect composition of group homomorphisms,
restricting the second map along the first homomorphism. -/
@[reassoc, simp]
theorem universalGSpaceCellularComplexMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularComplexMap (k := k) =
      φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularComplexMap := by
  unfold universalGSpaceCellularComplexMap universalGSpaceCellularComplex
  rw [cellularActionComplexMap_congr _ _ _ _ _ _ _ _ _ _ _ _ k
    (universalGSpaceCellularMap_comp ψ φ)
    (IsCellular.comp _ _ φ.isCellular_universalGSpaceCellularMap
      ψ.isCellular_universalGSpaceCellularMap)
    (fun g ↦ by
      rw [← universalGSpaceCellularMap_comp]
      exact (ψ.comp φ).universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap g)]
  exact cellularActionComplexMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k

/-- Forgetting the translation action intertwines the equivariant cellular chain map with the
ordinary geometric cellular chain map induced by `MonoidHom.universalGSpaceCellularMap`. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) ≫
      (universalGSpaceCellularComplexForget₂Iso k H).hom =
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        φ.universalGSpaceCellularComplexMap ≫
      ((universalGSpaceCellularComplex k H).repResForget₂Iso φ).hom := by
  unfold universalGSpaceCellularComplexForget₂Iso universalGSpaceCellularComplexMap
    universalGSpaceCellularComplex
  exact cellularActionComplexForget₂Iso_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _ _

end Ring

end MonoidHom
