/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Equivariant
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
