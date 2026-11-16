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
representations. Composing it with the explicit ordered join-to-standard comparison, and
further with `(Rep.barComplex.isoStandardComplex k G).symm`, gives chain homotopy equivalences in
`Rep k G` to both `Rep.standardComplex k G` and `Rep.barComplex k G` before forgetting the action.
In particular, a cellular basis vector with increasing-index vertex labels `(g₀, …, gₙ)` maps to
`g₀ • [g₀⁻¹g₁ | ⋯ | gₙ₋₁⁻¹gₙ]` scaled by the orientation unit `realizationChainScale k n`.

Any group homomorphism `φ : G →* H` acts on Milnor joins by the cellular map
`MonoidHom.universalGSpaceCellularMap`, inducing an equivariant chain map
`MonoidHom.universalGSpaceCellularComplexMap` into the restricted target complex that recovers the
underlying cellular chain map after forgetting actions and preserves the resolution augmentation
(`MonoidHom.universalGSpaceCellularComplexMap_f_zero_comp_π`) without assuming restriction preserves
projective representations.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections I.4, I.5, and II.4.
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
    universalGSpaceCellularTranslation_mul (ModuleCat.of k k) n

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
    universalGSpaceCellularTranslation_mul (ModuleCat.of k k) n

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
    universalGSpaceCellularTranslation_mul (ModuleCat.of k k)

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
    universalGSpaceCellularTranslation_mul (ModuleCat.of k k)

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

/-- Forgetting the translation action identifies the equivariant cellular-to-ordered comparison
with the module-level cellular comparison `universalGSpaceCellularChainComplexIso`. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_comp_map_universalGSpaceCellularComplexIso :
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexForget₂Iso_hom_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceCellularChainComplexIso_hom_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
  simp only [Rep.forget₂_moduleCat_map, universalGSpaceCellularRepIso_hom_toLinearMap,
    LinearEquiv.toModuleIso_hom, eqToHom_trans_assoc]

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
-- The body is exposed, as for `universalGSpaceResolution` and Mathlib's
-- `Rep.standardResolution`, so that the complex of the resolution is the cellular chain complex
-- by definition: stating `universalGSpaceCellularResolution_π` and passing
-- `MonoidHom.universalGSpaceCellularComplexMap` directly as a morphism of resolutions need this.
@[expose]
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
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G :=
  (rfl)

/-- In degree zero the augmentation is the geometric cellular augmentation, not just
an abstract map to the trivial representation. -/
theorem universalGSpaceCellularResolution_π_f_zero_hom_apply
    (x : (cellularChainGroup (univ : Set (universalGSpace G))
      (ModuleCat.of k k) 0 : ModuleCat k)) :
    ((universalGSpaceCellularResolution k G).π.f 0).hom
      ((eqToHom (universalGSpaceCellularComplex_X k G 0).symm) x) =
      cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k) x := by
  simp only [universalGSpaceCellularResolution_π, HomologicalComplex.comp_f,
    universalGSpaceCellularComplexIso_hom_f, universalGSpaceAugmentation_f_zero]
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

/-- The geometric cellular-to-standard comparison is a chain homotopy equivalence in `Rep k G`:
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

/-- The inverse equivariant comparison is the projective lift back to ordered join chains,
followed by the inverse equivariant cellular-to-ordered isomorphism. -/
@[simp]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_inv :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv =
      ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
          (universalGSpaceResolution k G) ≫
        (universalGSpaceCellularComplexIso k G).inv := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv,
    HomotopyEquiv.trans, HomotopyEquiv.ofIso, universalGSpaceStandardHomotopyEquiv_inv]
  -- The two projective lifts carry the definitionally equal augmentation targets of the
  -- join and standard resolutions; reflexivity identifies these implicit object arguments.
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

/-- The geometric cellular-to-standard map preserves augmentation. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_comp_π :
    (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        (Rep.standardResolution k G).π =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom]
  exact (Category.assoc _ _ _).trans
    (congrArg ((universalGSpaceCellularComplexIso k G).hom ≫ ·)
      (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G))

/-- The explicit geometric cellular-to-standard map agrees up to equivariant chain homotopy
with Mathlib's abstract comparison of the two projective resolutions. -/
def universalGSpaceCellularStandardComparisonHomotopy :
    Homotopy (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
      (ProjectiveResolution.homotopyEquiv (universalGSpaceCellularResolution k G)
        (Rep.standardResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceCellularResolution k G)
    (Rep.standardResolution k G) (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom
    ((universalGSpaceCellularRepStandardHomotopyEquiv_comp_π k G).trans
      (universalGSpaceCellularResolution_π k G).symm)

/-- **Equivariant chain homotopy equivalence between geometric cellular chains of Milnor's join
and Mathlib's inhomogeneous bar resolution.** -/
def universalGSpaceCellularBarHomotopyEquiv :
    HomotopyEquiv (universalGSpaceCellularComplex k G) (Rep.barComplex k G) :=
  (universalGSpaceCellularRepStandardHomotopyEquiv k G).trans
    (HomotopyEquiv.ofIso (Rep.barComplex.isoStandardComplex k G).symm)

/-- `universalGSpaceCellularBarHomotopyEquiv` composes the equivariant cellular-to-standard
homotopy equivalence with the inverse of `Rep.barComplex.isoStandardComplex`. -/
theorem universalGSpaceCellularBarHomotopyEquiv_def :
    universalGSpaceCellularBarHomotopyEquiv k G =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).trans
        (HomotopyEquiv.ofIso (Rep.barComplex.isoStandardComplex k G).symm) :=
  (rfl)

/-- The forward map to `Rep.barComplex` factors through the explicit join-to-standard comparison
followed by `(Rep.barComplex.isoStandardComplex k G).inv`. -/
@[simp]
theorem universalGSpaceCellularBarHomotopyEquiv_hom :
    (universalGSpaceCellularBarHomotopyEquiv k G).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫
        (Rep.barComplex.isoStandardComplex k G).inv := by
  simp [universalGSpaceCellularBarHomotopyEquiv_def, HomotopyEquiv.trans, HomotopyEquiv.ofIso]

/-- The inverse map from `Rep.barComplex` applies `(Rep.barComplex.isoStandardComplex k G).hom`
followed by the inverse equivariant join-to-standard comparison. -/
@[simp]
theorem universalGSpaceCellularBarHomotopyEquiv_inv :
    (universalGSpaceCellularBarHomotopyEquiv k G).inv =
      (Rep.barComplex.isoStandardComplex k G).hom ≫
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv := by
  simp [universalGSpaceCellularBarHomotopyEquiv_def, HomotopyEquiv.trans, HomotopyEquiv.ofIso]

/-- **Explicit formula on cellular basis elements.** An `n`-simplex `c` of Milnor's join with
increasing-index vertex labels `(g₀, …, gₙ)` maps to the inhomogeneous bar generator
`[g₀⁻¹g₁ | ⋯ | gₙ₋₁⁻¹gₙ]` with group coefficient `sₙ • g₀`, where
`sₙ = realizationChainScale k n`. -/
theorem universalGSpaceCellularBarHomotopyEquiv_hom_f_hom_cellularChainBasis {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    ((universalGSpaceCellularBarHomotopyEquiv k G).hom.f n).hom
        ((eqToHom (universalGSpaceCellularComplex_X k G n).symm)
          (cellularChainBasis (univ : Set (universalGSpace G)) k n
            ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c))) =
      Finsupp.single
        (fun i : Fin n ↦
          (universalGSpaceCellLabels c i.castSucc)⁻¹ * universalGSpaceCellLabels c i.succ)
        (MonoidAlgebra.single (universalGSpaceCellLabels c 0)
          (realizationChainScale k n : k)) := by
  rw [universalGSpaceCellularBarHomotopyEquiv_hom]
  simp only [HomologicalComplex.comp_f, Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom_f_hom_cellularChainBasis,
    TauCeti.Rep.barComplex.isoStandardComplex_inv_f]
  exact TauCeti.Rep.diagonalSuccIsoFree_hom_hom_single n (universalGSpaceCellLabels c)
    (realizationChainScale k n : k)

/-- The explicit geometric cellular-to-inhomogeneous-bar map preserves augmentation. -/
@[reassoc]
theorem universalGSpaceCellularBarHomotopyEquiv_comp_π :
    (universalGSpaceCellularBarHomotopyEquiv k G).hom ≫ (Rep.barResolution k G).π =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [TauCeti.Rep.barResolution_π, universalGSpaceCellularBarHomotopyEquiv_hom, Category.assoc,
    Iso.inv_hom_id_assoc, ← TauCeti.Rep.standardResolution_π,
    universalGSpaceCellularRepStandardHomotopyEquiv_comp_π]

/-- The explicit geometric cellular-to-inhomogeneous-bar map agrees up to equivariant chain
homotopy with Mathlib's abstract comparison of the two projective resolutions. -/
def universalGSpaceCellularBarComparisonHomotopy :
    Homotopy (universalGSpaceCellularBarHomotopyEquiv k G).hom
      (ProjectiveResolution.homotopyEquiv (universalGSpaceCellularResolution k G)
        (Rep.barResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceCellularResolution k G)
    (Rep.barResolution k G) (universalGSpaceCellularBarHomotopyEquiv k G).hom
    ((universalGSpaceCellularBarHomotopyEquiv_comp_π k G).trans
      (universalGSpaceCellularResolution_π k G).symm)

end Resolution

end TauCeti

namespace MonoidHom

open TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

variable {k G H : Type u} [Group G] [Group H]

/-- The universal-subset cellular map of a group homomorphism intertwines translation by `g` with
translation by `φ g`. -/
@[reassoc]
theorem universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap
    (φ : G →* H) (g : G) :
    universalGSpaceCellularTranslation g ≫ φ.universalGSpaceCellularMap =
      φ.universalGSpaceCellularMap ≫ universalGSpaceCellularTranslation (φ g) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  grind [universalGSpaceCellularMap_apply, universalGSpaceCellularTranslation_apply,
    universalGSpaceMap_smul, CategoryTheory.comp_apply]

section ChainComplex

variable [Ring k]

/-- The equivariant morphism of geometric cellular chain representations in degree `n` induced by
`MonoidHom.universalGSpaceMap`. -/
def universalGSpaceCellularRepMap (φ : G →* H) (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G n) ⟶
      Rep.res φ (Rep.of (universalGSpaceCellularRepresentation k H n)) :=
  cellularActionRepMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul
    univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul
    φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap (ModuleCat.of k k) n

/-- Forgetting equivariance recovers the cellular chain-group map of
`MonoidHom.universalGSpaceCellularMap`. -/
@[simp]
theorem universalGSpaceCellularRepMap_hom_toLinearMap (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularRepMap (k := k) n).hom.toLinearMap =
      (cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) n).hom := by
  unfold universalGSpaceCellularRepMap
  exact cellularActionRepMap_hom_toLinearMap _ _ _ _ _ _ _ _ _ _ _ _ _ (ModuleCat.of k k) n

/-- On cellular basis elements, the induced representation morphism carries the generator of a
simplex `c` to the generator of the relabelled simplex `φ.universalGSpaceCellMap c`, with no
orientation sign. -/
theorem universalGSpaceCellularRepMap_hom_cellularChainBasis (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (φ.universalGSpaceCellularRepMap (k := k) n).hom
        (cellularChainBasis (univ : Set (universalGSpace G)) k n
          ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c)) =
      cellularChainBasis (univ : Set (universalGSpace H)) k n
        ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm
          (φ.universalGSpaceCellMap c)) := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepMap_hom_toLinearMap]
  refine cellularChainGroupMap_cellularChainBasis _ _ _ k fun x _ _ ↦ ?_
  rw [AbstractSimplicialComplex.map_realizationCellEquiv_symm,
    AbstractSimplicialComplex.map_realizationCellEquiv_symm]
  exact (φ.universalGSpaceCellularMap_apply _).trans (φ.universalGSpaceMap_characteristicMap c x)

/-- The identity homomorphism induces the identity morphism on geometric cellular chain
representations of Milnor's join. -/
@[simp]
theorem universalGSpaceCellularRepMap_id (n : ℕ) :
    (MonoidHom.id G).universalGSpaceCellularRepMap (k := k) n =
      𝟙 (Rep.of (universalGSpaceCellularRepresentation k G n)) := by
  unfold universalGSpaceCellularRepMap universalGSpaceCellularRepresentation
  have hcomm : ∀ g : G,
      universalGSpaceCellularTranslation g ≫ 𝟙 (TopCat.of (univ : Set (universalGSpace G))) =
        𝟙 _ ≫ universalGSpaceCellularTranslation ((MonoidHom.id G) g) := by
    intro g
    simp
  exact (cellularActionRepMap_congr _ _ _ _ _ _ _ _ _ _ (MonoidHom.id G)
    (MonoidHom.id G).isCellular_universalGSpaceCellularMap (isCellular_id univ) _ hcomm
    universalGSpaceCellularMap_id (ModuleCat.of k k) n).trans
    (cellularActionRepMap_id _ _ _ _ _ hcomm (ModuleCat.of k k) n)

/-- Degreewise equivariant cellular chain maps of Milnor joins respect composition of group
homomorphisms. -/
@[simp]
theorem universalGSpaceCellularRepMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) (n : ℕ) :
    (ψ.comp φ).universalGSpaceCellularRepMap (k := k) n =
      φ.universalGSpaceCellularRepMap n ≫
        (Rep.resFunctor φ).map (ψ.universalGSpaceCellularRepMap n) := by
  unfold universalGSpaceCellularRepMap universalGSpaceCellularRepresentation
  have hcomm : ∀ g : G,
      universalGSpaceCellularTranslation g ≫
          (φ.universalGSpaceCellularMap ≫ ψ.universalGSpaceCellularMap) =
        (φ.universalGSpaceCellularMap ≫ ψ.universalGSpaceCellularMap) ≫
          universalGSpaceCellularTranslation ((ψ.comp φ) g) := by
    intro g
    rw [← Category.assoc,
      φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap,
      Category.assoc,
      ψ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap,
      Category.assoc, MonoidHom.comp_apply]
  exact (cellularActionRepMap_congr _ _ _ _ _ _ _ _ _ _ (ψ.comp φ)
    (ψ.comp φ).isCellular_universalGSpaceCellularMap
    (IsCellular.comp univ univ φ.isCellular_universalGSpaceCellularMap
      ψ.isCellular_universalGSpaceCellularMap)
    _ hcomm (universalGSpaceCellularMap_comp ψ φ) (ModuleCat.of k k) n).trans
    (cellularActionRepMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ψ φ
      φ.isCellular_universalGSpaceCellularMap ψ.isCellular_universalGSpaceCellularMap
      _ _ hcomm (ModuleCat.of k k) n)

/-- The degreewise equivariant cellular chain maps commute with the geometric cellular
differentials of Milnor's join. -/
@[reassoc]
theorem universalGSpaceCellularRepMap_comp_universalGSpaceCellularDifferential
    (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularRepMap (k := k) (n + 1) ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularDifferential k H n) =
      universalGSpaceCellularDifferential k G n ≫
        φ.universalGSpaceCellularRepMap n := by
  unfold universalGSpaceCellularRepMap universalGSpaceCellularDifferential
  exact cellularActionRepMap_comp_cellularActionDifferential _ _ _ _ _ _ _ _ _ _
    φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap
    (ModuleCat.of k k) n

/-- **Equivariant chain map on geometric cellular chains of Milnor's join** induced by the
continuous map `MonoidHom.universalGSpaceMap` of a group homomorphism `φ : G →* H`. -/
def universalGSpaceCellularComplexMap (φ : G →* H) :
    universalGSpaceCellularComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (universalGSpaceCellularComplex k H) :=
  cellularActionComplexMap univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul
    univ universalGSpaceCellularTranslation
    isCellular_universalGSpaceCellularTranslation universalGSpaceCellularTranslation_one
    universalGSpaceCellularTranslation_mul
    φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap (ModuleCat.of k k)

/-- In degree `n` the equivariant cellular chain map is `universalGSpaceCellularRepMap`, up to
the canonical cellular-term transports. -/
@[simp]
theorem universalGSpaceCellularComplexMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularComplexMap (k := k)).f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        φ.universalGSpaceCellularRepMap n ≫
        eqToHom (congrArg (Rep.resFunctor φ).obj
          (universalGSpaceCellularComplex_X k H n).symm) := by
  unfold universalGSpaceCellularComplexMap universalGSpaceCellularRepMap
    universalGSpaceCellularComplex universalGSpaceCellularRepresentation
  exact cellularActionComplexMap_f _ _ _ _ _ _ _ _ _ _ _ _ _ (ModuleCat.of k k) n

/-- Forgetting the translation actions identifies `universalGSpaceCellularComplexMap` with the
underlying geometric cellular chain map of `MonoidHom.universalGSpaceCellularMap`. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) ≫
      (universalGSpaceCellularComplexForget₂Iso k H).hom =
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        φ.universalGSpaceCellularComplexMap ≫
      ((universalGSpaceCellularComplex k H).repResForget₂Iso φ).hom := by
  unfold universalGSpaceCellularComplexMap universalGSpaceCellularComplexForget₂Iso
    universalGSpaceCellularComplex
  exact cellularActionComplexForget₂Iso_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _ _
    (ModuleCat.of k k)

/-- The identity homomorphism induces the identity equivariant cellular chain map on Milnor's join.
-/
@[simp]
theorem universalGSpaceCellularComplexMap_id :
    (MonoidHom.id G).universalGSpaceCellularComplexMap (k := k) =
      𝟙 (universalGSpaceCellularComplex k G) := by
  ext n : 1
  simp

/-- Equivariant cellular chain maps of Milnor joins respect composition of group homomorphisms. -/
@[simp]
theorem universalGSpaceCellularComplexMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularComplexMap (k := k) =
      φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularComplexMap := by
  ext n : 1
  -- `-proj` keeps `(Rep.resFunctor _).map` unreduced so `Functor.map_comp` and `eqToHom_map`
  -- fire; `Rep.resFunctor` is an `abbrev`, so restriction along `ψ.comp φ` agrees with sequential
  -- restriction along `ψ` then `φ` on objects.
  simp -proj [eqToHom_map]

end ChainComplex

section Resolution

variable [CommRing k]

/-- **The equivariant cellular chain map on Milnor's join lies over the identity of `k`.** No
hypothesis on restriction preserving projective objects is needed. -/
@[reassoc]
theorem universalGSpaceCellularComplexMap_f_zero_comp_π (φ : G →* H) :
    (φ.universalGSpaceCellularComplexMap (k := k)).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) =
      (universalGSpaceCellularResolution k G).π.f 0 := by
  apply (cancel_epi (eqToHom (universalGSpaceCellularComplex_X k G 0).symm)).mp
  have hL :
      eqToHom (universalGSpaceCellularComplex_X k G 0).symm ≫
          ((φ.universalGSpaceCellularComplexMap (k := k)).f 0 ≫
            (Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0)) =
        φ.universalGSpaceCellularRepMap 0 ≫
          (Rep.resFunctor φ).map
            (eqToHom (universalGSpaceCellularComplex_X k H 0).symm ≫
              (universalGSpaceCellularResolution k H).π.f 0) := by
    -- `-proj` keeps the `abbrev` `(Rep.resFunctor φ).map` unreduced so `Functor.map_comp` and
    -- `eqToHom_map` merge the cellular-term transport into the restricted augmentation map.
    simp -proj [eqToHom_map]
  rw [hL]
  refine Rep.hom_ext <| DFunLike.ext _ _ fun x ↦ ?_
  have hy : (φ.universalGSpaceCellularRepMap (k := k) 0).hom x =
      (cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) 0) x := by
    rw [← Representation.IntertwiningMap.toLinearMap_apply,
      universalGSpaceCellularRepMap_hom_toLinearMap]
  -- `(universalGSpaceCellularResolution k _).complex` reduces to `universalGSpaceCellularComplex`
  -- at default transparency, while `Rep.hom_comp` and `Rep.resMap_hom_apply` hold by reflexivity,
  -- so assembling the elementwise chain in term mode avoids `rw`'s implicit-transparency check.
  exact (universalGSpaceCellularResolution_π_f_zero_hom_apply k H
      ((φ.universalGSpaceCellularRepMap (k := k) 0).hom x)).trans <|
    (congrArg
      (cellularAugmentation (univ : Set (universalGSpace H)) (ModuleCat.of k k)) hy).trans <|
      (ConcreteCategory.congr_hom
        (cellularChainGroupMap_comp_cellularAugmentation univ univ
          φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k)) x).trans
        (universalGSpaceCellularResolution_π_f_zero_hom_apply k G x).symm

end Resolution

end MonoidHom
