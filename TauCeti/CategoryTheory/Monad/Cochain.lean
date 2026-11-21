/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Comonad cochains

The functor `cochainCosimplicialAugmented` applies `linearYoneda` to the augmented
simplicial resolution. Forgetting the augmentation gives `cochainCosimplicial`.
Its alternating coface complex, `cochainComplex`, computes comonad cohomology
of `X` with coefficients in `Y` and has `Hom(G^(n+1) X, Y)` in degree `n`.
Faces are numbered from the outermost comonad factor, so the differential starts
with a positive outermost counit. The degree-zero augmentation is precomposition
with the counit, packaged in `cochainComplexAugmentation` as a cochain map from
`Hom(X, Y)` concentrated in degree zero.

The construction is contravariant in `X` and covariant in `Y`. No additivity
or linearity of the comonad is needed: the module structure comes from the
linear Hom spaces, and precomposition is linear for every morphism.

The construction follows Barr–Beck, *Homology and standard constructions*,
§§1, 4, and Gainutdinov–Haferkamp–Schweigert, *Davydov–Yetter cohomology,
comonads and Ocneanu rigidity*, §2.2. We use Mathlib's `linearYoneda` and
`AlgebraicTopology.alternatingCofaceMapComplex`.
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology Functor
open scoped Simplicial

universe w v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (G : Comonad C) (k : Type w) [Ring k] [Linear k C]

/-- Apply the linear Hom functor to the augmented simplicial resolution of a comonad. -/
def cochainCosimplicialAugmented : Cᵒᵖ ⥤ C ⥤ CosimplicialObject.Augmented (ModuleCat.{v} k) :=
  G.augmentedSimplicialResolution.op ⋙ (simplicialCosimplicialAugmentedEquiv C).functor ⋙
    (linearYoneda k C ⋙ CosimplicialObject.Augmented.whiskering Cᵒᵖ (ModuleCat.{v} k)).flip

/-- The augmented cochains are obtained by whiskering the dual of the augmented resolution. -/
lemma cochainCosimplicialAugmented_def : G.cochainCosimplicialAugmented k =
    G.augmentedSimplicialResolution.op ⋙ (simplicialCosimplicialAugmentedEquiv C).functor ⋙
      (linearYoneda k C ⋙ CosimplicialObject.Augmented.whiskering Cᵒᵖ (ModuleCat.{v} k)).flip :=
  (rfl)

/-- The cosimplicial module of comonad cochains, contravariant in the resolved
object and covariant in the coefficient object. -/
def cochainCosimplicial : Cᵒᵖ ⥤ C ⥤ CosimplicialObject (ModuleCat.{v} k) :=
  G.simplicialResolution.op ⋙ (simplicialCosimplicialEquiv C).functor ⋙
    (linearYoneda k C ⋙ CosimplicialObject.whiskering Cᵒᵖ (ModuleCat.{v} k)).flip

/-- The cochain bifunctor applies linear Hom to the dual of the simplicial resolution. -/
lemma cochainCosimplicial_def : G.cochainCosimplicial k =
    G.simplicialResolution.op ⋙ (simplicialCosimplicialEquiv C).functor ⋙
      (linearYoneda k C ⋙ CosimplicialObject.whiskering Cᵒᵖ (ModuleCat.{v} k)).flip := (rfl)

/-- At a pair of objects, the cosimplicial module is formed by applying linear Hom. -/
lemma cochainCosimplicial_obj_obj (X Y : C) :
    ((G.cochainCosimplicial k).obj (op X)).obj Y =
      (G.simplicialResolution.obj X).rightOp ⋙ (linearYoneda k C).obj Y := (rfl)

/-- The augmented cochains are the dual of the augmented resolution, with linear Hom applied. -/
lemma cochainCosimplicialAugmented_obj_obj (X Y : C) :
    ((G.cochainCosimplicialAugmented k).obj (op X)).obj Y =
      ((CosimplicialObject.Augmented.whiskering _ _).obj ((linearYoneda k C).obj Y)).obj
        (G.augmentedSimplicialResolution.obj X).rightOp := (rfl)

/-- Dropping the augmentation recovers the cosimplicial cochain bifunctor. -/
lemma cochainCosimplicialAugmented_comp_drop :
    G.cochainCosimplicialAugmented k ⋙
      (Functor.whiskeringRight _ _ _).obj CosimplicialObject.Augmented.drop =
      G.cochainCosimplicial k := (rfl)

/-- The point of the augmented cochain bifunctor is the linear Hom bifunctor. -/
lemma cochainCosimplicialAugmented_comp_point :
    G.cochainCosimplicialAugmented k ⋙
      (Functor.whiskeringRight _ _ _).obj CosimplicialObject.Augmented.point =
      linearCoyoneda k C := (rfl)

/-- The degree-`n` comonad cochains are maps out of `G^(n+1) X`. -/
def cochainCosimplicialObjIso (X Y : C) (n : ℕ) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).obj ⦋n⦌ ≅
      ModuleCat.of k ((G.resolutionStage (n + 1)).obj X ⟶ Y) :=
  Iso.refl _

/-- The object in degree `n` is the linear Hom out of the corresponding resolution stage. -/
lemma cochainCosimplicial_obj_obj_obj (X Y : C) (n : ℕ) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).obj ⦋n⦌ =
      ModuleCat.of k ((G.resolutionStage (n + 1)).obj X ⟶ Y) := (rfl)

/-- The degree identification is induced by the object equality. -/
lemma cochainCosimplicialObjIso_eq_eqToIso (X Y : C) (n : ℕ) :
    G.cochainCosimplicialObjIso k X Y n =
      eqToIso (G.cochainCosimplicial_obj_obj_obj k X Y n) := (rfl)

/-- Cofaces precompose with the counit in the indicated position. -/
@[reassoc (attr := simp)]
lemma cochainCosimplicial_δ (X Y : C) {n : ℕ} (i : Fin (n + 2)) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).δ i ≫
        (G.cochainCosimplicialObjIso k X Y (n + 1)).hom =
      (G.cochainCosimplicialObjIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionFace (n + 1) i).app X)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_δ X i)

/-- Codegeneracies precompose with comultiplication in the indicated position. -/
@[reassoc (attr := simp)]
lemma cochainCosimplicial_σ (X Y : C) {n : ℕ} (i : Fin (n + 1)) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).σ i ≫
        (G.cochainCosimplicialObjIso k X Y n).hom =
      (G.cochainCosimplicialObjIso k X Y (n + 1)).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionDegeneracy n i).app X)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_σ X i)

/-- In each cosimplicial degree, the resolved-object map acts by precomposition. -/
@[reassoc (attr := simp)]
lemma cochainCosimplicial_map_app_app {X X' : C} (f : X' ⟶ X) (Y : C) (n : ℕ) :
    (((G.cochainCosimplicial k).map f.op).app Y).app ⦋n⦌ ≫
        (G.cochainCosimplicialObjIso k X' Y n).hom =
      (G.cochainCosimplicialObjIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionStage (n + 1)).map f)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_map_app f n)

/-- In each cosimplicial degree, the coefficient map acts by postcomposition. -/
@[reassoc (attr := simp)]
lemma cochainCosimplicial_obj_map_app (X : C) {Y Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    (((G.cochainCosimplicial k).obj (op X)).map g).app ⦋n⦌ ≫
        (G.cochainCosimplicialObjIso k X Y' n).hom =
      (G.cochainCosimplicialObjIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.rightComp k _ g) := by
  ext h
  rfl

/-- The comonad cochain complex, as a bifunctor. Its differentials are the
alternating sums of precomposition with the outermost-first faces. -/
def cochainComplex : Cᵒᵖ ⥤ C ⥤ CochainComplex (ModuleCat.{v} k) ℕ :=
  G.cochainCosimplicial k ⋙
    (Functor.whiskeringRight _ _ _).obj (alternatingCofaceMapComplex (ModuleCat k))

/-- The cochain complex bifunctor is the alternating coface complex of the cochains. -/
lemma cochainComplex_def : G.cochainComplex k =
    G.cochainCosimplicial k ⋙
      (Functor.whiskeringRight _ _ _).obj (alternatingCofaceMapComplex (ModuleCat k)) := (rfl)

/-- The complex at a pair of objects is the alternating coface complex of their cochains. -/
lemma cochainComplex_obj_obj (X Y : C) :
    ((G.cochainComplex k).obj (op X)).obj Y =
      (alternatingCofaceMapComplex (ModuleCat k)).obj
        (((G.cochainCosimplicial k).obj (op X)).obj Y) := (rfl)

/-- Identify degree `n` with the module `Hom(G^(n+1) X, Y)`. -/
def cochainComplexXIso (X Y : C) (n : ℕ) :
    (((G.cochainComplex k).obj (op X)).obj Y).X n ≅
      ModuleCat.of k ((G.resolutionStage (n + 1)).obj X ⟶ Y) :=
  G.cochainCosimplicialObjIso k X Y n

/-- The degrees of the cochain complex are the terms of the cosimplicial module. -/
lemma cochainComplex_obj_obj_X (X Y : C) (n : ℕ) :
    (((G.cochainComplex k).obj (op X)).obj Y).X n =
      (((G.cochainCosimplicial k).obj (op X)).obj Y).obj ⦋n⦌ := (rfl)

/-- The complex degree identification is inherited from the cosimplicial module. -/
lemma cochainComplexXIso_eq (X Y : C) (n : ℕ) :
    G.cochainComplexXIso k X Y n =
      eqToIso (G.cochainComplex_obj_obj_X k X Y n) ≪≫ G.cochainCosimplicialObjIso k X Y n :=
  (rfl)

/-- The differential is the signed sum of precomposition with each counit. -/
@[reassoc]
lemma cochainComplex_d (X Y : C) (n : ℕ) :
    (((G.cochainComplex k).obj (op X)).obj Y).d n (n + 1) ≫
        (G.cochainComplexXIso k X Y (n + 1)).hom =
      (G.cochainComplexXIso k X Y n).hom ≫
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionFace (n + 1) i).app X)) := by
  dsimp only [cochainComplex, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
    alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  simp only [AlternatingCofaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    cochainComplexXIso, cochainCosimplicial_δ]

/-- Contravariance acts by precomposition with the iterated comonad map. -/
@[reassoc (attr := simp)]
lemma cochainComplex_map_app_f {X X' : C} (f : X' ⟶ X) (Y : C) (n : ℕ) :
    (((G.cochainComplex k).map f.op).app Y).f n ≫
        (G.cochainComplexXIso k X' Y n).hom =
      (G.cochainComplexXIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionStage (n + 1)).map f)) :=
  G.cochainCosimplicial_map_app_app k f Y n

/-- Covariance acts by postcomposition with the coefficient map. -/
@[reassoc (attr := simp)]
lemma cochainComplex_obj_map_f (X : C) {Y Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    ((((G.cochainComplex k).obj (op X)).map g).f n) ≫
        (G.cochainComplexXIso k X Y' n).hom =
      (G.cochainComplexXIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.rightComp k _ g) :=
  G.cochainCosimplicial_obj_map_app k X g n

/-- The counit sends a map `X ⟶ Y` to its degree-zero comonad cochain. -/
def cochainAugmentation (X Y : C) :
    ModuleCat.of k (X ⟶ Y) ⟶ (((G.cochainComplex k).obj (op X)).obj Y).X 0 :=
  (((G.cochainCosimplicialAugmented k).obj (op X)).obj Y).hom.app ⦋0⦌

/-- The degree-zero augmentation, as an arrow, is the degree-zero cosimplicial component. -/
lemma cochainAugmentation_arrow_mk (X Y : C) :
    Arrow.mk (G.cochainAugmentation k X Y) =
      CosimplicialObject.Augmented.toArrow.obj
        (((G.cochainCosimplicialAugmented k).obj (op X)).obj Y) := (rfl)

/-- Under the degree-zero identification, the augmentation is precomposition
with the counit. -/
@[reassoc (attr := simp)]
lemma cochainAugmentation_comp_cochainComplexXIso_hom (X Y : C) :
    G.cochainAugmentation k X Y ≫ (G.cochainComplexXIso k X Y 0).hom =
      ModuleCat.ofHom (Linear.leftComp k Y (G.ε.app X)) := by
  -- Whiskering the simplicial augmentation inserts an identity from `constComp`.
  change (𝟙 _ ≫ ((linearYoneda k C).obj Y).map
    ((G.simplicialResolutionAugmentation X).app (op ⦋0⦌)).op) ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp, simplicialResolutionAugmentation_app_zero]
  rfl

/-- Augmented cochains are cocycles. -/
@[reassoc (attr := simp)]
lemma cochainAugmentation_comp_d (X Y : C) :
    G.cochainAugmentation k X Y ≫
      (((G.cochainComplex k).obj (op X)).obj Y).d 0 1 = 0 := by
  let A := ((G.cochainCosimplicialAugmented k).obj (op X)).obj Y
  -- Compute in the cosimplicial terms so both summands have the same dependent endpoints.
  change A.hom.app ⦋0⦌ ≫ AlternatingCofaceMapComplex.objD A.right 0 = 0
  have h (i : Fin 2) : A.hom.app ⦋0⦌ ≫ A.right.δ i = A.hom.app ⦋1⦌ := by
    simpa [CosimplicialObject.δ] using (A.hom.naturality (SimplexCategory.δ i)).symm
  simp [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, Preadditive.comp_add,
    Preadditive.comp_neg, h]

/-- The augmentation as a cochain map from `Hom(X, Y)` concentrated in degree zero. -/
def cochainComplexAugmentation (X Y : C) :
    (CochainComplex.single₀ (ModuleCat k)).obj (ModuleCat.of k (X ⟶ Y)) ⟶
      (((G.cochainComplex k).obj (op X)).obj Y) :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨G.cochainAugmentation k X Y, G.cochainAugmentation_comp_d k X Y⟩

/-- The degree-zero part of the cochain map is the counit augmentation. -/
@[simp]
lemma cochainComplexAugmentation_f_zero (X Y : C) :
    (G.cochainComplexAugmentation k X Y).f 0 = G.cochainAugmentation k X Y := by
  apply CochainComplex.fromSingle₀Equiv_symm_apply_f_zero

/-- The augmentation is zero in positive degrees. -/
@[simp]
lemma cochainComplexAugmentation_f_succ (X Y : C) (n : ℕ) :
    (G.cochainComplexAugmentation k X Y).f (n + 1) = 0 := by
  exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
    (ModuleCat.of k (X ⟶ Y)) (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

/-- The augmentation is natural in the resolved object. -/
@[reassoc]
lemma cochainAugmentation_naturality_left {X X' : C} (f : X' ⟶ X) (Y : C) :
    G.cochainAugmentation k X Y ≫ (((G.cochainComplex k).map f.op).app Y).f 0 =
      ModuleCat.ofHom (Linear.leftComp k Y f) ≫ G.cochainAugmentation k X' Y := by
  exact (CosimplicialObject.Augmented.w_app
    (η := ((G.cochainCosimplicialAugmented k).map f.op).app Y) (n := ⦋0⦌)).symm

/-- The augmentation is natural in the coefficient object. -/
@[reassoc]
lemma cochainAugmentation_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    G.cochainAugmentation k X Y ≫ (((G.cochainComplex k).obj (op X)).map g).f 0 =
      ModuleCat.ofHom (Linear.rightComp k X g) ≫ G.cochainAugmentation k X Y' := by
  exact (CosimplicialObject.Augmented.w_app
    (η := ((G.cochainCosimplicialAugmented k).obj (op X)).map g) (n := ⦋0⦌)).symm

/-- The cochain augmentation is natural in the resolved object. -/
@[reassoc]
lemma cochainComplexAugmentation_naturality_left {X X' : C} (f : X' ⟶ X) (Y : C) :
    G.cochainComplexAugmentation k X Y ≫ ((G.cochainComplex k).map f.op).app Y =
      (CochainComplex.single₀ (ModuleCat k)).map (ModuleCat.ofHom (Linear.leftComp k Y f)) ≫
        G.cochainComplexAugmentation k X' Y := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  rw [CochainComplex.fromSingle₀Equiv_apply_coe, CochainComplex.fromSingle₀Equiv_apply_coe]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    cochainComplexAugmentation_f_zero, cochainComplexAugmentation_f_zero]
  exact G.cochainAugmentation_naturality_left k f Y

/-- The cochain augmentation is natural in the coefficient object. -/
@[reassoc]
lemma cochainComplexAugmentation_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    G.cochainComplexAugmentation k X Y ≫ ((G.cochainComplex k).obj (op X)).map g =
      (CochainComplex.single₀ (ModuleCat k)).map (ModuleCat.ofHom (Linear.rightComp k X g)) ≫
        G.cochainComplexAugmentation k X Y' := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  rw [CochainComplex.fromSingle₀Equiv_apply_coe, CochainComplex.fromSingle₀Equiv_apply_coe]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    cochainComplexAugmentation_f_zero, cochainComplexAugmentation_f_zero]
  exact G.cochainAugmentation_naturality_right k X g

end CategoryTheory.Comonad
