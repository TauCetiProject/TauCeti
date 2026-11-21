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

Applying `Hom(-, Y)` to the augmented simplicial resolution of a comonad gives
an augmented cosimplicial module. Its alternating coface complex has
`Hom(G^(n+1) X, Y)` in degree `n`. Faces are numbered from the outermost
comonad factor, so the differential starts with a positive outermost counit.

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

/-- The cosimplicial module of comonad cochains, contravariant in the resolved
object and covariant in the coefficient object. -/
def cochainCosimplicial : Cᵒᵖ ⥤ C ⥤ CosimplicialObject (ModuleCat.{v} k) where
  obj X :=
    { obj := fun Y => (G.simplicialResolution.obj X.unop).rightOp ⋙ (linearYoneda k C).obj Y
      map := fun g => whiskerLeft _ ((linearYoneda k C).map g) }
  map f :=
    { app := fun Y => whiskerRight (NatTrans.rightOp (G.simplicialResolution.map f.unop))
        ((linearYoneda k C).obj Y)
      naturality {Y Y'} g := by
        ext n h
        exact (Category.assoc ((G.simplicialResolution.map f.unop).app (op n)) h g).symm }
  map_id X := by ext Y n h; simp
  map_comp f g := by ext Y n h; simp

/-- The degree-`n` comonad cochains are maps out of `G^(n+1) X`. -/
def cochainCosimplicialXIso (X Y : C) (n : ℕ) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).obj ⦋n⦌ ≅
      ModuleCat.of k ((G.resolutionStage (n + 1)).obj X ⟶ Y) :=
  Iso.refl _

/-- Cofaces precompose with the counit in the indicated position. -/
@[reassoc]
lemma cochainCosimplicial_δ (X Y : C) {n : ℕ} (i : Fin (n + 2)) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).δ i ≫
        (G.cochainCosimplicialXIso k X Y (n + 1)).hom =
      (G.cochainCosimplicialXIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionFace (n + 1) i).app X)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_δ X i)

/-- Codegeneracies precompose with comultiplication in the indicated position. -/
@[reassoc]
lemma cochainCosimplicial_σ (X Y : C) {n : ℕ} (i : Fin (n + 1)) :
    (((G.cochainCosimplicial k).obj (op X)).obj Y).σ i ≫
        (G.cochainCosimplicialXIso k X Y n).hom =
      (G.cochainCosimplicialXIso k X Y (n + 1)).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionDegeneracy n i).app X)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_σ X i)

/-- The comonad cochain complex, as a bifunctor. Its differentials are the
alternating sums of precomposition with the outermost-first faces. -/
def cochainComplex : Cᵒᵖ ⥤ C ⥤ CochainComplex (ModuleCat.{v} k) ℕ :=
  G.cochainCosimplicial k ⋙
    (Functor.whiskeringRight _ _ _).obj (alternatingCofaceMapComplex (ModuleCat k))

/-- Identify degree `n` with the module `Hom(G^(n+1) X, Y)`. -/
def cochainComplexXIso (X Y : C) (n : ℕ) :
    (((G.cochainComplex k).obj (op X)).obj Y).X n ≅
      ModuleCat.of k ((G.resolutionStage (n + 1)).obj X ⟶ Y) :=
  G.cochainCosimplicialXIso k X Y n

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
lemma cochainComplex_map_f (X X' Y : C) (f : X' ⟶ X) (n : ℕ) :
    (((G.cochainComplex k).map f.op).app Y).f n ≫
        (G.cochainComplexXIso k X' Y n).hom =
      (G.cochainComplexXIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.leftComp k Y ((G.resolutionStage (n + 1)).map f)) := by
  ext h
  exact congrArg (· ≫ h) (G.simplicialResolution_map_app f n)

/-- Covariance acts by postcomposition with the coefficient map. -/
@[reassoc (attr := simp)]
lemma cochainComplex_obj_map_f (X Y Y' : C) (g : Y ⟶ Y') (n : ℕ) :
    ((((G.cochainComplex k).obj (op X)).map g).f n) ≫
        (G.cochainComplexXIso k X Y' n).hom =
      (G.cochainComplexXIso k X Y n).hom ≫
        ModuleCat.ofHom (Linear.rightComp k _ g) := by
  rfl

/-- The counit sends a map `X ⟶ Y` to its degree-zero comonad cochain. -/
def cochainAugmentation (X Y : C) :
    ModuleCat.of k (X ⟶ Y) ⟶ (((G.cochainComplex k).obj (op X)).obj Y).X 0 :=
  ModuleCat.ofHom (Linear.leftComp k Y (G.ε.app X)) ≫
    (G.cochainComplexXIso k X Y 0).inv

/-- Under the degree-zero identification, the augmentation is precomposition
with the counit. -/
@[reassoc (attr := simp)]
lemma cochainAugmentation_comp_XIso (X Y : C) :
    G.cochainAugmentation k X Y ≫ (G.cochainComplexXIso k X Y 0).hom =
      ModuleCat.ofHom (Linear.leftComp k Y (G.ε.app X)) := by
  rfl

/-- Augmented cochains are cocycles. -/
@[reassoc (attr := simp)]
lemma cochainAugmentation_comp_d (X Y : C) :
    G.cochainAugmentation k X Y ≫
      (((G.cochainComplex k).obj (op X)).obj Y).d 0 1 = 0 := by
  apply (cancel_mono (G.cochainComplexXIso k X Y 1).hom).1
  rw [Category.assoc, cochainComplex_d]
  rw [← Category.assoc, cochainAugmentation_comp_XIso]
  -- The recursive degree-one carriers are definitionally `G X` and `G² X`.
  -- `erw` aligns them, including the module structures on their Hom spaces.
  erw [Fin.sum_univ_two]
  ext h
  dsimp
  simp only [neg_smul, one_smul]
  -- Evaluate the module maps explicitly; rewriting under the dependent stage
  -- carriers cannot identify the degree-one module with `Hom(G² X, Y)`.
  change (G.resolutionFace 1 0).app X ≫ G.ε.app X ≫ h +
      -((G.resolutionFace 1 1).app X ≫ G.ε.app X ≫ h) = 0
  rw [← sub_eq_add_neg, sub_eq_zero]
  simp only [resolutionFace_zero_app, ← Fin.succ_zero_eq_one, resolutionFace_succ_app]
  dsimp only [resolutionStage, Functor.comp_obj, Functor.id_obj]
  have hε := G.ε.naturality (G.ε.app X)
  dsimp only [Functor.id_obj, Functor.id_map] at hε
  simpa only [Category.assoc] using congrArg (· ≫ h) hε.symm

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
lemma cochainAugmentation_naturality_left (X X' Y : C) (f : X' ⟶ X) :
    G.cochainAugmentation k X Y ≫ (((G.cochainComplex k).map f.op).app Y).f 0 =
      ModuleCat.ofHom (Linear.leftComp k Y f) ≫ G.cochainAugmentation k X' Y := by
  ext h
  -- Evaluate the degree-zero Hom modules to avoid rewriting their dependent carriers.
  change (G.resolutionStage 1).map f ≫ G.ε.app X ≫ h = G.ε.app X' ≫ f ≫ h
  dsimp only [resolutionStage, Functor.comp_map, Functor.id_map]
  have hε := G.ε.naturality f
  dsimp only [Functor.id_obj, Functor.id_map] at hε
  simpa only [Category.assoc] using congrArg (· ≫ h) hε

/-- The augmentation is natural in the coefficient object. -/
@[reassoc]
lemma cochainAugmentation_naturality_right (X Y Y' : C) (g : Y ⟶ Y') :
    G.cochainAugmentation k X Y ≫ (((G.cochainComplex k).obj (op X)).map g).f 0 =
      ModuleCat.ofHom (Linear.rightComp k X g) ≫ G.cochainAugmentation k X Y' := by
  ext h
  exact Category.assoc (G.ε.app X) h g

end CategoryTheory.Comonad
