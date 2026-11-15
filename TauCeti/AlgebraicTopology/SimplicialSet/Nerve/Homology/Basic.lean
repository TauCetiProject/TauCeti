/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

import TauCeti.AlgebraicTopology.SimplexCategory.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Homology of a category with coefficients in a functor

For a category `C` and `M : C ⥤ A`, `TauCeti.categorySimplicialObject C M` has degree-`n` object
`∐_{σ ∈ ComposableArrows C n} M(σ₀)`, and its alternating complex `TauCeti.categoryChainComplex`
and homology `TauCeti.categoryHomology` are functorial in `M` and `F : C ⥤ D`, recover
`(nerve C).homology X n` for constant coefficients, and send short exact coefficient sequences in
`AB4` abelian categories to long exact homology sequences (`TauCeti.categoryHomologyδ`).

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* C. A. Weibel, *The K-book*, Graduate Studies in Math. 145 (2013), IV.3.5.
-/

public noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe u v u₂ v₂ u₃ v₃ u' v'

namespace TauCeti

section SimplicialObject

variable {A : Type u'} [Category.{v'} A]

/-- The simplicial object associated to `C` and `M : C ⥤ A`, with degree-`n` object
`∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
def categorySimplicialObject (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : SimplicialObject A where
  obj Δ := ∐ fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0)
  map {Δ₁ Δ₂} f := Sigma.desc fun σ ↦
    M.map (σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))) ≫
      Sigma.ι (fun τ : ComposableArrows C Δ₂.unop.len ↦ M.obj (τ.obj 0))
        (σ.whiskerLeft f.unop.toOrderHom.monotone.functor)
  map_id Δ := by
    dsimp only [ComposableArrows.whiskerLeft]; ext σ
    rw [Sigma.ι_comp_desc, Category.comp_id,
      σ.map_homOfLE_eq_eqToHom (rfl : (𝟙 Δ).unop.toOrderHom 0 = 0), eqToHom_map]
    -- `(𝟙 Δ).unop.toOrderHom` is `OrderHom.id`, so `whiskerLeft` along it fixes `σ` definitionally.
    exact Category.id_comp _
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    dsimp only [ComposableArrows.whiskerLeft]; ext σ
    simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      Functor.comp_map, ← M.map_comp_assoc, ← σ.map_comp]
    -- Reindexing along `f ≫ g` composes the monotone functors by definition, and morphisms in the
    -- poset `Fin (Δ₁.unop.len + 1)` are unique.
    exact congrArg (fun h ↦ M.map (σ.map h) ≫ _) (Subsingleton.elim _ _)

section SimplicialLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌` of the `σ`-summand. -/
def ιCategorySimplicialObject (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌ :=
  Sigma.ι (fun τ : ComposableArrows C n ↦ M.obj (τ.obj 0)) σ

/-- Colimit cofan presenting `(categorySimplicialObject C M) _⦋n⦌` as `∐_{σ ∈ NₙC} M(σ₀)`. -/
abbrev categorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) :=
  Cofan.mk _ (ιCategorySimplicialObject M)

/-- `categorySimplicialObjectXCofan M n` is a coproduct colimit. -/
def isColimitCategorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categorySimplicialObjectXCofan M n) := coproductIsCoproduct _

@[ext] lemma categorySimplicialObject_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categorySimplicialObject C M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategorySimplicialObject M σ ≫ f = ιCategorySimplicialObject M σ ≫ g) : f = g :=
  (isColimitCategorySimplicialObjectXCofan M n).hom_ext fun ⟨σ⟩ ↦ h σ

/-- Action of `φ : ⦋m⦌ ⟶ ⦋n⦌` on the `σ`-summand of `categorySimplicialObject C M`. -/
@[reassoc] lemma ιCategorySimplicialObject_map (M : C ⥤ A) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).map φ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (φ.toOrderHom 0)))) ≫
        ιCategorySimplicialObject M ((nerve C).map φ.op σ) := Sigma.ι_comp_desc _ _

/-- Action of an epimorphism `φ : ⦋n⦌ ⟶ ⦋m⦌` in `SimplexCategory` on the `σ`-summand of
`categorySimplicialObject C M`. -/
@[reassoc] lemma ιCategorySimplicialObject_map_of_epi (M : C ⥤ A) {m n : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌)
    [Epi φ] (σ : ComposableArrows C m) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).map φ.op =
      eqToHom (by rw [CategoryTheory.nerve.map_obj, SimplexCategory.toOrderHom_zero_of_epi]) ≫
        ιCategorySimplicialObject M ((nerve C).map φ.op σ) := by
  rw [ιCategorySimplicialObject_map,
    σ.map_homOfLE_eq_eqToHom (SimplexCategory.toOrderHom_zero_of_epi φ), eqToHom_map]
  -- `((nerve C).map φ.op σ).obj 0` is definitionally `σ.obj (φ.toOrderHom 0)`.
  rfl

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_δ_zero (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategorySimplicialObject M ((nerve C).δ 0 σ) := by
  rw [SimplicialObject.δ, ιCategorySimplicialObject_map]
  -- `(SimplexCategory.δ 0).toOrderHom 0 = 1` and `(nerve C).δ 0 = (nerve C).map (δ 0).op` by def.
  rfl

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_δ_succ (M : C ⥤ A) {n : ℕ}
    (j : Fin (n + 1)) (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ j.succ =
      ιCategorySimplicialObject M ((nerve C).δ j.succ σ) := by
  rw [SimplicialObject.δ, ιCategorySimplicialObject_map,
    σ.map_homOfLE_eq_eqToHom (rfl : (SimplexCategory.δ j.succ).toOrderHom 0 = 0), eqToHom_map]
  exact Category.id_comp _

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (τ : ComposableArrows C n) :
    ιCategorySimplicialObject M τ ≫ (categorySimplicialObject C M).σ i =
      ιCategorySimplicialObject M ((nerve C).σ i τ) := by
  rw [SimplicialObject.σ, ιCategorySimplicialObject_map,
    τ.map_homOfLE_eq_eqToHom (rfl : (SimplexCategory.σ i).toOrderHom 0 = 0), eqToHom_map]
  exact Category.id_comp _

/-- Morphism of simplicial objects induced by `α : M ⟶ N`. -/
def categorySimplicialObjectCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObject C M ⟶ categorySimplicialObject C N where
  app Δ := Sigma.desc fun σ ↦
    α.app (σ.obj 0) ≫ Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦ N.obj (τ.obj 0)) σ
  naturality {Δ₁ Δ₂} f := by
    dsimp [categorySimplicialObject]; ext σ; simp [ComposableArrows.whiskerLeft, α.naturality_assoc]

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_coeffMap_app {M N : C ⥤ A} (α : M ⟶ N)
    {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObjectCoeffMap α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ιCategorySimplicialObject N σ := Sigma.ι_comp_desc _ _

@[simp] lemma categorySimplicialObjectCoeffMap_id (M : C ⥤ A) :
    categorySimplicialObjectCoeffMap (𝟙 M) = 𝟙 (categorySimplicialObject C M) :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

@[reassoc] lemma categorySimplicialObjectCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) :
    categorySimplicialObjectCoeffMap (α ≫ β) =
      categorySimplicialObjectCoeffMap α ≫ categorySimplicialObjectCoeffMap β :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

/-- Morphism of simplicial objects induced by `F : C ⥤ D` and `M : D ⥤ A`. -/
def categorySimplicialObjectMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject C (F ⋙ M) ⟶ categorySimplicialObject D M where
  app Δ := Sigma.desc fun σ ↦
    Sigma.ι (fun τ : ComposableArrows D Δ.unop.len ↦ M.obj (τ.obj 0))
      ((F.mapComposableArrows Δ.unop.len).obj σ)
  naturality {Δ₁ Δ₂} f := by
    dsimp only [categorySimplicialObject, ComposableArrows.whiskerLeft]; ext σ
    simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, Functor.comp_map,
      Functor.mapComposableArrows_obj_map]
    -- `whiskerLeft` commutes definitionally with postcomposing by `F` (`mapComposableArrows`).
    rfl

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_categorySimplicialObjectMap_app
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject (F ⋙ M) σ ≫ (categorySimplicialObjectMap F M).app (op ⦋n⦌) =
      ιCategorySimplicialObject M ((F.mapComposableArrows n).obj σ) := Sigma.ι_comp_desc _ _

@[simp] lemma categorySimplicialObjectMap_id (M : C ⥤ A) :
    categorySimplicialObjectMap (𝟭 C) M = 𝟙 (categorySimplicialObject C M) :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ by
    rw [ιCategorySimplicialObject_categorySimplicialObjectMap_app]
    simp [Functor.mapComposableArrows, Functor.comp_id, Functor.id_comp])

@[reassoc] lemma categorySimplicialObjectMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categorySimplicialObjectMap (F ⋙ G) M =
      categorySimplicialObjectMap F (G ⋙ M) ≫ categorySimplicialObjectMap G M :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ by
    rw [ιCategorySimplicialObject_categorySimplicialObjectMap_app]
    -- `(F ⋙ G) ⋙ M` and `F ⋙ G ⋙ M` agree definitionally on objects and morphisms.
    change _ = ιCategorySimplicialObject (F ⋙ G ⋙ M) σ ≫ _
    simp [Functor.mapComposableArrows, Functor.assoc])

/-- `categorySimplicialObjectMap F` is natural in coefficient transformations `α : M ⟶ N`. -/
@[reassoc] lemma categorySimplicialObjectMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categorySimplicialObjectCoeffMap (Functor.whiskerLeft F α) ≫ categorySimplicialObjectMap F N =
      categorySimplicialObjectMap F M ≫ categorySimplicialObjectCoeffMap α :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

end SimplicialLemmas

/-- Functoriality of `categorySimplicialObject` in `M : C ⥤ A`. -/
abbrev categorySimplicialObjectFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ SimplicialObject A :=
  { obj := categorySimplicialObject C, map := categorySimplicialObjectCoeffMap
    map_id := categorySimplicialObjectCoeffMap_id
    map_comp := categorySimplicialObjectCoeffMap_comp }

/-- Identification of `categorySimplicialObject` for constant coefficients with
`((SimplicialObject.whiskering _ _).obj (sigmaConst.obj X)).obj (nerve C)`
(`nerve C ⋙ sigmaConst.obj X`). -/
def categorySimplicialObjectConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) : categorySimplicialObject C ((Functor.const C).obj X) ≅
      (SimplicialObject.whiskering _ _ |>.obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents (fun Δ ↦
    { hom := Sigma.desc fun σ ↦ Sigma.ι (fun _ : (nerve C).obj Δ ↦ X) σ
      inv := Sigma.desc fun σ ↦ Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦
        ((Functor.const C).obj X).obj (τ.obj 0)) σ
      hom_inv_id := by dsimp [categorySimplicialObject]; ext σ; simp
      inv_hom_id := by dsimp [categorySimplicialObject]; ext σ; simp })
    (fun f ↦ by
      dsimp [categorySimplicialObject, Sigma.map']
      ext σ
      simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.id_comp]
      -- `(nerve C).obj _` is `ComposableArrows C _` and `(nerve C).map f` is `whiskerLeft`.
      exact (Sigma.ι_comp_desc
        (fun a : (nerve C).obj _ ↦ Sigma.ι (fun _ ↦ X) ((nerve C).map f a)) σ).symm)

@[reassoc (attr := simp)] lemma ιCategorySimplicialObject_constIso_hom {C : Type u}
    [Category.{v} C] [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject ((Functor.const C).obj X) σ ≫
      (categorySimplicialObjectConstIso C X).hom.app (op ⦋n⦌) =
      Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ := Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)] lemma ι_categorySimplicialObjectConstIso_inv {C : Type u}
    [Category.{v} C] [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ ≫
      (categorySimplicialObjectConstIso C X).inv.app (op ⦋n⦌) =
      ιCategorySimplicialObject ((Functor.const C).obj X) σ := Sigma.ι_comp_desc _ _

end SimplicialObject

section ChainComplex

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The category chain complex of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryChainComplex (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj (categorySimplicialObject C M)

/-- Functor sending `M : C ⥤ A` to `categoryChainComplex C M`. -/
abbrev categoryChainComplexFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ AlgebraicTopology.alternatingFaceMapComplex A

/-- Comparison of `categoryChainComplex` for constant coefficients with `(nerve C).chainComplex`. -/
def categoryChainComplexConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) : categoryChainComplex C ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

section ChainComplexLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- `categorySimplicialObjectFunctor C A` is an additive functor, supplying additivity and
preservation of zero morphisms for `categoryChainComplexFunctor C A` and
`categoryHomologyFunctor C A n`. -/
instance : (categorySimplicialObjectFunctor C A).Additive where
  map_add {_ _} _ _ :=
    NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

/-- Chain map induced by a natural transformation `α : M ⟶ N`. -/
def categoryChainComplexCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex C M ⟶ categoryChainComplex C N :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectCoeffMap α)

lemma categoryChainComplexCoeffMap_def {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplexCoeffMap α =
      (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectCoeffMap α) :=
  (rfl)

@[simp] lemma categoryChainComplexCoeffMap_id (M : C ⥤ A) :
    categoryChainComplexCoeffMap (𝟙 M) = 𝟙 (categoryChainComplex C M) := by
  simp [categoryChainComplexCoeffMap_def]

@[reassoc] lemma categoryChainComplexCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) :
    categoryChainComplexCoeffMap (α ≫ β) =
      categoryChainComplexCoeffMap α ≫ categoryChainComplexCoeffMap β := by
  simp only [categoryChainComplexCoeffMap_def, categorySimplicialObjectCoeffMap_comp,
    Functor.map_comp]

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n` of the `σ`-summand. -/
abbrev ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n := ιCategorySimplicialObject M σ

/-- Degree-`0` summand inclusion at a vertex `c : C`. -/
def ιCategoryChainComplex₀ (M : C ⥤ A) (c : C) : M.obj c ⟶ (categoryChainComplex C M).X 0 :=
  ιCategoryChainComplex M (ComposableArrows.mk₀ c)

/-- Degree-`1` summand inclusion at an arrow `f : c₀ ⟶ c₁`. -/
def ιCategoryChainComplex₁ (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 1 := ιCategoryChainComplex M (ComposableArrows.mk₁ f)

/-- Degree-`2` summand inclusion at a composable pair `(f, g)`. -/
def ιCategoryChainComplex₂ (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 2 := ιCategoryChainComplex M (ComposableArrows.mk₂ f g)

@[simp] lemma ιCategoryChainComplex_mk₀ (M : C ⥤ A) (c : C) :
    ιCategoryChainComplex M (ComposableArrows.mk₀ c) = ιCategoryChainComplex₀ M c := (rfl)

@[simp] lemma ιCategoryChainComplex_mk₁ (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ιCategoryChainComplex M (ComposableArrows.mk₁ f) = ιCategoryChainComplex₁ M f := (rfl)

@[simp] lemma ιCategoryChainComplex_mk₂ (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    ιCategoryChainComplex M (ComposableArrows.mk₂ f g) = ιCategoryChainComplex₂ M f g := (rfl)

/-- Colimit cofan presenting `(categoryChainComplex C M).X n` as `∐_{σ ∈ NₙC} M(σ₀)`. -/
abbrev categoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) := Cofan.mk _ (ιCategoryChainComplex M)

/-- `categoryChainComplexXCofan M n` is a coproduct colimit. -/
def isColimitCategoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categoryChainComplexXCofan M n) := isColimitCategorySimplicialObjectXCofan M n

@[ext] lemma categoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categoryChainComplex C M).X n ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategoryChainComplex M σ ≫ f = ιCategoryChainComplex M σ ≫ g) : f = g :=
  categorySimplicialObject_hom_ext h

lemma categoryChainComplex_hom_ext₀ {M : C ⥤ A} {T : A}
    {f g : (categoryChainComplex C M).X 0 ⟶ T}
    (h : ∀ c : C, ιCategoryChainComplex₀ M c ≫ f = ιCategoryChainComplex₀ M c ≫ g) : f = g :=
  categoryChainComplex_hom_ext fun σ ↦ by obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective σ; exact h c

/-- Transport `ιCategoryChainComplex` along an equality of simplices `σ = τ`. -/
@[reassoc] lemma eqToHom_ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} {σ τ : ComposableArrows C n}
    (h : σ = τ) (h₀ : M.obj (σ.obj 0) = M.obj (τ.obj 0) := by rw [h]) :
    eqToHom h₀ ≫ ιCategoryChainComplex M τ = ιCategoryChainComplex M σ := by subst h; simp

/-- Alternating-face boundary formula on the `σ`-summand of `categoryChainComplex C M`. -/
@[reassoc] lemma ιCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1),
          (-1) ^ (j.val + 1) • ιCategoryChainComplex M ((nerve C).δ j.succ σ) := by
  dsimp only [categoryChainComplex, ιCategoryChainComplex]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Preadditive.comp_zsmul, Fin.val_zero, pow_zero, one_smul,
    ιCategorySimplicialObject_δ_zero, Fin.val_succ, ιCategorySimplicialObject_δ_succ]
  -- Both sides now agree up to `(nerve C) _⦋n + 1⦌ = ComposableArrows C (n + 1)`.
  rfl

/-- Degree-`1` boundary on an arrow `f : c₀ ⟶ c₁`. -/
@[reassoc] lemma ιCategoryChainComplex₁_d_one_zero (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ιCategoryChainComplex₁ M f ≫ (categoryChainComplex C M).d 1 0 =
      M.map f ≫ ιCategoryChainComplex₀ M c₁ - ιCategoryChainComplex₀ M c₀ := by
  have h₀ := ((eqToHom_ιCategoryChainComplex M (ComposableArrows.ext₀ rfl :
    (nerve C).δ 0 (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ c₁) rfl).symm.trans
      (Category.id_comp _)).trans (ιCategoryChainComplex_mk₀ M c₁)
  have h₁ := ((eqToHom_ιCategoryChainComplex M (ComposableArrows.ext₀ rfl :
    (nerve C).δ 1 (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ c₀) rfl).symm.trans
      (Category.id_comp _)).trans (ιCategoryChainComplex_mk₀ M c₀)
  have halg : M.map f ≫ ιCategoryChainComplex₀ M c₁ + (-1 : ℤ) ^ 1 • ιCategoryChainComplex₀ M c₀ =
      M.map f ≫ ιCategoryChainComplex₀ M c₁ - ιCategoryChainComplex₀ M c₀ := by
    simp [sub_eq_add_neg]
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₁ f)).trans
    (((congrArg (_ + ·) (Fin.sum_univ_one _)).trans ?_).trans halg)
  exact congrArg₂ (· + ·) (by simp [h₀]) (congrArg ((-1 : ℤ) ^ 1 • ·) h₁)

/-- Degree-`2` boundary on a composable pair `(f, g)`. -/
@[reassoc] lemma ιCategoryChainComplex₂_d_two_one (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁)
    (g : c₁ ⟶ c₂) :
    ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex C M).d 2 1 =
      M.map f ≫ ιCategoryChainComplex₁ M g - ιCategoryChainComplex₁ M (f ≫ g) +
        ιCategoryChainComplex₁ M f := by
  have h₀ := ((eqToHom_ιCategoryChainComplex M (CategoryTheory.nerve.δ₀_mk₂_eq f g) rfl).symm.trans
    (Category.id_comp _)).trans (ιCategoryChainComplex_mk₁ M g)
  have h₁ := ((eqToHom_ιCategoryChainComplex M (CategoryTheory.nerve.δ₁_mk₂_eq f g) rfl).symm.trans
    (Category.id_comp _)).trans (ιCategoryChainComplex_mk₁ M (f ≫ g))
  have h₂ := ((eqToHom_ιCategoryChainComplex M (CategoryTheory.nerve.δ₂_mk₂_eq f g) rfl).symm.trans
    (Category.id_comp _)).trans (ιCategoryChainComplex_mk₁ M f)
  have halg : M.map f ≫ ιCategoryChainComplex₁ M g +
      ((-1 : ℤ) ^ 1 • ιCategoryChainComplex₁ M (f ≫ g) +
        (-1 : ℤ) ^ 2 • ιCategoryChainComplex₁ M f) =
      M.map f ≫ ιCategoryChainComplex₁ M g - ιCategoryChainComplex₁ M (f ≫ g) +
        ιCategoryChainComplex₁ M f := by
    simp [sub_eq_add_neg, add_assoc]
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₂ f g)).trans
    (((congrArg (_ + ·) (Fin.sum_univ_two _)).trans ?_).trans halg)
  exact congrArg₂ (· + ·) (by simp [h₀])
    (congrArg₂ (· + ·) (congrArg ((-1 : ℤ) ^ 1 • ·) h₁) (congrArg ((-1 : ℤ) ^ 2 • ·) h₂))

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_categoryChainComplexCoeffMap_f
    {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexCoeffMap α).f n =
      α.app (σ.obj 0) ≫ ιCategoryChainComplex N σ :=
  ιCategorySimplicialObject_coeffMap_app α σ

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_categoryChainComplexCoeffMap_f
    {M N : C ⥤ A} (α : M ⟶ N) (c : C) :
    ιCategoryChainComplex₀ M c ≫ (categoryChainComplexCoeffMap α).f 0 =
      α.app c ≫ ιCategoryChainComplex₀ N c :=
  ιCategorySimplicialObject_coeffMap_app α (ComposableArrows.mk₀ c)

/-- Chain map `categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M` along `F : C ⥤ D`. -/
def categoryChainComplexMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectMap F M)

lemma categoryChainComplexMap_def {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) : categoryChainComplexMap F M =
      (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectMap F M) := (rfl)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex (F ⋙ M) σ ≫ (categoryChainComplexMap F M).f n =
      ιCategoryChainComplex M ((F.mapComposableArrows n).obj σ) :=
  ιCategorySimplicialObject_categorySimplicialObjectMap_app F M σ

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (c : C) :
    ιCategoryChainComplex₀ (F ⋙ M) c ≫ (categoryChainComplexMap F M).f 0 =
      ιCategoryChainComplex₀ M (F.obj c) :=
  (ιCategoryChainComplex_categoryChainComplexMap_f F M (ComposableArrows.mk₀ c)).trans <|
    ((eqToHom_ιCategoryChainComplex M (ComposableArrows.ext₀ rfl :
      (F.mapComposableArrows 0).obj (ComposableArrows.mk₀ c) =
        ComposableArrows.mk₀ (F.obj c)) rfl).symm.trans (Category.id_comp _))

@[simp] lemma categoryChainComplexMap_id (M : C ⥤ A) :
    categoryChainComplexMap (𝟭 C) M = 𝟙 (categoryChainComplex C M) := by
  rw [categoryChainComplexMap_def, categorySimplicialObjectMap_id]
  exact (AlgebraicTopology.alternatingFaceMapComplex A).map_id _

@[reassoc] lemma categoryChainComplexMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexMap (F ⋙ G) M =
      categoryChainComplexMap F (G ⋙ M) ≫ categoryChainComplexMap G M := by
  simp only [categoryChainComplexMap_def, categorySimplicialObjectMap_comp, Functor.map_comp]

/-- `categoryChainComplexMap F` is natural in coefficient transformations `α : M ⟶ N`. -/
@[reassoc] lemma categoryChainComplexMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categoryChainComplexCoeffMap (Functor.whiskerLeft F α) ≫ categoryChainComplexMap F N =
      categoryChainComplexMap F M ≫ categoryChainComplexCoeffMap α := by
  simp only [categoryChainComplexCoeffMap_def, categoryChainComplexMap_def, ← Functor.map_comp,
    categorySimplicialObjectMap_naturality]

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_constIso_hom (X : A) {n : ℕ}
    (σ : ComposableArrows C n) : ιCategoryChainComplex ((Functor.const C).obj X) σ ≫
      (categoryChainComplexConstIso C X).hom.f n = (nerve C).ιChainComplex σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

@[reassoc (attr := simp)] lemma ιChainComplex_constIso_inv (X : A) {n : ℕ}
    (σ : ComposableArrows C n) : (nerve C).ιChainComplex σ ≫
      (categoryChainComplexConstIso C X).inv.f n =
      ιCategoryChainComplex ((Functor.const C).obj X) σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

/-- Under `categoryChainComplexConstIso`, `categoryChainComplexMap F` agrees with
`SSet.chainComplexMap (nerveMap F) X`. -/
@[reassoc] lemma categoryChainComplexMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) :
    categoryChainComplexMap F ((Functor.const D).obj X) ≫
      (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  refine HomologicalComplex.Hom.ext (funext fun n ↦ categoryChainComplex_hom_ext fun σ ↦ ?_)
  -- `F ⋙ (Functor.const D).obj X` is definitionally `(Functor.const C).obj X`, and `(nerve C) _⦋n⦌`
  -- is definitionally `ComposableArrows C n`.
  let σ' : (nerve C) _⦋n⦌ := σ
  change ιCategoryChainComplex (F ⋙ (Functor.const D).obj X) σ ≫ _ =
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫ _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ιCategoryChainComplex_categoryChainComplexMap_f_assoc, ιCategoryChainComplex_constIso_hom,
    ιCategoryChainComplex_constIso_hom_assoc,
    SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X σ']
  -- `(nerveMap F).app (op ⦋n⦌)` acts by `(F.mapComposableArrows n).obj` by definition.
  rfl

/-- For an empty category `C`, `categoryChainComplex C M` is a zero chain complex. -/
lemma isZero_categoryChainComplex_of_isEmpty [IsEmpty C] (M : C ⥤ A) :
    IsZero (categoryChainComplex C M) := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.Hom.ext (funext fun _ ↦ categoryChainComplex_hom_ext fun σ ↦
    (IsEmpty.false (σ.obj 0)).elim)

end ChainComplexLemmas

end ChainComplex

section Homology

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [CategoryWithHomology A]

/-- Degree-`n` category homology `Hₙ(C, M)` of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryHomology (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) (n : ℕ) : A := (categoryChainComplex C M).homology n

/-- Functor `(C ⥤ A) ⥤ A` sending `M` to `categoryHomology C M n`. -/
abbrev categoryHomologyFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A]
    [CategoryWithHomology A] (n : ℕ) : (C ⥤ A) ⥤ A :=
  categoryChainComplexFunctor C A ⋙ HomologicalComplex.homologyFunctor A _ n

/-- Comparison of `categoryHomology` for constant coefficients with `(nerve C).homology X n`. -/
def categoryHomologyConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) (n : ℕ) : categoryHomology C ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  (HomologicalComplex.homologyFunctor A _ n).mapIso (categoryChainComplexConstIso C X)

@[simp] lemma categoryHomologyConstIso_hom (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) (n : ℕ) : (categoryHomologyConstIso C X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).hom n := (rfl)

@[simp] lemma categoryHomologyConstIso_inv (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) (n : ℕ) : (categoryHomologyConstIso C X n).inv =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).inv n := (rfl)

section HomologyLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Homology map `Hₙ(C, M) ⟶ Hₙ(C, N)` induced by `α : M ⟶ N`. -/
abbrev categoryHomologyCoeffMap {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomology C M n ⟶ categoryHomology C N n :=
  HomologicalComplex.homologyMap (categoryChainComplexCoeffMap α) n

@[simp] lemma categoryHomologyCoeffMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyCoeffMap (𝟙 M) n = 𝟙 (categoryHomology C M n) := by
  simp [categoryHomologyCoeffMap]

@[reassoc] lemma categoryHomologyCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (α ≫ β) n =
      categoryHomologyCoeffMap α n ≫ categoryHomologyCoeffMap β n := by
  simp only [categoryHomologyCoeffMap, categoryChainComplexCoeffMap_comp,
    HomologicalComplex.homologyMap_comp]

/-- Homology map `Hₙ(C, F ⋙ M) ⟶ Hₙ(D, M)` induced by `F : C ⥤ D`. -/
def categoryHomologyMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    categoryHomology C (F ⋙ M) n ⟶ categoryHomology D M n :=
  HomologicalComplex.homologyMap (categoryChainComplexMap F M) n

lemma categoryHomologyMap_def {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) : categoryHomologyMap F M n =
      HomologicalComplex.homologyMap (categoryChainComplexMap F M) n := (rfl)

@[simp] lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟭 C) M n = 𝟙 (categoryHomology C M n) := by
  rw [categoryHomologyMap_def, categoryChainComplexMap_id]
  exact HomologicalComplex.homologyMap_id _ n

@[reassoc] lemma categoryHomologyMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyMap (F ⋙ G) M n =
      categoryHomologyMap F (G ⋙ M) n ≫ categoryHomologyMap G M n := by
  simp only [categoryHomologyMap_def, categoryChainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

/-- `categoryHomologyMap F` is natural in coefficient transformations `α : M ⟶ N`. -/
@[reassoc] lemma categoryHomologyMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (Functor.whiskerLeft F α) n ≫ categoryHomologyMap F N n =
      categoryHomologyMap F M n ≫ categoryHomologyCoeffMap α n := by
  simp only [categoryHomologyCoeffMap, categoryHomologyMap_def,
    ← HomologicalComplex.homologyMap_comp, categoryChainComplexMap_naturality]

/-- Under `categoryHomologyConstIso`, `categoryHomologyMap F` agrees with
`SSet.homologyMap (nerveMap F) X n`. -/
@[reassoc] lemma categoryHomologyMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) (n : ℕ) :
    categoryHomologyMap F ((Functor.const D).obj X) n ≫
      (categoryHomologyConstIso D X n).hom =
      (categoryHomologyConstIso C X n).hom ≫ SSet.homologyMap (nerveMap F) X n := by
  rw [categoryHomologyMap_def, categoryHomologyConstIso_hom, categoryHomologyConstIso_hom,
    SSet.homologyMap, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexMap_constIso_hom]

/-- For an empty category `C`, `categoryHomology C M n` is zero in every degree `n`. -/
lemma isZero_categoryHomology_of_isEmpty [IsEmpty C] (M : C ⥤ A) (n : ℕ) :
    IsZero (categoryHomology C M n) := by
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id,
    (isZero_categoryChainComplex_of_isEmpty M).eq_of_src (𝟙 _) 0,
    HomologicalComplex.homologyMap_zero]

end HomologyLemmas

end Homology

section LongExactSequence

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [Abelian A] [HasCoproducts.{max u v} A] [AB4OfSize.{max u v} A]

/-- A short exact sequence of coefficient functors `C ⥤ A` induces a short exact sequence of
category chain complexes when `AB4OfSize.{max u v} A` holds. -/
lemma shortExact_map_categoryChainComplexFunctor {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (categoryChainComplexFunctor C A)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  let J := Discrete (ComposableArrows C n)
  let W : (C ⥤ A) ⥤ (J ⥤ A) :=
    (Functor.whiskeringLeft J C A).obj (Discrete.functor fun σ ↦ σ.obj 0)
  let S₀ : ShortComplex (J ⥤ A) := S.map W
  have hS₀ : S₀.ShortExact := hS.map_of_exact W
  let cocone (M : C ⥤ A) : Cocone (W.obj M) :=
    ⟨(categoryChainComplex C M).X n, Discrete.natTrans fun j ↦ ιCategoryChainComplex M j.as⟩
  let cf {M : C ⥤ A} (s : Cocone (W.obj M)) := Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩
  let isColim (M : C ⥤ A) : IsColimit (cocone M) :=
    { desc s := (isColimitCategoryChainComplexXCofan M n).desc (cf s)
      fac s j := (isColimitCategoryChainComplexXCofan M n).fac (cf s) ⟨j.as⟩
      uniq s m hm := (isColimitCategoryChainComplexXCofan M n).uniq (cf s) m fun ⟨σ⟩ ↦ hm ⟨σ⟩ }
  have hf (j : J) : (cocone S.X₁).ι.app j ≫ (categoryChainComplexCoeffMap S.f).f n =
      S₀.f.app j ≫ (cocone S.X₂).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.f j.as
  have hg (j : J) : (cocone S.X₂).ι.app j ≫ (categoryChainComplexCoeffMap S.g).f n =
      S₀.g.app j ≫ (cocone S.X₃).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.g j.as
  have : Mono S₀.f := hS₀.mono_f; have : Epi S₀.g := hS₀.epi_g
  have (j : J) : Epi (S₀.g.app j) := inferInstance
  exact { exact := colim.exact_mapShortComplex hS₀.exact
            (isColim S.X₁) (isColim S.X₂) (isColim S.X₃) _ _ hf hg
          mono_f := colim.map_mono' S₀.f (isColim S.X₁) (isColim S.X₂) _ hf
          epi_g := colim.map_epi' S₀.g (cocone S.X₂) (isColim S.X₃) _ hg }

/-- Connecting homomorphism `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` (for `m + 1 = n`) of a short exact
sequence `S` of coefficient functors. -/
def categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) : categoryHomology C S.X₃ n ⟶ categoryHomology C S.X₁ m :=
  (shortExact_map_categoryChainComplexFunctor hS).δ n m (by simpa)

/-- The composition `Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` with `categoryHomologyδ` vanishes. -/
@[reassoc (attr := simp)] lemma comp_categoryHomologyδ {S : ShortComplex (C ⥤ A)}
    (hS : S.ShortExact) (n m : ℕ) (h : m + 1 = n := by lia) :
    categoryHomologyCoeffMap S.g n ≫ categoryHomologyδ hS n m h = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).comp_δ n m (by simpa)

/-- The composition `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁) ⟶ Hₘ(C, S.X₂)` from `categoryHomologyδ` vanishes. -/
@[reassoc (attr := simp)] lemma categoryHomologyδ_comp {S : ShortComplex (C ⥤ A)}
    (hS : S.ShortExact) (n m : ℕ) (h : m + 1 = n := by lia) :
    categoryHomologyδ hS n m h ≫ categoryHomologyCoeffMap S.f m = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).δ_comp n m (by simpa)

/-- Exactness of `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁) ⟶ Hₘ(C, S.X₂)` for `m + 1 = n`. -/
lemma categoryHomology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (categoryHomologyδ_comp hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₁ n m (by simpa)

/-- Exactness of `Hₙ(C, S.X₁) ⟶ Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃)`. -/
lemma categoryHomology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (categoryHomologyFunctor C A n)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₂ n

/-- Exactness of `Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` for `m + 1 = n`. -/
lemma categoryHomology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (comp_categoryHomologyδ hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₃ n m (by simpa)

/-- The connecting morphism `categoryHomologyδ` is natural in morphisms of short exact sequences
of coefficient functors. -/
@[reassoc] lemma categoryHomologyδ_naturality_coeff {S₁ S₂ : ShortComplex (C ⥤ A)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n m : ℕ) (h : m + 1 = n := by lia) :
    categoryHomologyδ hS₁ n m h ≫ categoryHomologyCoeffMap φ.τ₁ m =
      categoryHomologyCoeffMap φ.τ₃ n ≫ categoryHomologyδ hS₂ n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    (shortExact_map_categoryChainComplexFunctor hS₁)
    (shortExact_map_categoryChainComplexFunctor hS₂) n m (by simpa)

/-- The connecting morphism `categoryHomologyδ` commutes with `categoryHomologyMap F` along any
functor `F : C ⥤ D`. -/
@[reassoc] lemma categoryHomologyδ_naturality_functor
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A] [AB4OfSize.{max u₂ v₂} A]
    (F : C ⥤ D) {S : ShortComplex (D ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)) n m h ≫
      categoryHomologyMap F S.X₁ m =
      categoryHomologyMap F S.X₃ n ≫ categoryHomologyδ hS n m h := by
  let Φ : (S.map ((Functor.whiskeringLeft C D A).obj F)).map (categoryChainComplexFunctor C A) ⟶
      S.map (categoryChainComplexFunctor D A) :=
    { τ₁ := categoryChainComplexMap F S.X₁, τ₂ := categoryChainComplexMap F S.X₂
      τ₃ := categoryChainComplexMap F S.X₃
      comm₁₂ := (categoryChainComplexMap_naturality F S.f).symm
      comm₂₃ := (categoryChainComplexMap_naturality F S.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (shortExact_map_categoryChainComplexFunctor
      (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)))
    (shortExact_map_categoryChainComplexFunctor hS) n m (by simpa)

end LongExactSequence

end TauCeti
