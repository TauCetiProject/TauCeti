/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import TauCeti.CategoryTheory.Bicategory.Functor.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Sites.Descent.Discrete

/-!
# The 2-Yoneda lemma for representable presheaves

Let `C` be a category, `X : C`, and `F` a `Cat`-valued pseudofunctor on `LocallyDiscrete Cᵒᵖ`,
for instance a prestack. The representable presheaf `yoneda.obj X` defines the discrete
pseudofunctor `Pseudofunctor.ofPresheaf (yoneda.obj X)`, whose fibre over `Y` is the set of
morphisms `Y ⟶ X`. This file proves the 2-Yoneda lemma: strong transformations
`ofPresheaf (yoneda.obj X) ⟶ F`, with modifications as morphisms, form a category equivalent to
the fibre `F(X)`.

The equivalence `Pseudofunctor.yonedaEquiv` sends a strong transformation `η` to the image
`η_X(𝟙 X)` of the identity of `X`. Its inverse `Pseudofunctor.yonedaPullback` sends an object `x`
of `F(X)` to the strong transformation `Pseudofunctor.yonedaPullbackObj` whose component at `Y`
sends `f : Y ⟶ X` to the pullback `F(f)(x)`, with naturality isomorphisms the composition
comparisons of `F`.

For the pseudofunctor underlying a stack in groupoids over schemes this is the identification of
morphisms `h_T → 𝒳` with objects of `𝒳(T)` (Stacks, Lemma 004B), retaining automorphisms.

## Main declarations

* `CategoryTheory.Pseudofunctor.yonedaPullbackObj`: the strong transformation
  `f ↦ F(f)(x)` attached to an object `x` of `F(X)`.
* `CategoryTheory.Pseudofunctor.yonedaPullback`: the functor
  `F(X) ⥤ (ofPresheaf (yoneda.obj X) ⟶ F)`.
* `CategoryTheory.Pseudofunctor.yonedaEvaluation`: evaluation at the identity of `X`.
* `CategoryTheory.Pseudofunctor.yonedaEquiv`: the 2-Yoneda equivalence
  `(ofPresheaf (yoneda.obj X) ⟶ F) ≌ F(X)`.

## References

* [Stacks Project, Lemma 004B](https://stacks.math.columbia.edu/tag/004B)
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Section 8.3, for the bicategorical
  Yoneda lemma.
-/

@[expose] public section

universe w' v u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory StrongTrans ofPresheaf

attribute [local instance] uliftCategory

-- The objects of the domain of `eqToHom p ≫ eqToHom q ≫ h` are only definitionally equal in the
-- coherence proofs below, so `simp` cannot merge the two `eqToHom`s there; this lemma is applied by
-- unification instead.
private lemma eqToHom_comp_eqToHom_comp {D : Type*} [Category* D] {X Y Z : D} (p : X = Y)
    (q : Y = X) (h : X ⟶ Z) : eqToHom p ≫ eqToHom q ≫ h = h := by
  simp

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, max v w'})
  (X : C)

/-- Pulling back a morphism `f : Y ⟶ X` along `g` corresponds to composing the corresponding
`1`-morphism `⟨op X⟩ ⟶ Y` of `LocallyDiscrete Cᵒᵖ` with `g`. -/
lemma toLoc_op_ofPresheaf_objEquiv_comp {Y Y' : LocallyDiscrete Cᵒᵖ}
    (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) (g : Y ⟶ Y') :
    (objEquiv Y.as a).op.toLoc ≫ g =
      (objEquiv Y'.as
        (((ofPresheaf.{w'} (yoneda.obj X)).map g).toFunctor.obj a)).op.toLoc :=
  rfl

/-- Pulling back a morphism `f : Y ⟶ X` along `g₁` and then along `g₂` corresponds to the same
`1`-morphism `⟨op X⟩ ⟶ Y''` as pulling it back along `g₁ ≫ g₂`. -/
lemma toLoc_op_ofPresheaf_objEquiv_map_map {Y Y' Y'' : LocallyDiscrete Cᵒᵖ}
    (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    (objEquiv Y''.as (((ofPresheaf.{w'} (yoneda.obj X)).map g₂).toFunctor.obj
        (((ofPresheaf.{w'} (yoneda.obj X)).map g₁).toFunctor.obj a))).op.toLoc =
      (objEquiv Y''.as
        (((ofPresheaf.{w'} (yoneda.obj X)).map (g₁ ≫ g₂)).toFunctor.obj a)).op.toLoc := by
  simp only [objEquiv_map_toFunctor_obj]
  simp

/-- The component at `Y` of `yonedaPullbackObj F X x`: the functor from the discrete category on
the morphisms `f : Y ⟶ X` to `F(Y)` sending `f` to the pullback `F(f)(x)`. -/
def yonedaPullbackApp (x : F.obj (.mk (op X))) (Y : LocallyDiscrete Cᵒᵖ) :
    (ofPresheaf.{w'} (yoneda.obj X)).obj Y ⟶ F.obj Y :=
  (ULift.downFunctor ⋙ Discrete.functor
    fun f : Y.as.unop ⟶ X ↦ (F.map f.op.toLoc).toFunctor.obj x).toCatHom

@[simp]
lemma yonedaPullbackApp_toFunctor_obj (x : F.obj (.mk (op X))) (Y : LocallyDiscrete Cᵒᵖ)
    (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) :
    (yonedaPullbackApp F X x Y).toFunctor.obj a =
      (F.map (objEquiv Y.as a).op.toLoc).toFunctor.obj x :=
  rfl

@[simp]
lemma yonedaPullbackApp_toFunctor_map (x : F.obj (.mk (op X))) (Y : LocallyDiscrete Cᵒᵖ)
    {a b : (ofPresheaf.{w'} (yoneda.obj X)).obj Y} (φ : a ⟶ b) :
    (yonedaPullbackApp F X x Y).toFunctor.map φ =
      eqToHom (by rw [IsDiscrete.eq_of_hom φ]) := by
  obtain rfl := IsDiscrete.eq_of_hom φ
  rw [Subsingleton.elim φ (𝟙 a), Functor.map_id, eqToHom_refl]

/-- The naturality isomorphism of `yonedaPullbackObj F X x` at `g : Y ⟶ Y'`: at `f : Y ⟶ X` it is
the composition comparison `F(f ≫ g)(x) ≅ F(g)(F(f)(x))` of `F`, written in
`LocallyDiscrete Cᵒᵖ`. -/
def yonedaPullbackNaturality (x : F.obj (.mk (op X))) {Y Y' : LocallyDiscrete Cᵒᵖ} (g : Y ⟶ Y') :
    (ofPresheaf.{w'} (yoneda.obj X)).map g ≫ yonedaPullbackApp F X x Y' ≅
      yonedaPullbackApp F X x Y ≫ F.map g :=
  Cat.Hom.isoMk <| IsDiscrete.natIso fun a ↦
    (Cat.Hom.toNatIso (F.mapComp' (objEquiv Y.as a).op.toLoc g
      (objEquiv Y'.as (((ofPresheaf.{w'} (yoneda.obj X)).map g).toFunctor.obj a)).op.toLoc
      (toLoc_op_ofPresheaf_objEquiv_comp X a g))).app x

@[simp]
lemma yonedaPullbackNaturality_hom_toNatTrans_app (x : F.obj (.mk (op X)))
    {Y Y' : LocallyDiscrete Cᵒᵖ} (g : Y ⟶ Y') (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) :
    (yonedaPullbackNaturality F X x g).hom.toNatTrans.app a =
      (F.mapComp' (objEquiv Y.as a).op.toLoc g
        (objEquiv Y'.as
          (((ofPresheaf.{w'} (yoneda.obj X)).map g).toFunctor.obj a)).op.toLoc
        (toLoc_op_ofPresheaf_objEquiv_comp X a g)).hom.toNatTrans.app x :=
  rfl

/-- The strong transformation `ofPresheaf (yoneda.obj X) ⟶ F` attached to an object `x` of
`F(X)`: its component at `Y` sends `f : Y ⟶ X` to `F(f)(x)`, and its naturality isomorphisms are
the composition comparisons of `F`. -/
def yonedaPullbackObj (x : F.obj (.mk (op X))) : ofPresheaf.{w'} (yoneda.obj X) ⟶ F where
  app Y := yonedaPullbackApp F X x Y
  naturality g := yonedaPullbackNaturality F X x g
  naturality_naturality η := naturality_naturality_of_locallyDiscrete _ _ _ _ η
  naturality_id Y := by
    ext a
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app]
    rw [yonedaPullbackNaturality_hom_toNatTrans_app, yonedaPullbackApp_toFunctor_map]
    refine (mapComp'_comp_id_hom_app_mapId_hom_app F _ _ _ x).trans ?_
    -- Both sides are `eqToHom`s between definitionally equal objects.
    rw [eqToHom_trans, eqToHom_trans]
    rfl
  naturality_comp g₁ g₂ := by
    ext a
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.associator_hom_app,
      Functor.associator_inv_app]
    rw [yonedaPullbackApp_toFunctor_map, yonedaPullbackNaturality_hom_toNatTrans_app,
      yonedaPullbackNaturality_hom_toNatTrans_app, yonedaPullbackNaturality_hom_toNatTrans_app,
      ← mapComp'_eq_mapComp]
    refine (mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app F _ g₁ g₂ _ (g₁ ≫ g₂) _
      (toLoc_op_ofPresheaf_objEquiv_comp X a g₁) rfl
      (toLoc_op_ofPresheaf_objEquiv_comp X a (g₁ ≫ g₂)) x).trans ?_
    rw [mapComp'_hom_toNatTrans_app_of_eq F _ g₂ _ _ (toLoc_op_ofPresheaf_objEquiv_comp X _ g₂)
      (toLoc_op_ofPresheaf_objEquiv_map_map X a g₁ g₂)]
    dsimp only [yonedaPullbackApp_toFunctor_obj, Functor.comp_obj,
      objEquiv_map_toFunctor_obj, Cat.Hom.comp_toFunctor]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    exact (eqToHom_comp_eqToHom_comp _ _ _).symm

@[simp]
lemma yonedaPullbackObj_app (x : F.obj (.mk (op X))) (Y : LocallyDiscrete Cᵒᵖ) :
    (yonedaPullbackObj F X x).app Y = yonedaPullbackApp F X x Y :=
  rfl

@[simp]
lemma yonedaPullbackObj_naturality (x : F.obj (.mk (op X))) {Y Y' : LocallyDiscrete Cᵒᵖ}
    (g : Y ⟶ Y') :
    (yonedaPullbackObj F X x).naturality g = yonedaPullbackNaturality F X x g :=
  rfl

/-- The component at `Y` of `yonedaPullbackMap F X φ`: the natural transformation with components
`F(f)(φ)`. -/
def yonedaPullbackMapApp {x y : F.obj (.mk (op X))} (φ : x ⟶ y) (Y : LocallyDiscrete Cᵒᵖ) :
    yonedaPullbackApp F X x Y ⟶ yonedaPullbackApp F X y Y where
  toNatTrans :=
    { app a := (F.map (objEquiv Y.as a).op.toLoc).toFunctor.map φ
      naturality _ _ ψ := IsDiscrete.naturality (G := (yonedaPullbackApp F X x Y).toFunctor)
        (H := (yonedaPullbackApp F X y Y).toFunctor)
        (fun a ↦ (F.map (objEquiv Y.as a).op.toLoc).toFunctor.map φ) ψ }

@[simp]
lemma yonedaPullbackMapApp_toNatTrans_app {x y : F.obj (.mk (op X))} (φ : x ⟶ y)
    (Y : LocallyDiscrete Cᵒᵖ) (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) :
    (yonedaPullbackMapApp F X φ Y).toNatTrans.app a =
      (F.map (objEquiv Y.as a).op.toLoc).toFunctor.map φ :=
  rfl

/-- The modification `yonedaPullbackObj F X x ⟶ yonedaPullbackObj F X y` induced by a morphism
`φ : x ⟶ y` of `F(X)`, with components `F(f)(φ)`. -/
def yonedaPullbackMap {x y : F.obj (.mk (op X))} (φ : x ⟶ y) :
    yonedaPullbackObj F X x ⟶ yonedaPullbackObj F X y :=
  ⟨{ app Y := yonedaPullbackMapApp F X φ Y
     naturality g := by
      ext a
      simp only [Cat.Hom₂.comp_app, yonedaPullbackObj_naturality,
        yonedaPullbackNaturality_hom_toNatTrans_app]
      exact mapComp'_hom_naturality F _ _ _ _ φ }⟩

@[simp]
lemma yonedaPullbackMap_as_app {x y : F.obj (.mk (op X))} (φ : x ⟶ y) (Y : LocallyDiscrete Cᵒᵖ) :
    (yonedaPullbackMap F X φ).as.app Y = yonedaPullbackMapApp F X φ Y :=
  rfl

/-- The functor `F(X) ⥤ (ofPresheaf (yoneda.obj X) ⟶ F)` sending `x` to the strong transformation
`f ↦ F(f)(x)`; it is the inverse of the 2-Yoneda equivalence `yonedaEquiv F X`. -/
def yonedaPullback : F.obj (.mk (op X)) ⥤ (ofPresheaf.{w'} (yoneda.obj X) ⟶ F) where
  obj := yonedaPullbackObj F X
  map := yonedaPullbackMap F X
  map_id x := by
    ext Y a
    simp
  map_comp φ ψ := by
    ext Y a
    simp

@[simp]
lemma yonedaPullback_obj (x : F.obj (.mk (op X))) :
    (yonedaPullback F X).obj x = yonedaPullbackObj F X x :=
  rfl

@[simp]
lemma yonedaPullback_map {x y : F.obj (.mk (op X))} (φ : x ⟶ y) :
    (yonedaPullback F X).map φ = yonedaPullbackMap F X φ :=
  rfl

/-- Evaluation of a strong transformation `ofPresheaf (yoneda.obj X) ⟶ F` at the identity of `X`;
it is the functor of the 2-Yoneda equivalence `yonedaEquiv F X`. -/
def yonedaEvaluation : (ofPresheaf.{w'} (yoneda.obj X) ⟶ F) ⥤ F.obj (.mk (op X)) where
  obj η := (η.app (.mk (op X))).toFunctor.obj
    ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X))
  map Γ := (Γ.as.app (.mk (op X))).toNatTrans.app
    ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X))

@[simp]
lemma yonedaEvaluation_obj (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F) :
    (yonedaEvaluation F X).obj η =
      (η.app (.mk (op X))).toFunctor.obj
        ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X)) :=
  rfl

@[simp]
lemma yonedaEvaluation_map {η θ : ofPresheaf.{w'} (yoneda.obj X) ⟶ F} (Γ : η ⟶ θ) :
    (yonedaEvaluation F X).map Γ =
      (Γ.as.app (.mk (op X))).toNatTrans.app
        ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X)) :=
  rfl

/-- The counit of the 2-Yoneda equivalence: evaluating `f ↦ F(f)(x)` at `𝟙 X` gives
`F(𝟙)(x) ≅ x`, the unit comparison of `F`. -/
def yonedaCounitIso : yonedaPullback F X ⋙ yonedaEvaluation F X ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x ↦ (Cat.Hom.toNatIso (F.mapId (.mk (op X)))).app x)
    (fun φ ↦ (F.mapId (.mk (op X))).hom.toNatTrans.naturality φ)

@[simp]
lemma yonedaCounitIso_hom_app (x : F.obj (.mk (op X))) :
    (yonedaCounitIso F X).hom.app x = (F.mapId (.mk (op X))).hom.toNatTrans.app x :=
  rfl

@[simp]
lemma yonedaCounitIso_inv_app (x : F.obj (.mk (op X))) :
    (yonedaCounitIso F X).inv.app x = (F.mapId (.mk (op X))).inv.toNatTrans.app x :=
  rfl

/-- Every object of the fibre of `ofPresheaf (yoneda.obj X)` over `Y` is the pullback of the
identity of `X` along the corresponding `1`-morphism `⟨op X⟩ ⟶ Y`. -/
lemma eq_map_obj_ofPresheaf_objEquiv_symm_id {Y : LocallyDiscrete Cᵒᵖ}
    (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) :
    a = ((ofPresheaf.{w'} (yoneda.obj X)).map (objEquiv Y.as a).op.toLoc).toFunctor.obj
      ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X)) :=
  (objEquiv.{w'} (P := yoneda.obj X) Y.as).injective (by
    simp only [objEquiv_map_toFunctor_obj, Equiv.apply_symm_apply]
    simp)

/-- The component at `Y` of the unit of the 2-Yoneda equivalence at `η`: at `f : Y ⟶ X` it is
the naturality isomorphism `η_Y(f) ≅ F(f)(η_X(𝟙 X))` of `η` at `f`. -/
def yonedaUnitApp (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F) (Y : LocallyDiscrete Cᵒᵖ) :
    η.app Y ≅ yonedaPullbackApp F X
      ((η.app (.mk (op X))).toFunctor.obj
        ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X))) Y :=
  Cat.Hom.isoMk <| IsDiscrete.natIso (D := (ofPresheaf.{w'} (yoneda.obj X)).obj Y) fun a ↦
    (η.app Y).toFunctor.mapIso (eqToIso (eq_map_obj_ofPresheaf_objEquiv_symm_id X a)) ≪≫
      (Cat.Hom.toNatIso (η.naturality (objEquiv Y.as a).op.toLoc)).app
        ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X))

@[simp]
lemma yonedaUnitApp_hom_toNatTrans_app (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F)
    (Y : LocallyDiscrete Cᵒᵖ) (a : (ofPresheaf.{w'} (yoneda.obj X)).obj Y) :
    (yonedaUnitApp F X η Y).hom.toNatTrans.app a =
      (η.app Y).toFunctor.map (eqToHom (eq_map_obj_ofPresheaf_objEquiv_symm_id X a)) ≫
        (η.naturality (objEquiv Y.as a).op.toLoc).hom.toNatTrans.app
          ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X)) :=
  rfl

/-- The unit of the 2-Yoneda equivalence at `η`: the invertible modification from `η` to the
strong transformation `f ↦ F(f)(η_X(𝟙 X))`, with components `yonedaUnitApp F X η`. -/
def yonedaUnitIsoApp (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F) :
    η ≅ yonedaPullbackObj F X ((yonedaEvaluation F X).obj η) :=
  isoMk (yonedaUnitApp F X η) fun {Y Y'} g ↦ by
    ext a
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      yonedaPullbackObj_naturality, yonedaPullbackNaturality_hom_toNatTrans_app,
      yonedaUnitApp_hom_toNatTrans_app]
    rw [naturality_comp'_hom_app η _ g _ (toLoc_op_ofPresheaf_objEquiv_comp X a g)]
    have key := (η.naturality g).hom.toNatTrans.naturality
      (eqToHom (eq_map_obj_ofPresheaf_objEquiv_symm_id X a))
    rw [Cat.Hom.comp_map, Cat.Hom.comp_map] at key
    dsimp only [yonedaEvaluation_obj, Cat.Hom.comp_toFunctor, Functor.comp_obj,
      yonedaPullbackObj_app, yonedaPullbackApp_toFunctor_obj,
      objEquiv_map_toFunctor_obj] at key ⊢
    simp only [Category.assoc, Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
    rw [← reassoc_of% key, ← Functor.map_comp_assoc]
    congr 1
    · exact Functor.congr_map _ (Subsingleton.elim _ _)
    · simp

@[simp]
lemma yonedaUnitIsoApp_hom_as_app (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F)
    (Y : LocallyDiscrete Cᵒᵖ) :
    (yonedaUnitIsoApp F X η).hom.as.app Y = (yonedaUnitApp F X η Y).hom :=
  rfl

/-- The unit of the 2-Yoneda equivalence. -/
def yonedaUnitIso : 𝟭 _ ≅ yonedaEvaluation F X ⋙ yonedaPullback F X :=
  NatIso.ofComponents (yonedaUnitIsoApp F X) fun {η θ} Γ ↦ by
    dsimp only [Functor.id_obj, Functor.comp_obj, yonedaPullback_obj, Functor.id_map,
      Functor.comp_map, yonedaPullback_map, yonedaEvaluation_obj, yonedaEvaluation_map]
    ext ⟨⟨Z⟩⟩ a
    simp only [homCategory_comp_as_app]
    dsimp only [yonedaUnitIsoApp_hom_as_app, yonedaPullbackMap_as_app, yonedaPullbackObj_app]
    rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, yonedaUnitApp_hom_toNatTrans_app,
      yonedaUnitApp_hom_toNatTrans_app, yonedaPullbackMapApp_toNatTrans_app]
    have hmod := congrArg
      (fun t ↦ t.toNatTrans.app ((objEquiv.{w'} (P := yoneda.obj X) (op X)).symm (𝟙 X)))
      (Γ.as.naturality (objEquiv _ a).op.toLoc)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at hmod
    -- Precompose the modification condition with `η_Z` of the `eqToHom` identifying `a` with a
    -- pullback of `𝟙 X`, and move it past `Γ` by naturality of `Γ_Z`. The goal itself is only
    -- type-correct up to unfolding, so the equation is assembled in the hypothesis.
    have key := (η.app _).toFunctor.map (eqToHom (eq_map_obj_ofPresheaf_objEquiv_symm_id X a)) ≫=
      hmod
    rw [reassoc_of% (Γ.as.app _).toNatTrans.naturality,
      ← Category.assoc ((η.app _).toFunctor.map _)] at key
    exact key

@[simp]
lemma yonedaUnitIso_hom_app (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F) :
    (yonedaUnitIso F X).hom.app η = (yonedaUnitIsoApp F X η).hom :=
  rfl

@[simp]
lemma yonedaUnitIso_inv_app (η : ofPresheaf.{w'} (yoneda.obj X) ⟶ F) :
    (yonedaUnitIso F X).inv.app η = (yonedaUnitIsoApp F X η).inv :=
  rfl

/-- The 2-Yoneda lemma (Stacks, Lemma 004B): evaluation at the identity of `X` is an equivalence
between the category of strong transformations `ofPresheaf (yoneda.obj X) ⟶ F`, with
modifications as morphisms, and the fibre `F(X)`. Its inverse sends `x` to the strong
transformation `f ↦ F(f)(x)`. -/
@[stacks 004B]
def yonedaEquiv : (ofPresheaf.{w'} (yoneda.obj X) ⟶ F) ≌ F.obj (.mk (op X)) :=
  Equivalence.mk (yonedaEvaluation F X) (yonedaPullback F X) (yonedaUnitIso F X)
    (yonedaCounitIso F X)

@[simp]
lemma yonedaEquiv_functor : (yonedaEquiv F X).functor = yonedaEvaluation F X :=
  rfl

@[simp]
lemma yonedaEquiv_inverse : (yonedaEquiv F X).inverse = yonedaPullback F X :=
  rfl

@[simp]
lemma yonedaEquiv_counitIso : (yonedaEquiv F X).counitIso = yonedaCounitIso F X :=
  rfl

end CategoryTheory.Pseudofunctor
