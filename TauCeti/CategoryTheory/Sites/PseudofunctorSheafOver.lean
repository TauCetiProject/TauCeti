/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver

/-!
# Components of the pseudofunctor of sheaves on slices

Mathlib's pseudofunctor `J.pseudofunctorOver A`
(`CategoryTheory.GrothendieckTopology.pseudofunctorOver`, by Joël Riou) sends `X : C` to the
category of sheaves on the slice site `J.over X` and a morphism `a : Y ⟶ X` to the pullback
`J.overMapPullback A a`, whose value at `W : Over Y` is the value at `(Over.map a).obj W`.

This file computes the components of its structural isomorphisms: the components of `mapComp'`
at `W` are the maps of a sheaf along the morphisms `Over.homMk (𝟙 W.left)` that identify
`(Over.map b).obj ((Over.map a).obj W)` with `(Over.map (a ≫ b)).obj W`. It deduces the
components of the gluing morphisms of the descent datum of a sheaf
(`pseudofunctorOver_toDescentData_obj_hom_hom_app`) and of the pullback `pullHom` of a morphism
of sheaves (`pseudofunctorOver_pullHom_hom_app`). These are the formulas used to compute with
descent data of sheaves on slices.
-/

public section

universe w v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section

variable {A : Type*} [Category* A]

/-- The component at `W` of the isomorphism `mapComp'` of `J.pseudofunctorOver A`, from the
pullback along a composite `ab = a ≫ b` to the iterated pullback, is the map of the sheaf along
the identification of `(Over.map b).obj ((Over.map a).obj W)` with `(Over.map ab).obj W`. -/
lemma pseudofunctorOver_mapComp'_hom_app {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
    (h : a ≫ b = ab) (M : Sheaf (J.over Z) A) (W : Over X) :
    (((J.pseudofunctorOver A).mapComp' b.op.toLoc a.op.toLoc ab.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M).hom.app (op W) =
      M.obj.map (Over.homMk (𝟙 W.left) (by simp [← h]) :
        (Over.map b).obj ((Over.map a).obj W) ⟶ (Over.map ab).obj W).op := by
  subst h
  -- `(a ≫ b).op.toLoc` is `b.op.toLoc ≫ a.op.toLoc` only up to unfolding `Quiver.Hom.toLoc`,
  -- so `mapComp'_eq_mapComp` is rewritten up to this unfolding.
  erw [mapComp'_eq_mapComp]
  simp
  congr 2

/-- The component at `W` of the inverse of the isomorphism `mapComp'` of
`J.pseudofunctorOver A`, as the map of the sheaf along the identification of
`(Over.map ab).obj W` with `(Over.map b).obj ((Over.map a).obj W)`. -/
lemma pseudofunctorOver_mapComp'_inv_app {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
    (h : a ≫ b = ab) (M : Sheaf (J.over Z) A) (W : Over X) :
    (((J.pseudofunctorOver A).mapComp' b.op.toLoc a.op.toLoc ab.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M).hom.app (op W) =
      M.obj.map (Over.homMk (𝟙 W.left) (by simp [← h]) :
        (Over.map ab).obj W ⟶ (Over.map b).obj ((Over.map a).obj W)).op := by
  subst h
  -- `(a ≫ b).op.toLoc` is `b.op.toLoc ≫ a.op.toLoc` only up to unfolding `Quiver.Hom.toLoc`,
  -- so `mapComp'_eq_mapComp` is rewritten up to this unfolding.
  erw [mapComp'_eq_mapComp]
  simp
  congr 2

/-- The component at `W` of the gluing morphism of the descent datum of a sheaf `M` on
`J.over S` along a family `f` is the map of `M` along the identification of the two images of
`W` in `Over S`. -/
lemma pseudofunctorOver_toDescentData_obj_hom_hom_app {ι : Type*} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (M : (J.pseudofunctorOver A).obj (.mk (op S))) {Y : C} (q : Y ⟶ S)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (W : Over Y) :
    ((((J.pseudofunctorOver A).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).hom.app (op W) =
      M.obj.map (Over.homMk (𝟙 W.left) (by simp [hf₁, hf₂]) :
        (Over.map (f i₂)).obj ((Over.map f₂).obj W) ⟶
          (Over.map (f i₁)).obj ((Over.map f₁).obj W)).op := by
  refine (congrArg₂ (· ≫ ·) (pseudofunctorOver_mapComp'_inv_app f₁ (f i₁) q hf₁ M W)
    (pseudofunctorOver_mapComp'_hom_app f₂ (f i₂) q hf₂ M W)).trans
      ((M.obj.map_comp _ _).symm.trans (congrArg M.obj.map (Quiver.Hom.unop_inj (by ext; simp))))

/-- The component at `W` of the pullback `pullHom φ g` of a morphism of sheaves `φ` is the
component of `φ` at `(Over.map g).obj W`, up to the identifications of the objects of
`Over X₁` and `Over X₂` involved. -/
lemma pseudofunctorOver_pullHom_hom_app {X₁ X₂ Y Y' : C}
    {M₁ : (J.pseudofunctorOver A).obj (.mk (op X₁))}
    {M₂ : (J.pseudofunctorOver A).obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : ((J.pseudofunctorOver A).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((J.pseudofunctorOver A).map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (W : Over Y') :
    (pullHom (F := J.pseudofunctorOver A) φ g gf₁ gf₂ hgf₁ hgf₂).hom.app (op W) =
      M₁.obj.map (Over.homMk (𝟙 W.left) (by simp [← hgf₁]) :
        (Over.map f₁).obj ((Over.map g).obj W) ⟶ (Over.map gf₁).obj W).op ≫
        φ.hom.app (op ((Over.map g).obj W)) ≫
        M₂.obj.map (Over.homMk (𝟙 W.left) (by simp [← hgf₂]) :
          (Over.map gf₂).obj W ⟶ (Over.map f₂).obj ((Over.map g).obj W)).op := by
  -- The components of a composite of morphisms of sheaves are, by definition, the composites of
  -- the components.
  exact congrArg₂ (fun a b ↦ a ≫ φ.hom.app (op ((Over.map g).obj W)) ≫ b)
    (pseudofunctorOver_mapComp'_hom_app g f₁ gf₁ hgf₁ M₁ W)
    (pseudofunctorOver_mapComp'_inv_app g f₂ gf₂ hgf₂ M₂ W)

end

/-- `pseudofunctorOver_pullHom_hom_app` for sheaves of types, evaluated at a section. -/
lemma pseudofunctorOver_pullHom_hom_app_apply {X₁ X₂ Y Y' : C}
    {M₁ : (J.pseudofunctorOver (Type w)).obj (.mk (op X₁))}
    {M₂ : (J.pseudofunctorOver (Type w)).obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : ((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (W : Over Y') (y : M₁.obj.obj (op ((Over.map gf₁).obj W))) :
    (pullHom (F := J.pseudofunctorOver (Type w)) φ g gf₁ gf₂ hgf₁ hgf₂).hom.app (op W) y =
      M₂.obj.map (Over.homMk (𝟙 W.left) (by simp [← hgf₂]) :
          (Over.map gf₂).obj W ⟶ (Over.map f₂).obj ((Over.map g).obj W)).op
        (φ.hom.app (op ((Over.map g).obj W))
          (M₁.obj.map (Over.homMk (𝟙 W.left) (by simp [← hgf₁]) :
            (Over.map f₁).obj ((Over.map g).obj W) ⟶ (Over.map gf₁).obj W).op y)) :=
  congrArg (fun k ↦ k y) (pseudofunctorOver_pullHom_hom_app φ g gf₁ gf₂ hgf₁ hgf₂ W)

end CategoryTheory.GrothendieckTopology
