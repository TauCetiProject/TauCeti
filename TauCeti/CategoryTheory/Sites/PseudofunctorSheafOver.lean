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
descent data of sheaves on slices. For a descent datum of sheaves of types, they show that its
gluing morphisms commute with restrictions (`pseudofunctorOver_descentData_hom_app_map`) and that
the gluing morphism for two equal morphisms is a restriction
(`pseudofunctorOver_descentData_hom_app_of_eq`).
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
@[simp]
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
  -- `simp` leaves `M.obj.map ((Over.mapComp a b).inv.app W).op = M.obj.map (Over.homMk _ _).op`.
  -- Both morphisms of `Over` have underlying morphism `𝟙 W.left`, so they agree on the nose
  -- (the triangle proofs agree by proof irrelevance), and `congr 2` closes the goal.
  simp
  congr 2

/-- The component at `W` of the inverse of the isomorphism `mapComp'` of
`J.pseudofunctorOver A`, as the map of the sheaf along the identification of
`(Over.map ab).obj W` with `(Over.map b).obj ((Over.map a).obj W)`. -/
@[simp]
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
  -- `simp` leaves `M.obj.map ((Over.mapComp a b).hom.app W).op = M.obj.map (Over.homMk _ _).op`.
  -- Both morphisms of `Over` have underlying morphism `𝟙 W.left`, so they agree on the nose
  -- (the triangle proofs agree by proof irrelevance), and `congr 2` closes the goal.
  simp
  congr 2

/-- The component at `W` of the gluing morphism of the descent datum of a sheaf `M` on
`J.over S` along a family `f` is the map of `M` along the identification of the two images of
`W` in `Over S`. -/
@[simp]
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
@[simp]
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
@[simp]
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

section DescentData

variable {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {D : (J.pseudofunctorOver (Type w)).DescentData f}

/-- The gluing morphisms of a descent datum of sheaves of types along `f` commute with the
restrictions along a morphism `b : Y' ⟶ Y`, up to the identifications of the objects of the
slices involved. -/
lemma pseudofunctorOver_descentData_hom_app_map {Y Y' : C} (b : Y' ⟶ Y) (q : Y ⟶ S)
    (q' : Y' ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (f₁' : Y' ⟶ X i₁) (f₂' : Y' ⟶ X i₂) (hf₁' : f₁' ≫ f i₁ = q')
    (hf₂' : f₂' ≫ f i₂ = q') (h₁ : b ≫ f₁ = f₁') (h₂ : b ≫ f₂ = f₂') {W : Over Y}
    {W' : Over Y'} (c : W'.left ⟶ W.left) (hc : c ≫ W.hom = W'.hom ≫ b)
    (x : (D.obj i₁).obj.obj (op ((Over.map f₁).obj W))) :
    (D.obj i₂).obj.map (Over.homMk c (by simp [← h₂, reassoc_of% hc]) :
        (Over.map f₂').obj W' ⟶ (Over.map f₂).obj W).op
      ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x) =
      (D.hom q' f₁' f₂' hf₁' hf₂').hom.app (op W')
        ((D.obj i₁).obj.map (Over.homMk c (by simp [← h₁, reassoc_of% hc]) :
          (Over.map f₁').obj W' ⟶ (Over.map f₁).obj W).op x) := by
  subst h₁ h₂
  have hq : b ≫ q = q' := by rw [← hf₁', ← hf₁, Category.assoc]
  let c' : (Over.map b).obj W' ⟶ W := Over.homMk c (by simpa using hc)
  -- The morphism `D.hom q' _ _` is the pullback of `D.hom q f₁ f₂` along `b`, whose components
  -- are those of `D.hom q f₁ f₂` up to the identifications `Over.homMk (𝟙 _)`.
  have key := pseudofunctorOver_pullHom_hom_app_apply (D.hom q f₁ f₂ hf₁ hf₂) b (b ≫ f₁)
    (b ≫ f₂) rfl rfl W' ((D.obj i₁).obj.map (Over.homMk c (by simp [reassoc_of% hc]) :
      (Over.map (b ≫ f₁)).obj W' ⟶ (Over.map f₁).obj W).op x)
  rw [D.pullHom_hom b q q' hq f₁ f₂ hf₁ hf₂ (b ≫ f₁) (b ≫ f₂) rfl rfl] at key
  let e₁ : (Over.map f₁).obj ((Over.map b).obj W') ⟶ (Over.map (b ≫ f₁)).obj W' :=
    Over.homMk (𝟙 _) (by simp)
  let e₂ : (Over.map (b ≫ f₂)).obj W' ⟶ (Over.map f₂).obj ((Over.map b).obj W') :=
    Over.homMk (𝟙 _) (by simp)
  refine Eq.trans ?_ key.symm
  -- Both sides restrict along morphisms with underlying morphism `c`, factored through
  -- `(Over.map b).obj W'` on the right.
  calc _ = (D.obj i₂).obj.map e₂.op ((D.obj i₂).obj.map ((Over.map f₂).map c').op
          ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x)) :=
        (congrArg (fun k ↦ (D.obj i₂).obj.map k.op ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x))
          (by ext; simp [c', e₂] : e₂ ≫ (Over.map f₂).map c' = _)).symm.trans
          (Functor.map_comp_apply _ _ _ _)
    _ = (D.obj i₂).obj.map e₂.op ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op ((Over.map b).obj W'))
          ((D.obj i₁).obj.map ((Over.map f₁).map c').op x)) :=
        congrArg (fun z ↦ (D.obj i₂).obj.map e₂.op z)
          (NatTrans.naturality_apply (D.hom q f₁ f₂ hf₁ hf₂).hom c'.op x).symm
    _ = _ :=
        congrArg (fun z ↦ (D.obj i₂).obj.map e₂.op ((D.hom q f₁ f₂ hf₁ hf₂).hom.app
          (op ((Over.map b).obj W')) z))
          ((congrArg (fun k ↦ (D.obj i₁).obj.map k.op x) (by ext; simp [c', e₁] :
            e₁ ≫ (Over.homMk c (by simp [reassoc_of% hc]) :
              (Over.map (b ≫ f₁)).obj W' ⟶ (Over.map f₁).obj W) = _)).symm.trans
            (Functor.map_comp_apply _ _ _ _))

/-- The gluing morphism of a descent datum of sheaves of types along `f` for two equal
morphisms `f₁ = f₂` is the restriction along the identification `Over.homMk (𝟙 _)`. -/
lemma pseudofunctorOver_descentData_hom_app_of_eq {Y : C} (q : Y ⟶ S) {i : ι} (f₁ f₂ : Y ⟶ X i)
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f i = q) (h : f₁ = f₂) (W : Over Y)
    (x : (D.obj i).obj.obj (op ((Over.map f₁).obj W))) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x =
      (D.obj i).obj.map (Over.homMk (𝟙 W.left) (by simp [h]) :
        (Over.map f₂).obj W ⟶ (Over.map f₁).obj W).op x := by
  subst h
  rw [D.hom_self q f₁ hf₁, show (Over.homMk (𝟙 W.left) (by simp) :
    (Over.map f₁).obj W ⟶ (Over.map f₁).obj W) = 𝟙 _ by ext; simp, op_id, Functor.map_id]
  rfl

end DescentData

end CategoryTheory.GrothendieckTopology
