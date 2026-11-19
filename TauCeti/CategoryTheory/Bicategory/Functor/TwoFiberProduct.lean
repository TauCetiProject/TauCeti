/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The 2-fiber product of pseudofunctors

Let `C` be a category and `α : F ⟶ H`, `β : G ⟶ H` strong transformations between
pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. Their 2-fiber product
`TauCeti.Stack.twoFiberProduct α β` is the pseudofunctor whose fiber over `X` is Mathlib's
categorical pullback `CategoricalPullback (α.app X) (β.app X)`: an object is a triple `(x, y, e)` of
`x` over `X` for `F`, `y` over `X` for `G` and an isomorphism `e : α x ≅ β y`, and the pullback
along `f` is `(f^* x, f^* y, f^* e)`, with `f^* e` transported along the naturality isomorphisms of
`α` and `β` (Stacks, Section 4.31 (003O)). It comes with the projections `twoFiberProduct.fst` and
`twoFiberProduct.snd` and the invertible modification `twoFiberProduct.iso : fst ≫ α ≅ snd ≫ β`.

The construction uses no topology; that the 2-fiber product of stacks is a stack is proved in
`TauCeti.CategoryTheory.Sites.Descent.TwoFiberProduct`.

The fibers of `twoFiberProduct α β` are categorical pullbacks of categories in `Cat.{v', u'}`, whose
objects lie in `Type (max u' v')`; the construction is therefore stated for pseudofunctors with
values in `Cat.{v', max u' v'}`. For pseudofunctors with values in `Cat.{u, u + 1}`, as on schemes
`Scheme.{u}` or on the big site `Over S` of a scheme `S : Scheme.{u}`, take `u' := u + 1`; since
`max u' u = u + 1` does not determine `u'` by unification, this is written
`twoFiberProduct.{u + 1, u}`.

## Main declarations

* `TauCeti.Stack.twoFiberProduct`: the 2-fiber product of two strong transformations with a common
  target.
* `TauCeti.Stack.twoFiberProduct.fst`, `TauCeti.Stack.twoFiberProduct.snd`: the projections.
* `TauCeti.Stack.twoFiberProduct.iso`: the `2`-cell `fst ≫ α ≅ snd ≫ β`.

## References

* [Stacks Project, Section 003O](https://stacks.math.columbia.edu/tag/003O)
-/

open CategoryTheory Bicategory Limits CategoricalPullback Opposite
open scoped Pseudofunctor.StrongTrans

universe u' v' v u

@[expose] public section

namespace TauCeti.Stack

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

namespace twoFiberProduct

/-- The fiber of the 2-fiber product over `X`: the categorical pullback of the components of `α`
and `β` at `X`. -/
abbrev Fiber (X : Cᵒᵖ) : Type (max u' v') :=
  (α.app (.mk X)).toFunctor ⊡ (β.app (.mk X)).toFunctor

/-- The structure isomorphism `α (f^* x.fst) ≅ β (f^* x.snd)` of the pullback along `f` of an
object `x` of the fiber over `X`: the pullback of `x.iso` along `f`, transported along the
naturality isomorphisms of `α` and `β`. -/
def mapIso {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Fiber α β X) :
    (α.app (.mk Y)).toFunctor.obj ((F.map f.toLoc).toFunctor.obj x.fst) ≅
      (β.app (.mk Y)).toFunctor.obj ((G.map f.toLoc).toFunctor.obj x.snd) :=
  (Cat.Hom.toNatIso (α.naturality f.toLoc)).app x.fst ≪≫ (H.map f.toLoc).toFunctor.mapIso x.iso ≪≫
    ((Cat.Hom.toNatIso (β.naturality f.toLoc)).app x.snd).symm

@[simp]
lemma mapIso_hom {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Fiber α β X) :
    (mapIso α β f x).hom = (α.naturality f.toLoc).hom.toNatTrans.app x.fst ≫
      (H.map f.toLoc).toFunctor.map x.iso.hom ≫ (β.naturality f.toLoc).inv.toNatTrans.app x.snd :=
  (rfl)

/-- The pullback functor of the 2-fiber product along `f : X ⟶ Y` in `Cᵒᵖ`. -/
@[simps]
def map {X Y : Cᵒᵖ} (f : X ⟶ Y) : Fiber α β X ⥤ Fiber α β Y where
  obj x := ⟨(F.map f.toLoc).toFunctor.obj x.fst, (G.map f.toLoc).toFunctor.obj x.snd,
    mapIso α β f x⟩
  map φ :=
    { fst := (F.map f.toLoc).toFunctor.map φ.fst
      snd := (G.map f.toLoc).toFunctor.map φ.snd
      w := by
        have h₁ := (α.naturality f.toLoc).hom.toNatTrans.naturality φ.fst
        have h₂ := (β.naturality f.toLoc).inv.toNatTrans.naturality φ.snd
        simp only [Cat.Hom.comp_toFunctor, CategoryTheory.Functor.comp_map,
          CategoryTheory.Functor.comp_obj] at h₁ h₂
        simp only [mapIso_hom, Category.assoc]
        rw [reassoc_of% h₁, ← CategoryTheory.Functor.map_comp_assoc, φ.w,
          CategoryTheory.Functor.map_comp_assoc, h₂] }
  map_id x := by ext <;> simp
  map_comp φ ψ := by ext <;> simp

/-- The compatibility of the unit comparisons of `F` and `G` with the structure isomorphisms. -/
lemma mapId_w (X : Cᵒᵖ) (x : Fiber α β X) :
    (α.app (.mk X)).toFunctor.map ((F.mapId' (𝟙 X).toLoc).hom.toNatTrans.app x.fst) ≫
        x.iso.hom =
      (mapIso α β (𝟙 X) x).hom ≫
        (β.app (.mk X)).toFunctor.map ((G.mapId' (𝟙 X).toLoc).hom.toNatTrans.app x.snd) := by
  rw [← cancel_epi ((α.naturality (𝟙 X).toLoc).inv.toNatTrans.app x.fst)]
  simp only [mapIso_hom, Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  simp only [Pseudofunctor.StrongTrans.naturality_id'_inv_app α (𝟙 X).toLoc rfl,
    Pseudofunctor.StrongTrans.naturality_id'_inv_app β (𝟙 X).toLoc rfl, Category.assoc,
    Cat.Hom.id_toFunctor, CategoryTheory.Functor.id_obj]
  simp only [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp,
    Cat.Hom.inv_hom_id_toNatTrans_app]
  -- The identities produced by the unit comparisons live over the objects
  -- `(𝟙 (F.obj X)).toFunctor.obj x.fst`, which are only definitionally `x.fst`.
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
  exact (H.mapId'_hom_naturality _ _ _).symm

/-- The compatibility of the composition comparisons of `F` and `G` with the structure
isomorphisms. -/
lemma mapComp_w {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f.toLoc ≫ g.toLoc = fg.toLoc) (x : Fiber α β X) :
    (α.app (.mk Z)).toFunctor.map ((F.mapComp' f.toLoc g.toLoc fg.toLoc h).hom.toNatTrans.app
        x.fst) ≫ (mapIso α β g ((map α β f).obj x)).hom =
      (mapIso α β fg x).hom ≫ (β.app (.mk Z)).toFunctor.map
        ((G.mapComp' f.toLoc g.toLoc fg.toLoc h).hom.toNatTrans.app x.snd) := by
  simp only [mapIso_hom, map_obj_iso,
    Pseudofunctor.StrongTrans.naturality_comp'_hom_app α f.toLoc g.toLoc fg.toLoc h,
    Pseudofunctor.StrongTrans.naturality_comp'_inv_app β f.toLoc g.toLoc fg.toLoc h,
    Category.assoc]
  rw [H.mapComp'_naturality_1_assoc]
  simp only [← CategoryTheory.Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app,
    Cat.Hom.comp_toFunctor, CategoryTheory.Functor.comp_obj]
  -- The identity produced by `G.mapComp'` lives over `(G.map f ≫ G.map g).toFunctor.obj x.snd`,
  -- and `(map α β f).obj x` unfolds to the pair of pullbacks, both only definitionally.
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  -- The two sides now differ only in these definitionally equal objects.
  rfl

/-- The unit isomorphism of the 2-fiber product, from the unit comparisons of `F` and `G`. -/
@[simps!]
def mapIdIso (X : Cᵒᵖ) : map α β (𝟙 X) ≅ 𝟭 (Fiber α β X) :=
  mkNatIso (Functor.isoWhiskerLeft (π₁ _ _) (Cat.Hom.toNatIso (F.mapId' (𝟙 X).toLoc)))
    (Functor.isoWhiskerLeft (π₂ _ _) (Cat.Hom.toNatIso (G.mapId' (𝟙 X).toLoc)))
    (by
      ext x
      simp only [Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerLeft_app, catCommSq_iso_hom_app,
        Category.id_comp]
      -- The identity lives over `(π₂ _ _).obj x`, which is only definitionally `x.snd`.
      erw [Category.comp_id]
      exact mapId_w α β X x)

/-- The composition isomorphism of the 2-fiber product at a factorization `f ≫ g = fg`, from the
composition comparisons of `F` and `G`. -/
@[simps!]
def mapCompIso {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    map α β fg ≅ map α β f ⋙ map α β g :=
  mkNatIso (Functor.isoWhiskerLeft (π₁ _ _)
      (Cat.Hom.toNatIso (F.mapComp' f.toLoc g.toLoc fg.toLoc (congrArg Quiver.Hom.toLoc h))))
    (Functor.isoWhiskerLeft (π₂ _ _)
      (Cat.Hom.toNatIso (G.mapComp' f.toLoc g.toLoc fg.toLoc (congrArg Quiver.Hom.toLoc h))))
    (by
      ext x
      simp only [Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerLeft_app, catCommSq_iso_hom_app,
        Category.id_comp]
      -- The identity lives over `(π₂ _ _).obj x`, which is only definitionally `x.snd`.
      erw [Category.comp_id]
      exact mapComp_w α β f g fg (congrArg Quiver.Hom.toLoc h) x)

end twoFiberProduct

open twoFiberProduct in
/-- The 2-fiber product of two strong transformations `α : F ⟶ H` and `β : G ⟶ H` of
pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`: its fiber over `X` is the categorical pullback of
`α.app X` and `β.app X`, and its pullback functors and comparisons are those of `F` and `G`
(Stacks, Section 4.31 (003O)). -/
def twoFiberProduct : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun X ↦ Cat.of (Fiber α β X)) (map α β)
    (mapIdIso α β) (mapCompIso α β)
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' x ↦ by
      apply CategoricalPullback.hom_ext
      · exact F.mapComp'_hom_app_comp_map_mapComp'_hom_app _ _ _ _ _ _
          (congrArg Quiver.Hom.toLoc hfg) (congrArg Quiver.Hom.toLoc hgh)
          (congrArg Quiver.Hom.toLoc hfgh) (congrArg Quiver.Hom.toLoc hfgh') _
      · exact G.mapComp'_hom_app_comp_map_mapComp'_hom_app _ _ _ _ _ _
          (congrArg Quiver.Hom.toLoc hfg) (congrArg Quiver.Hom.toLoc hgh)
          (congrArg Quiver.Hom.toLoc hfgh) (congrArg Quiver.Hom.toLoc hfgh') _)
    (fun f hf x ↦ by
      apply CategoricalPullback.hom_ext
      · exact F.mapComp'_hom_app_comp_map_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _
      · exact G.mapComp'_hom_app_comp_map_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _)
    (fun f hf x ↦ by
      apply CategoricalPullback.hom_ext
      · exact F.mapComp'_hom_app_comp_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _
      · exact G.mapComp'_hom_app_comp_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _)

namespace twoFiberProduct

/-! ### Components of the 2-fiber product

The fibers `(twoFiberProduct α β).obj X` are categorical pullbacks only after unfolding
`twoFiberProduct`, so the following projection lemmas are stated on them directly. -/

@[simp]
lemma comp_fst' {X : LocallyDiscrete Cᵒᵖ} {x y z : (twoFiberProduct α β).obj X} (f : x ⟶ y)
    (g : y ⟶ z) : (f ≫ g).fst = f.fst ≫ g.fst :=
  (rfl)

@[simp]
lemma comp_snd' {X : LocallyDiscrete Cᵒᵖ} {x y z : (twoFiberProduct α β).obj X} (f : x ⟶ y)
    (g : y ⟶ z) : (f ≫ g).snd = f.snd ≫ g.snd :=
  (rfl)

@[simp]
lemma id_fst' {X : LocallyDiscrete Cᵒᵖ} (x : (twoFiberProduct α β).obj X) :
    Hom.fst (𝟙 x) = 𝟙 x.fst :=
  (rfl)

@[simp]
lemma id_snd' {X : LocallyDiscrete Cᵒᵖ} (x : (twoFiberProduct α β).obj X) :
    Hom.snd (𝟙 x) = 𝟙 x.snd :=
  (rfl)

@[simp]
lemma map_obj_fst' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).map f).toFunctor.obj x).fst = (F.map f).toFunctor.obj x.fst :=
  (rfl)

@[simp]
lemma map_obj_snd' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).map f).toFunctor.obj x).snd = (G.map f).toFunctor.obj x.snd :=
  (rfl)

/-- The structure isomorphism of a pullback in the 2-fiber product. -/
lemma map_obj_iso' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).map f).toFunctor.obj x).iso = mapIso α β f.as x :=
  (rfl)

@[simp]
lemma map_map_fst' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (twoFiberProduct α β).obj X}
    (φ : x ⟶ y) :
    (((twoFiberProduct α β).map f).toFunctor.map φ).fst = (F.map f).toFunctor.map φ.fst :=
  (rfl)

@[simp]
lemma map_map_snd' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (twoFiberProduct α β).obj X}
    (φ : x ⟶ y) :
    (((twoFiberProduct α β).map f).toFunctor.map φ).snd = (G.map f).toFunctor.map φ.snd :=
  (rfl)

-- In the following lemmas, after `subst`, the comparison `(twoFiberProduct α β).mapComp f g` is
-- by construction the isomorphism with components `F.mapComp' f g (f ≫ g) rfl` and
-- `G.mapComp' f g (f ≫ g) rfl`, and similarly for the unit comparisons.

@[simp]
lemma mapId'_hom_app_fst {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapId' f hf).hom.toNatTrans.app x).fst =
      (F.mapId' f hf).hom.toNatTrans.app x.fst := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapId'_inv_app_fst {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapId' f hf).inv.toNatTrans.app x).fst =
      (F.mapId' f hf).inv.toNatTrans.app x.fst := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapId'_hom_app_snd {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapId' f hf).hom.toNatTrans.app x).snd =
      (G.mapId' f hf).hom.toNatTrans.app x.snd := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapId'_inv_app_snd {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapId' f hf).inv.toNatTrans.app x).snd =
      (G.mapId' f hf).inv.toNatTrans.app x.snd := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapComp'_hom_app_fst {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).hom.toNatTrans.app x.fst := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapComp'_inv_app_fst {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).inv.toNatTrans.app x.fst := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapComp'_hom_app_snd {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).hom.toNatTrans.app x.snd := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β)]
  rfl

@[simp]
lemma mapComp'_inv_app_snd {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFiberProduct α β).obj X) :
    (((twoFiberProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).inv.toNatTrans.app x.snd := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β)]
  rfl

/-! ### The projections and the `2`-cell -/

/-- The first projection `twoFiberProduct α β ⟶ F`, with components the first projections of the
categorical pullbacks. -/
def fst : twoFiberProduct α β ⟶ F where
  app X := (π₁ (α.app X).toFunctor (β.app X).toFunctor).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 _)
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id X := by
    ext x
    -- The naturality isomorphisms are identities between `1`-morphisms that agree only
    -- definitionally, so the whiskered identities are evaluated by `change`.
    change 𝟙 _ ≫ (F.mapId X).hom.toNatTrans.app x.fst =
      (((twoFiberProduct α β).mapId X).hom.toNatTrans.app x).fst ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β), mapId'_hom_app_fst,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 (F.obj X)).toFunctor.obj x.fst`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `naturality_id`.
    change 𝟙 _ ≫ (F.mapComp f g).hom.toNatTrans.app x.fst =
      (((twoFiberProduct α β).mapComp f g).hom.toNatTrans.app x).fst ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (F.map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β), mapComp'_hom_app_fst,
      Pseudofunctor.mapComp'_eq_mapComp]
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    -- The remaining identities live over objects that are only definitionally `F`-pullbacks.
    erw [Category.comp_id, Category.comp_id]

/-- The second projection `twoFiberProduct α β ⟶ G`, with components the second projections of
the categorical pullbacks. -/
def snd : twoFiberProduct α β ⟶ G where
  app X := (π₂ (α.app X).toFunctor (β.app X).toFunctor).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 _)
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id X := by
    ext x
    -- As for `fst`.
    change 𝟙 _ ≫ (G.mapId X).hom.toNatTrans.app x.snd =
      (((twoFiberProduct α β).mapId X).hom.toNatTrans.app x).snd ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (twoFiberProduct α β), mapId'_hom_app_snd,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 (G.obj X)).toFunctor.obj x.snd`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `fst`.
    change 𝟙 _ ≫ (G.mapComp f g).hom.toNatTrans.app x.snd =
      (((twoFiberProduct α β).mapComp f g).hom.toNatTrans.app x).snd ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (G.map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (twoFiberProduct α β), mapComp'_hom_app_snd,
      Pseudofunctor.mapComp'_eq_mapComp]
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    -- The remaining identities live over objects that are only definitionally `G`-pullbacks.
    erw [Category.comp_id, Category.comp_id]

@[simp]
lemma fst_app_toFunctor (X : LocallyDiscrete Cᵒᵖ) :
    ((fst α β).app X).toFunctor = π₁ (α.app X).toFunctor (β.app X).toFunctor :=
  (rfl)

@[simp]
lemma snd_app_toFunctor (X : LocallyDiscrete Cᵒᵖ) :
    ((snd α β).app X).toFunctor = π₂ (α.app X).toFunctor (β.app X).toFunctor :=
  (rfl)

/-- The `2`-cell `fst ≫ α ≅ snd ≫ β` of the 2-fiber product, with components the structure
isomorphisms of the objects of the categorical pullbacks. -/
def iso : fst α β ≫ α ≅ snd α β ≫ β :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun x ↦ x.iso) (fun φ ↦ φ.w)))
    (fun {X Y} f ↦ by
      ext x
      rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app]
      -- The naturality isomorphisms of `fst` and `snd` are identities, and the structure
      -- isomorphism of a pullback is `mapIso`, both only definitionally.
      change ((α.naturality f).hom.toNatTrans.app x.fst ≫
          (H.map f).toFunctor.map x.iso.hom ≫ (β.naturality f).inv.toNatTrans.app x.snd) ≫
          (β.app Y).toFunctor.map (𝟙 _) ≫ (β.naturality f).hom.toNatTrans.app x.snd =
        ((α.app Y).toFunctor.map (𝟙 _) ≫ (α.naturality f).hom.toNatTrans.app x.fst) ≫
          (H.map f).toFunctor.map x.iso.hom
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
      erw [Category.id_comp, Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id])

@[simp]
lemma iso_hom_as_app_toNatTrans_app (X : LocallyDiscrete Cᵒᵖ) (x : (twoFiberProduct α β).obj X) :
    ((iso α β).hom.as.app X).toNatTrans.app x = x.iso.hom :=
  (rfl)

@[simp]
lemma iso_inv_as_app_toNatTrans_app (X : LocallyDiscrete Cᵒᵖ) (x : (twoFiberProduct α β).obj X) :
    ((iso α β).inv.as.app X).toNatTrans.app x = x.iso.inv :=
  (rfl)

/-- The pullback along `u` of the structure isomorphism of an object of the 2-fiber product,
expressed through the structure isomorphism of its pullback. -/
lemma map_iso_hom {X Y : LocallyDiscrete Cᵒᵖ} (u : X ⟶ Y) (x : (twoFiberProduct α β).obj X) :
    (H.map u).toFunctor.map x.iso.hom = (α.naturality u).inv.toNatTrans.app x.fst ≫
      (((twoFiberProduct α β).map u).toFunctor.obj x).iso.hom ≫
        (β.naturality u).hom.toNatTrans.app x.snd := by
  -- The structure isomorphism of the pullback is `mapIso`, whose source and target are only
  -- definitionally those of `((twoFiberProduct α β).map u).toFunctor.obj x`.
  change _ = _ ≫ ((α.naturality u).hom.toNatTrans.app x.fst ≫
    (H.map u).toFunctor.map x.iso.hom ≫ (β.naturality u).inv.toNatTrans.app x.snd) ≫ _
  simp

end twoFiberProduct

end TauCeti.Stack

end
