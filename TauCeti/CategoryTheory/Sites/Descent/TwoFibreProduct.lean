/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The 2-fibre product of pseudofunctors

Let `C` be a category and `α : F ⟶ H`, `β : G ⟶ H` strong transformations between
pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. Their 2-fibre product
`TauCeti.Stack.twoFibreProduct α β` is the pseudofunctor whose fibre over `X` is Mathlib's
categorical pullback `CategoricalPullback (α.app X) (β.app X)`: an object is a triple `(x, y, e)` of
`x` over `X` for `F`, `y` over `X` for `G` and an isomorphism `e : α x ≅ β y`, and the pullback
along `f` is `(f^* x, f^* y, f^* e)`, with `f^* e` transported along the naturality isomorphisms of
`α` and `β` (Stacks, Section 4.31 (003O)). It comes with the projections `twoFibreProduct.fst` and
`twoFibreProduct.snd` and the invertible modification `twoFibreProduct.iso : fst ≫ α ≅ snd ≫ β`.

For a Grothendieck topology `J` on `C`, the 2-fibre product of two stacks over a prestack is a
stack (`twoFibreProduct.isStack`), and that of two prestacks over a prestack is a prestack
(`twoFibreProduct.isPrestack`) (Stacks, Lemma 8.4.6 (026G)). Both rest on statements about a single
family of morphisms `f i : X i ⟶ S`: the descent functor of the 2-fibre product is fully faithful
when those of `F` and `G` are and that of `H` is faithful
(`twoFibreProduct.fullyFaithfulToDescentData`), and essentially surjective when those of `F` and `G`
are and that of `H` is fully faithful (`twoFibreProduct.essSurj_toDescentData`).

The fibres of `twoFibreProduct α β` are categorical pullbacks of categories in `Cat.{v', u'}`, whose
objects lie in `Type (max u' v')`; the construction is therefore stated for pseudofunctors with
values in `Cat.{v', max u' v'}`. For pseudofunctors with values in `Cat.{u, u + 1}`, as on schemes
`Scheme.{u}` or on the big site `Over S` of a scheme `S : Scheme.{u}`, take `u' := u + 1`; since
`max u' u = u + 1` does not determine `u'` by unification, this is written
`twoFibreProduct.{u + 1, u}`.

## Main declarations

* `TauCeti.Stack.twoFibreProduct`: the 2-fibre product of two strong transformations with a common
  target.
* `TauCeti.Stack.twoFibreProduct.fst`, `TauCeti.Stack.twoFibreProduct.snd`: the projections.
* `TauCeti.Stack.twoFibreProduct.iso`: the `2`-cell `fst ≫ α ≅ snd ≫ β`.
* `TauCeti.Stack.twoFibreProduct.descentDataFst`, `TauCeti.Stack.twoFibreProduct.descentDataSnd`:
  the projections of descent data.
* `TauCeti.Stack.twoFibreProduct.isPrestack`, `TauCeti.Stack.twoFibreProduct.isStack`: the 2-fibre
  product of prestacks (respectively stacks) over a prestack is a prestack (respectively stack).

## References

* [Stacks Project, Section 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Lemma 026G](https://stacks.math.columbia.edu/tag/026G)
-/

open CategoryTheory Bicategory Limits CategoricalPullback Opposite
open scoped Pseudofunctor.StrongTrans

universe t u' v' v u

@[expose] public section

namespace TauCeti.Stack

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

namespace twoFibreProduct

/-- The fibre of the 2-fibre product over `X`: the categorical pullback of the components of `α`
and `β` at `X`. -/
abbrev Fibre (X : Cᵒᵖ) : Type (max u' v') :=
  (α.app (.mk X)).toFunctor ⊡ (β.app (.mk X)).toFunctor

/-- The structure isomorphism `α (f^* x.fst) ≅ β (f^* x.snd)` of the pullback along `f` of an
object `x` of the fibre over `X`: the pullback of `x.iso` along `f`, transported along the
naturality isomorphisms of `α` and `β`. -/
def mapIso {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Fibre α β X) :
    (α.app (.mk Y)).toFunctor.obj ((F.map f.toLoc).toFunctor.obj x.fst) ≅
      (β.app (.mk Y)).toFunctor.obj ((G.map f.toLoc).toFunctor.obj x.snd) :=
  (Cat.Hom.toNatIso (α.naturality f.toLoc)).app x.fst ≪≫ (H.map f.toLoc).toFunctor.mapIso x.iso ≪≫
    ((Cat.Hom.toNatIso (β.naturality f.toLoc)).app x.snd).symm

@[simp]
lemma mapIso_hom {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Fibre α β X) :
    (mapIso α β f x).hom = (α.naturality f.toLoc).hom.toNatTrans.app x.fst ≫
      (H.map f.toLoc).toFunctor.map x.iso.hom ≫ (β.naturality f.toLoc).inv.toNatTrans.app x.snd :=
  (rfl)

/-- The pullback functor of the 2-fibre product along `f : X ⟶ Y` in `Cᵒᵖ`. -/
@[simps]
def map {X Y : Cᵒᵖ} (f : X ⟶ Y) : Fibre α β X ⥤ Fibre α β Y where
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
lemma mapId_w (X : Cᵒᵖ) (x : Fibre α β X) :
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
    (h : f.toLoc ≫ g.toLoc = fg.toLoc) (x : Fibre α β X) :
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

/-- The unit isomorphism of the 2-fibre product, from the unit comparisons of `F` and `G`. -/
@[simps!]
def mapIdIso (X : Cᵒᵖ) : map α β (𝟙 X) ≅ 𝟭 (Fibre α β X) :=
  NatIso.ofComponents (fun x ↦ mkIso ((Cat.Hom.toNatIso (F.mapId' (𝟙 X).toLoc)).app x.fst)
    ((Cat.Hom.toNatIso (G.mapId' (𝟙 X).toLoc)).app x.snd) (mapId_w α β X x)) (fun φ ↦ by
      ext
      · exact F.mapId'_hom_naturality _ rfl φ.fst
      · exact G.mapId'_hom_naturality _ rfl φ.snd)

/-- The composition isomorphism of the 2-fibre product at a factorization `f ≫ g = fg`, from the
composition comparisons of `F` and `G`. -/
@[simps!]
def mapCompIso {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    map α β fg ≅ map α β f ⋙ map α β g :=
  NatIso.ofComponents (fun x ↦ mkIso
    ((Cat.Hom.toNatIso
      (F.mapComp' f.toLoc g.toLoc fg.toLoc (congrArg Quiver.Hom.toLoc h))).app x.fst)
    ((Cat.Hom.toNatIso
      (G.mapComp' f.toLoc g.toLoc fg.toLoc (congrArg Quiver.Hom.toLoc h))).app x.snd)
    (mapComp_w α β f g fg (congrArg Quiver.Hom.toLoc h) x)) (fun φ ↦ by
      ext
      · exact F.mapComp'_hom_naturality _ _ _ (congrArg Quiver.Hom.toLoc h) φ.fst
      · exact G.mapComp'_hom_naturality _ _ _ (congrArg Quiver.Hom.toLoc h) φ.snd)

end twoFibreProduct

open twoFibreProduct in
/-- The 2-fibre product of two strong transformations `α : F ⟶ H` and `β : G ⟶ H` of
pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`: its fibre over `X` is the categorical pullback of
`α.app X` and `β.app X`, and its pullback functors and comparisons are those of `F` and `G`
(Stacks, Section 4.31 (003O)). -/
def twoFibreProduct : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun X ↦ Cat.of (Fibre α β X)) (map α β)
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

namespace twoFibreProduct

/-! ### Components of the 2-fibre product

The fibres `(twoFibreProduct α β).obj X` are categorical pullbacks only after unfolding
`twoFibreProduct`, so the following projection lemmas are stated on them directly. -/

@[simp]
lemma comp_fst' {X : LocallyDiscrete Cᵒᵖ} {x y z : (twoFibreProduct α β).obj X} (f : x ⟶ y)
    (g : y ⟶ z) : (f ≫ g).fst = f.fst ≫ g.fst :=
  (rfl)

@[simp]
lemma comp_snd' {X : LocallyDiscrete Cᵒᵖ} {x y z : (twoFibreProduct α β).obj X} (f : x ⟶ y)
    (g : y ⟶ z) : (f ≫ g).snd = f.snd ≫ g.snd :=
  (rfl)

@[simp]
lemma id_fst' {X : LocallyDiscrete Cᵒᵖ} (x : (twoFibreProduct α β).obj X) :
    Hom.fst (𝟙 x) = 𝟙 x.fst :=
  (rfl)

@[simp]
lemma id_snd' {X : LocallyDiscrete Cᵒᵖ} (x : (twoFibreProduct α β).obj X) :
    Hom.snd (𝟙 x) = 𝟙 x.snd :=
  (rfl)

@[simp]
lemma map_obj_fst' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).map f).toFunctor.obj x).fst = (F.map f).toFunctor.obj x.fst :=
  (rfl)

@[simp]
lemma map_obj_snd' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).map f).toFunctor.obj x).snd = (G.map f).toFunctor.obj x.snd :=
  (rfl)

/-- The structure isomorphism of a pullback in the 2-fibre product. -/
lemma map_obj_iso' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).map f).toFunctor.obj x).iso = mapIso α β f.as x :=
  (rfl)

@[simp]
lemma map_map_fst' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (twoFibreProduct α β).obj X}
    (φ : x ⟶ y) :
    (((twoFibreProduct α β).map f).toFunctor.map φ).fst = (F.map f).toFunctor.map φ.fst :=
  (rfl)

@[simp]
lemma map_map_snd' {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (twoFibreProduct α β).obj X}
    (φ : x ⟶ y) :
    (((twoFibreProduct α β).map f).toFunctor.map φ).snd = (G.map f).toFunctor.map φ.snd :=
  (rfl)

-- In the following lemmas, after `subst`, the comparison `(twoFibreProduct α β).mapComp f g` is
-- by construction the isomorphism with components `F.mapComp' f g (f ≫ g) rfl` and
-- `G.mapComp' f g (f ≫ g) rfl`, and similarly for the unit comparisons.

@[simp]
lemma mapId'_hom_app_fst {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapId' f hf).hom.toNatTrans.app x).fst =
      (F.mapId' f hf).hom.toNatTrans.app x.fst := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapId'_inv_app_fst {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapId' f hf).inv.toNatTrans.app x).fst =
      (F.mapId' f hf).inv.toNatTrans.app x.fst := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapId'_hom_app_snd {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapId' f hf).hom.toNatTrans.app x).snd =
      (G.mapId' f hf).hom.toNatTrans.app x.snd := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapId'_inv_app_snd {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapId' f hf).inv.toNatTrans.app x).snd =
      (G.mapId' f hf).inv.toNatTrans.app x.snd := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapComp'_hom_app_fst {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).hom.toNatTrans.app x.fst := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapComp'_inv_app_fst {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).inv.toNatTrans.app x.fst := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapComp'_hom_app_snd {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).hom.toNatTrans.app x.snd := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β)]
  rfl

@[simp]
lemma mapComp'_inv_app_snd {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (twoFibreProduct α β).obj X) :
    (((twoFibreProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).inv.toNatTrans.app x.snd := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β)]
  rfl

/-! ### The projections and the `2`-cell -/

/-- The first projection `twoFibreProduct α β ⟶ F`, with components the first projections of the
categorical pullbacks. -/
def fst : twoFibreProduct α β ⟶ F where
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
      (((twoFibreProduct α β).mapId X).hom.toNatTrans.app x).fst ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β), mapId'_hom_app_fst,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 (F.obj X)).toFunctor.obj x.fst`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `naturality_id`.
    change 𝟙 _ ≫ (F.mapComp f g).hom.toNatTrans.app x.fst =
      (((twoFibreProduct α β).mapComp f g).hom.toNatTrans.app x).fst ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (F.map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β), mapComp'_hom_app_fst,
      Pseudofunctor.mapComp'_eq_mapComp]
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    -- The remaining identities live over objects that are only definitionally `F`-pullbacks.
    erw [Category.comp_id, Category.comp_id]

/-- The second projection `twoFibreProduct α β ⟶ G`, with components the second projections of
the categorical pullbacks. -/
def snd : twoFibreProduct α β ⟶ G where
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
      (((twoFibreProduct α β).mapId X).hom.toNatTrans.app x).snd ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (twoFibreProduct α β), mapId'_hom_app_snd,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 (G.obj X)).toFunctor.obj x.snd`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `fst`.
    change 𝟙 _ ≫ (G.mapComp f g).hom.toNatTrans.app x.snd =
      (((twoFibreProduct α β).mapComp f g).hom.toNatTrans.app x).snd ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (G.map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (twoFibreProduct α β), mapComp'_hom_app_snd,
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

/-- The `2`-cell `fst ≫ α ≅ snd ≫ β` of the 2-fibre product, with components the structure
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
lemma iso_hom_as_app_toNatTrans_app (X : LocallyDiscrete Cᵒᵖ) (x : (twoFibreProduct α β).obj X) :
    ((iso α β).hom.as.app X).toNatTrans.app x = x.iso.hom :=
  (rfl)

@[simp]
lemma iso_inv_as_app_toNatTrans_app (X : LocallyDiscrete Cᵒᵖ) (x : (twoFibreProduct α β).obj X) :
    ((iso α β).inv.as.app X).toNatTrans.app x = x.iso.inv :=
  (rfl)

/-- The pullback along `u` of the structure isomorphism of an object of the 2-fibre product,
expressed through the structure isomorphism of its pullback. -/
lemma map_iso_hom {X Y : LocallyDiscrete Cᵒᵖ} (u : X ⟶ Y) (x : (twoFibreProduct α β).obj X) :
    (H.map u).toFunctor.map x.iso.hom = (α.naturality u).inv.toNatTrans.app x.fst ≫
      (((twoFibreProduct α β).map u).toFunctor.obj x).iso.hom ≫
        (β.naturality u).hom.toNatTrans.app x.snd := by
  -- The structure isomorphism of the pullback is `mapIso`, whose source and target are only
  -- definitionally those of `((twoFibreProduct α β).map u).toFunctor.obj x`.
  change _ = _ ≫ ((α.naturality u).hom.toNatTrans.app x.fst ≫
    (H.map u).toFunctor.map x.iso.hom ≫ (β.naturality u).inv.toNatTrans.app x.snd) ≫ _
  simp

end twoFibreProduct

end TauCeti.Stack

/-! ### Descent data of the 2-fibre product -/

namespace TauCeti.Stack.twoFibreProduct

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

@[simp]
lemma pullHom_fst ⦃X₁ X₂ : C⦄ ⦃M₁ : (twoFibreProduct α β).obj (.mk (op X₁))⦄
    ⦃M₂ : (twoFibreProduct α β).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((twoFibreProduct α β).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((twoFibreProduct α β).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).fst = pullHom (F := F) φ.fst g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_fst', map_map_fst', mapComp'_hom_app_fst, mapComp'_inv_app_fst]
  -- The two sides differ only in the implicit objects of the compositions.
  rfl

@[simp]
lemma pullHom_snd ⦃X₁ X₂ : C⦄ ⦃M₁ : (twoFibreProduct α β).obj (.mk (op X₁))⦄
    ⦃M₂ : (twoFibreProduct α β).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((twoFibreProduct α β).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((twoFibreProduct α β).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).snd = pullHom (F := G) φ.snd g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_snd', map_map_snd', mapComp'_hom_app_snd, mapComp'_inv_app_snd]
  -- The two sides differ only in the implicit objects of the compositions.
  rfl

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The first projection of descent data of the 2-fibre product. -/
@[simps]
def descentDataFst : (twoFibreProduct α β).DescentData f ⥤ F.DescentData f where
  obj D :=
    { obj i := (D.obj i).fst
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).fst
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← pullHom_fst, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := congrArg Hom.fst (D.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg Hom.fst (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D D'} φ :=
    { hom i := (φ.hom i).fst
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrArg Hom.fst (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- The second projection of descent data of the 2-fibre product. -/
@[simps]
def descentDataSnd : (twoFibreProduct α β).DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (D.obj i).snd
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).snd
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← pullHom_snd, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := congrArg Hom.snd (D.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg Hom.snd (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D D'} φ :=
    { hom i := (φ.hom i).snd
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrArg Hom.snd (φ.comm q f₁ f₂ hf₁ hf₂) }

@[simp]
lemma toDescentData_obj_hom_fst (M : (twoFibreProduct α β).obj (.mk (op S))) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((((twoFibreProduct α β).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).fst =
      ((F.toDescentData f).obj M.fst).hom q f₁ f₂ hf₁ hf₂ := by
  -- Unfold `toDescentData` on the 2-fibre product, whose comparisons are only definitionally
  -- those of `Pseudofunctor.DescentData.ofObj`.
  change (((twoFibreProduct α β).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    _).inv.toNatTrans.app M ≫ ((twoFibreProduct α β).mapComp' (f i₂).op.toLoc f₂.op.toLoc
      q.op.toLoc _).hom.toNatTrans.app M).fst = _
  rw [comp_fst', mapComp'_inv_app_fst, mapComp'_hom_app_fst]
  rfl

@[simp]
lemma toDescentData_obj_hom_snd (M : (twoFibreProduct α β).obj (.mk (op S))) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((((twoFibreProduct α β).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).snd =
      ((G.toDescentData f).obj M.snd).hom q f₁ f₂ hf₁ hf₂ := by
  -- As for `toDescentData_obj_hom_fst`.
  change (((twoFibreProduct α β).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    _).inv.toNatTrans.app M ≫ ((twoFibreProduct α β).mapComp' (f i₂).op.toLoc f₂.op.toLoc
      q.op.toLoc _).hom.toNatTrans.app M).snd = _
  rw [comp_snd', mapComp'_inv_app_snd, mapComp'_hom_app_snd]
  rfl

/-- The first component of a morphism of descent data between objects of the 2-fibre product. -/
@[simps]
def homFst {M N : (twoFibreProduct α β).obj (.mk (op S))}
    (Φ : ((twoFibreProduct α β).toDescentData f).obj M ⟶
      ((twoFibreProduct α β).toDescentData f).obj N) :
    (F.toDescentData f).obj M.fst ⟶ (F.toDescentData f).obj N.fst where
  hom i := (Φ.hom i).fst
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have := congrArg Hom.fst (Φ.comm q f₁ f₂ hf₁ hf₂)
    rwa [comp_fst', comp_fst', toDescentData_obj_hom_fst, toDescentData_obj_hom_fst] at this

/-- The second component of a morphism of descent data between objects of the 2-fibre product. -/
@[simps]
def homSnd {M N : (twoFibreProduct α β).obj (.mk (op S))}
    (Φ : ((twoFibreProduct α β).toDescentData f).obj M ⟶
      ((twoFibreProduct α β).toDescentData f).obj N) :
    (G.toDescentData f).obj M.snd ⟶ (G.toDescentData f).obj N.snd where
  hom i := (Φ.hom i).snd
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have := congrArg Hom.snd (Φ.comm q f₁ f₂ hf₁ hf₂)
    rwa [comp_snd', comp_snd', toDescentData_obj_hom_snd, toDescentData_obj_hom_snd] at this

end TauCeti.Stack.twoFibreProduct

end

/-! ### Descent of morphisms and effectivity -/

public section

namespace TauCeti.Stack.twoFibreProduct

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

/-- A morphism of pullbacks in the 2-fibre product whose components are the pullbacks of `a` and
`b` exhibits `(a, b)` as compatible with the structure isomorphisms after pulling back along `u`. -/
private lemma map_map_comp_iso_hom {X Y : Cᵒᵖ} (u : X ⟶ Y) {x y : Fibre α β X} (a : x.fst ⟶ y.fst)
    (b : x.snd ⟶ y.snd) (φ : (map α β u).obj x ⟶ (map α β u).obj y)
    (h₁ : (F.map u.toLoc).toFunctor.map a = φ.fst) (h₂ : (G.map u.toLoc).toFunctor.map b = φ.snd) :
    (H.map u.toLoc).toFunctor.map ((α.app (.mk X)).toFunctor.map a ≫ y.iso.hom) =
      (H.map u.toLoc).toFunctor.map (x.iso.hom ≫ (β.app (.mk X)).toFunctor.map b) := by
  have hw := φ.w
  simp only [map_obj_iso, mapIso_hom] at hw
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 α,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 β, h₁, h₂,
    ← cancel_epi ((α.naturality u.toLoc).hom.toNatTrans.app x.fst)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hw ⊢
  rw [← cancel_mono ((β.naturality u.toLoc).inv.toNatTrans.app y.snd)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app]
  -- The identity lives over `(G.map u ≫ β.app Y).toFunctor.obj y.snd`, which is only
  -- definitionally the source of `(β.naturality u).inv.toNatTrans.app y.snd`.
  erw [Category.comp_id]
  exact hw.trans ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _)))

/-- A morphism of descent data out of `toDescentData`, conjugated by the composition comparisons. -/
private lemma comm_aux₁ {S X₁ X₂ Y : C} {M : F.obj (.mk (op S))} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {q : Y ⟶ S} (hq₁ : f₁ ≫ p₁ = q) (hq₂ : f₂ ≫ p₂ = q)
    {N₁ : F.obj (.mk (op X₁))} {N₂ : F.obj (.mk (op X₂))}
    (φ₁ : (F.map p₁.op.toLoc).toFunctor.obj M ⟶ N₁) (φ₂ : (F.map p₂.op.toLoc).toFunctor.obj M ⟶ N₂)
    (δ : (F.map f₁.op.toLoc).toFunctor.obj N₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (h : (F.map f₁.op.toLoc).toFunctor.map φ₁ ≫ δ =
      ((F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app M ≫
        (F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app M) ≫
        (F.map f₂.op.toLoc).toFunctor.map φ₂) :
    (F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
        (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app M ≫
        (F.map f₁.op.toLoc).toFunctor.map φ₁ ≫ δ =
      (F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app M ≫
        (F.map f₂.op.toLoc).toFunctor.map φ₂ := by
  rw [h]
  simp

/-- A morphism of descent data into `toDescentData`, conjugated by the composition comparisons. -/
private lemma comm_aux₂ {S X₁ X₂ Y : C} {M : G.obj (.mk (op S))} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {q : Y ⟶ S} (hq₁ : f₁ ≫ p₁ = q) (hq₂ : f₂ ≫ p₂ = q)
    {N₁ : G.obj (.mk (op X₁))} {N₂ : G.obj (.mk (op X₂))}
    (φ₁ : N₁ ⟶ (G.map p₁.op.toLoc).toFunctor.obj M) (φ₂ : N₂ ⟶ (G.map p₂.op.toLoc).toFunctor.obj M)
    (δ : (G.map f₁.op.toLoc).toFunctor.obj N₁ ⟶ (G.map f₂.op.toLoc).toFunctor.obj N₂)
    (h : (G.map f₁.op.toLoc).toFunctor.map φ₁ ≫
        ((G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app M ≫
          (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app M) =
      δ ≫ (G.map f₂.op.toLoc).toFunctor.map φ₂) :
    (G.map f₁.op.toLoc).toFunctor.map φ₁ ≫
        (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app M =
      δ ≫ (G.map f₂.op.toLoc).toFunctor.map φ₂ ≫
        (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app M := by
  rw [← reassoc_of% h]
  simp

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- If the descent functors of `F` and `G` along a family of morphisms are fully faithful and that
of `H` is faithful, the descent functor of the 2-fibre product along this family is fully
faithful. -/
noncomputable def fullyFaithfulToDescentData (hF : (F.toDescentData f).FullyFaithful)
    (hG : (G.toDescentData f).FullyFaithful) [(H.toDescentData f).Faithful] :
    ((twoFibreProduct α β).toDescentData f).FullyFaithful where
  preimage {M N} Φ :=
    { fst := hF.preimage (homFst α β f Φ)
      snd := hG.preimage (homSnd α β f Φ)
      w := (H.toDescentData f).map_injective (by
        ext i
        have h₁ := congrArg (fun φ ↦ φ.hom i) (hF.map_preimage (homFst α β f Φ))
        have h₂ := congrArg (fun φ ↦ φ.hom i) (hG.map_preimage (homSnd α β f Φ))
        simp only [toDescentData_map_hom, homFst_hom, homSnd_hom] at h₁ h₂
        exact map_map_comp_iso_hom α β (f i).op _ _ (Φ.hom i) h₁ h₂) }
  map_preimage {M N} Φ := by
    ext i
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact congrArg (fun φ ↦ φ.hom i) (hF.map_preimage (homFst α β f Φ))
    · exact congrArg (fun φ ↦ φ.hom i) (hG.map_preimage (homSnd α β f Φ))
  preimage_map {M N} φ := by
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact hF.preimage_map φ.fst
    · exact hG.preimage_map φ.snd

section glue

/-! The construction of the structure isomorphism of a glued object. Given objects `M₁` of `F` and
`M₂` of `G` over `S`, local identifications of their pullbacks with the components of objects `d`
of the 2-fibre product give local morphisms `p^* (α M₁) ⟶ p^* (β M₂)`; when these come from the
pieces of a descent datum, they form a morphism of descent data for `H`. -/

variable (M₁ : F.obj (.mk (op S))) (M₂ : G.obj (.mk (op S)))

/-- The local comparison `p^* (α M₁) ⟶ p^* (β M₂)` through an object `d` of the 2-fibre product
over `X` and morphisms `p^* M₁ ⟶ d.fst` and `d.snd ⟶ p^* M₂`. -/
private def glueHom {X : C} (p : X ⟶ S) (d : Fibre α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) :
    (H.map p.op.toLoc).toFunctor.obj ((α.app (.mk (op S))).toFunctor.obj M₁) ⟶
      (H.map p.op.toLoc).toFunctor.obj ((β.app (.mk (op S))).toFunctor.obj M₂) :=
  (α.naturality p.op.toLoc).inv.toNatTrans.app M₁ ≫ (α.app (.mk (op X))).toFunctor.map e₁ ≫
    d.iso.hom ≫ (β.app (.mk (op X))).toFunctor.map e₂ ≫
      (β.naturality p.op.toLoc).hom.toNatTrans.app M₂

private lemma isIso_glueHom {X : C} (p : X ⟶ S) (d : Fibre α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) (h₁ : IsIso e₁) (h₂ : IsIso e₂) :
    IsIso (glueHom α β M₁ M₂ p d e₁ e₂) := by
  dsimp only [glueHom]
  infer_instance

/-- The pullback of `glueHom` along `f₁ : Y ⟶ X`, conjugated by the composition comparisons of
`H`. -/
private lemma pullHom_glueHom {X Y : C} (p : X ⟶ S) (d : Fibre α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) (f₁ : Y ⟶ X) (q : Y ⟶ S)
    (hq : f₁ ≫ p = q) :
    (H.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc (congrArg (·.op.toLoc) hq)).hom.toNatTrans.app _ ≫
        (H.map f₁.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p d e₁ e₂) ≫
          (H.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq)).inv.toNatTrans.app _ =
      (α.naturality q.op.toLoc).inv.toNatTrans.app M₁ ≫
        (α.app (.mk (op Y))).toFunctor.map
          ((F.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq)).hom.toNatTrans.app M₁ ≫
            (F.map f₁.op.toLoc).toFunctor.map e₁) ≫
        (mapIso α β f₁.op d).hom ≫
          (β.app (.mk (op Y))).toFunctor.map ((G.map f₁.op.toLoc).toFunctor.map e₂ ≫
            (G.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
                (congrArg (·.op.toLoc) hq)).inv.toNatTrans.app
              M₂) ≫
          (β.naturality q.op.toLoc).hom.toNatTrans.app M₂ := by
  simp only [glueHom, mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 α,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 β,
    Pseudofunctor.StrongTrans.naturality_comp'_inv_app α p.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq),
    Pseudofunctor.StrongTrans.naturality_comp'_hom_app β p.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq)]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  -- The identity lives over `(G.map p ≫ G.map f₁).toFunctor.obj M₂`, which is only
  -- definitionally the target of `G.mapComp'`.
  erw [Category.comp_id]

variable {M₁ M₂}

/-- Local comparisons built from the pieces of a descent datum agree on overlaps, conjugated by the
composition comparisons of `H`: they form a morphism of descent data for `H`. -/
private lemma glueHom_comm {X₁ X₂ Y : C} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S} {d₁ : Fibre α β (op X₁)}
    {d₂ : Fibre α β (op X₂)} {e₁₁ : (F.map p₁.op.toLoc).toFunctor.obj M₁ ⟶ d₁.fst}
    {e₁₂ : (F.map p₂.op.toLoc).toFunctor.obj M₁ ⟶ d₂.fst}
    {e₂₁ : d₁.snd ⟶ (G.map p₁.op.toLoc).toFunctor.obj M₂}
    {e₂₂ : d₂.snd ⟶ (G.map p₂.op.toLoc).toFunctor.obj M₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {q : Y ⟶ S} (hq₁ : f₁ ≫ p₁ = q) (hq₂ : f₂ ≫ p₂ = q)
    (δ₁ : (F.map f₁.op.toLoc).toFunctor.obj d₁.fst ⟶ (F.map f₂.op.toLoc).toFunctor.obj d₂.fst)
    (δ₂ : (G.map f₁.op.toLoc).toFunctor.obj d₁.snd ⟶ (G.map f₂.op.toLoc).toFunctor.obj d₂.snd)
    (hw : (α.app (.mk (op Y))).toFunctor.map δ₁ ≫ (mapIso α β f₂.op d₂).hom =
      (mapIso α β f₁.op d₁).hom ≫ (β.app (.mk (op Y))).toFunctor.map δ₂)
    (h₁ : (F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
        (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app
        M₁ ≫ (F.map f₁.op.toLoc).toFunctor.map e₁₁ ≫ δ₁ =
      (F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app M₁ ≫
        (F.map f₂.op.toLoc).toFunctor.map e₁₂)
    (h₂ : (G.map f₁.op.toLoc).toFunctor.map e₂₁ ≫
        (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app M₂ =
      δ₂ ≫ (G.map f₂.op.toLoc).toFunctor.map e₂₂ ≫
        (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app
          M₂) :
    (H.map f₁.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p₁ d₁ e₁₁ e₂₁) ≫
        (H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app _ ≫
        (H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app _ =
      ((H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app _ ≫
        (H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app _) ≫
        (H.map f₂.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p₂ d₂ e₁₂ e₂₂) := by
  -- The two pullbacks to `Y`, computed by `pullHom_glueHom`, agree by `hw`, `h₁` and `h₂`.
  have hI : (α.app (.mk (op Y))).toFunctor.map
        ((F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app
          M₁ ≫ (F.map f₁.op.toLoc).toFunctor.map e₁₁) ≫ (mapIso α β f₁.op d₁).hom ≫
        (β.app (.mk (op Y))).toFunctor.map ((G.map f₁.op.toLoc).toFunctor.map e₂₁ ≫
          (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app
            M₂) =
      (α.app (.mk (op Y))).toFunctor.map
        ((F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app
          M₁ ≫ (F.map f₂.op.toLoc).toFunctor.map e₁₂) ≫ (mapIso α β f₂.op d₂).hom ≫
        (β.app (.mk (op Y))).toFunctor.map ((G.map f₂.op.toLoc).toFunctor.map e₂₂ ≫
          (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app
            M₂) := by
    rw [h₂, ← h₁]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% hw]
  rw [← cancel_epi ((H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app _),
    ← cancel_mono ((H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app _)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [pullHom_glueHom α β M₁ M₂ p₁ d₁ e₁₁ e₂₁ f₁ q hq₁,
    pullHom_glueHom α β M₁ M₂ p₂ d₂ e₁₂ e₂₂ f₂ q hq₂, reassoc_of% hI]

/-- An isomorphism `m : α M₁ ≅ β M₂` whose pullback along `p` is the local comparison through `d`
makes the identifications of the components of `d` with the pullbacks of `M₁` and `M₂`
compatible with the structure isomorphisms. -/
private lemma glueHom_w {X : C} {p : X ⟶ S} {d : Fibre α β (op X)}
    {e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst}
    {e₂ : (G.map p.op.toLoc).toFunctor.obj M₂ ⟶ d.snd}
    {e₂' : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂} (he₂ : e₂' ≫ e₂ = 𝟙 _)
    (m : (α.app (.mk (op S))).toFunctor.obj M₁ ≅ (β.app (.mk (op S))).toFunctor.obj M₂)
    (hm : (H.map p.op.toLoc).toFunctor.map m.hom = glueHom α β M₁ M₂ p d e₁ e₂') :
    (α.app (.mk (op X))).toFunctor.map e₁ ≫ d.iso.hom =
      (mapIso α β p.op (⟨M₁, M₂, m⟩ : Fibre α β (op S))).hom ≫
        (β.app (.mk (op X))).toFunctor.map e₂ := by
  simp only [mapIso_hom, hm, glueHom, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    ← CategoryTheory.Functor.map_comp, he₂, CategoryTheory.Functor.map_id, Category.comp_id]

end glue

variable {α β} in
/-- If the descent functors of `F` and `G` along a family of morphisms are essentially surjective
and that of `H` is fully faithful, the descent functor of the 2-fibre product along this family is
essentially surjective: a descent datum glues to the triple of the gluings of its components and
the isomorphism glued, in `H`, from the structure isomorphisms of its pieces. -/
lemma essSurj_toDescentData [(F.toDescentData f).EssSurj] [(G.toDescentData f).EssSurj]
    (hH : (H.toDescentData f).FullyFaithful) :
    ((twoFibreProduct α β).toDescentData f).EssSurj where
  mem_essImage D := by
    -- Glue the two components of `D`.
    let e₁ := (F.toDescentData f).objObjPreimageIso ((descentDataFst α β f).obj D)
    let e₂ := (G.toDescentData f).objObjPreimageIso ((descentDataSnd α β f).obj D)
    have he₁ (i : ι) : IsIso (e₁.hom.hom i) :=
      ⟨e₁.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₁.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₁.inv_hom_id⟩
    have he₂ (i : ι) : IsIso (e₂.inv.hom i) :=
      ⟨e₂.hom.hom i, congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id,
        congrArg (fun φ ↦ φ.hom i) e₂.hom_inv_id⟩
    -- The local comparisons form an isomorphism of descent data for `H`.
    let Ψ : (H.toDescentData f).obj ((α.app _).toFunctor.obj
        ((F.toDescentData f).objPreimage ((descentDataFst α β f).obj D))) ≅
        (H.toDescentData f).obj ((β.app _).toFunctor.obj
          ((G.toDescentData f).objPreimage ((descentDataSnd α β f).obj D))) :=
      DescentData.isoMk (fun i ↦ @asIso _ _ _ _ (glueHom α β _ _ (f i) (D.obj i) (e₁.hom.hom i)
        (e₂.inv.hom i)) (isIso_glueHom α β _ _ _ _ _ _ (he₁ i) (he₂ i)))
        (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
          refine glueHom_comm α β hf₁ hf₂ (D.hom q f₁ f₂ hf₁ hf₂).fst (D.hom q f₁ f₂ hf₁ hf₂).snd
            (D.hom q f₁ f₂ hf₁ hf₂).w ?_ ?_
          · exact comm_aux₁ hf₁ hf₂ _ _ _ (e₁.hom.comm q f₁ f₂ hf₁ hf₂)
          · exact comm_aux₂ hf₁ hf₂ _ _ _ (e₂.inv.comm q f₁ f₂ hf₁ hf₂))
    -- It descends to the structure isomorphism of the glued object.
    let m := hH.preimageIso Ψ
    let M : (twoFibreProduct α β).obj (.mk (op S)) := ⟨_, _, m⟩
    have hm (i : ι) := congrArg (fun φ ↦ φ.hom i) (hH.map_preimage Ψ.hom)
    refine ⟨M, ⟨DescentData.isoMk (fun i ↦ mkIso
      ⟨e₁.hom.hom i, e₁.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₁.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₁.inv_hom_id⟩
      ⟨e₂.hom.hom i, e₂.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₂.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id⟩
      (glueHom_w α β (congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id) m (hm i))) ?_⟩⟩
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact (e₁.hom.comm q f₁ f₂ hf₁ hf₂).trans
        (congrArg (· ≫ _) (toDescentData_obj_hom_fst α β f M q f₁ f₂ hf₁ hf₂).symm)
    · exact (e₂.hom.comm q f₁ f₂ hf₁ hf₂).trans
        (congrArg (· ≫ _) (toDescentData_obj_hom_snd α β f M q f₁ f₂ hf₁ hf₂).symm)

variable {J : GrothendieckTopology C}

/-- The 2-fibre product of two prestacks over a prestack is a prestack. -/
instance isPrestack [F.IsPrestack J] [G.IsPrestack J] [H.IsPrestack J] :
    (twoFibreProduct α β).IsPrestack J :=
  IsPrestack.of_isPrestackFor fun _ R hR ↦
    have := (H.isPrestackFor' R hR).fullyFaithful.faithful
    ⟨⟨fullyFaithfulToDescentData α β (F.isPrestackFor' R hR).fullyFaithful
      (G.isPrestackFor' R hR).fullyFaithful⟩⟩

/-- The 2-fibre product of two stacks over a prestack is a stack (Stacks, Lemma 8.4.6 (026G)). -/
@[stacks 026G]
instance isStack [F.IsStack J] [G.IsStack J] [H.IsPrestack J] :
    (twoFibreProduct α β).IsStack J where
  essSurj_of_sieve R hR :=
    have := IsStack.essSurj_of_sieve F R hR
    have := IsStack.essSurj_of_sieve G R hR
    essSurj_toDescentData (H.isPrestackFor' R hR).fullyFaithful

end TauCeti.Stack.twoFibreProduct
