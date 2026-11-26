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
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Equivalence
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Groupoid
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Pasting

/-!
# The 2-fiber product of pseudofunctors

Let `C` be a category and `α : F ⟶ H`, `β : G ⟶ H` strong transformations between
pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. Their 2-fiber product
`TauCeti.Stack.twoFiberProduct α β` is the pseudofunctor whose fiber over `X` is Mathlib's
categorical pullback `CategoricalPullback (α.app X) (β.app X)`: an object is a triple `(x, y, e)` of
`x` over `X` for `F`, `y` over `X` for `G` and an isomorphism `e : α x ≅ β y`, and the pullback
along `f` is `(f^* x, f^* y, f^* e)`, with `f^* e` transported along the naturality isomorphisms of
`α` and `β` (Stacks, Section 4.31 (003O)). It comes with the projections `twoFiberProduct.fst` and
`twoFiberProduct.snd` and the invertible modification `twoFiberProduct.iso : fst ≫ α ≅ snd ≫ β`,
and it has the 2-universal property of the 2-fiber product: strong transformations into it are
induced by pairs of strong transformations into `F` and `G` with an invertible modification
between their composites to `H` (`twoFiberProduct.lift`), and modifications between them are
determined by their projections (`twoFiberProduct.homMk`, `twoFiberProduct.hom_ext`). Its fibers
are groupoids when those of `F` and `G` are (`twoFiberProduct.isGroupoid_obj`), its second
projection is a fiberwise equivalence when `α` is (`twoFiberProduct.isEquivalence_snd_app`), and
its first projection is one when `β` is (`twoFiberProduct.isEquivalence_fst_app`). Finally,
2-fiber products paste: for `γ : K ⟶ F` there is a strong transformation
`twoFiberProduct γ (fst α β) ⟶ twoFiberProduct (γ ≫ α) β` whose components are equivalences
(`twoFiberProduct.pullbackRightPullbackFst`).

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
* `TauCeti.Stack.twoFiberProduct.lift`: the strong transformation into the 2-fiber product
  induced by `a : K ⟶ F`, `b : K ⟶ G` and `e : a ≫ α ≅ b ≫ β`, with `liftCompFst`, `liftCompSnd`
  and `whiskerLeft_lift_iso_hom`.
* `TauCeti.Stack.twoFiberProduct.homMk`, `TauCeti.Stack.twoFiberProduct.isoMk`,
  `TauCeti.Stack.twoFiberProduct.hom_ext`: modifications into the 2-fiber product.
* `TauCeti.Stack.twoFiberProduct.mapObjIsoMk`: an isomorphism between the pullbacks of two objects
  with the same second component, given on the first components, with
  `TauCeti.Stack.twoFiberProduct.mapIso_hom_comp_mapIso_inv` for the comparison of their structure
  isomorphisms.
* `TauCeti.Stack.twoFiberProduct.isGroupoid_obj`: the fibers are groupoids when those of `F` and
  `G` are.
* `TauCeti.Stack.twoFiberProduct.isEquivalence_snd_app`,
  `TauCeti.Stack.twoFiberProduct.isEquivalence_fst_app`: equivalences are stable under 2-base
  change.
* `TauCeti.Stack.twoFiberProduct.pullbackRightPullbackFst`,
  `TauCeti.Stack.twoFiberProduct.isEquivalence_pullbackRightPullbackFst_app`: the pasting law
  `twoFiberProduct γ (fst α β) ⟶ twoFiberProduct (γ ≫ α) β`, whose components are equivalences.

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

/-- For two objects `(x, s, e)` and `(x', s, e')` of the fiber with the same second component, the
composite of the structure isomorphism of the pullback of the first with the inverse of that of the
second is the pullback of `e ≫ e'⁻¹` along `f`, conjugated by the naturality isomorphisms of
`α`. -/
lemma mapIso_hom_comp_mapIso_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) {x x' : F.obj (.mk X)}
    {s : G.obj (.mk X)} (e : (α.app (.mk X)).toFunctor.obj x ≅ (β.app (.mk X)).toFunctor.obj s)
    (e' : (α.app (.mk X)).toFunctor.obj x' ≅ (β.app (.mk X)).toFunctor.obj s) :
    (mapIso α β f ⟨x, s, e⟩).hom ≫ (mapIso α β f ⟨x', s, e'⟩).inv =
      (α.naturality f.toLoc).hom.toNatTrans.app x ≫
        (H.map f.toLoc).toFunctor.map (e.hom ≫ e'.inv) ≫
          (α.naturality f.toLoc).inv.toNatTrans.app x' := by
  simp [mapIso]

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

/-- The component over `X` of the first projection is an equivalence when that of `β` is:
equivalences are stable under 2-base change. -/
instance isEquivalence_fst_app (X : LocallyDiscrete Cᵒᵖ) [(β.app X).toFunctor.IsEquivalence] :
    ((fst α β).app X).toFunctor.IsEquivalence :=
  -- The fiber over `X` is a categorical pullback only definitionally, so instance search does
  -- not find `CategoricalPullback.isEquivalence_π₁`.
  CategoricalPullback.isEquivalence_π₁ _ _

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

/-- An isomorphism between the pullbacks along `f` of two objects `(x, s, e)` and `(x', s, e')`
with the same second component, given by an isomorphism `a` of the pullbacks of their first
components whose image under `α` is the pullback of `e ≫ e'⁻¹`, conjugated by the naturality
isomorphisms of `α`. Its second component is the identity. -/
@[no_expose]
def mapObjIsoMk {X Y : Cᵒᵖ} (f : X ⟶ Y) {x x' : F.obj (.mk X)} {s : G.obj (.mk X)}
    (e : (α.app (.mk X)).toFunctor.obj x ≅ (β.app (.mk X)).toFunctor.obj s)
    (e' : (α.app (.mk X)).toFunctor.obj x' ≅ (β.app (.mk X)).toFunctor.obj s)
    (a : (F.map f.toLoc).toFunctor.obj x ≅ (F.map f.toLoc).toFunctor.obj x')
    (ha : (α.app (.mk Y)).toFunctor.map a.hom = (α.naturality f.toLoc).hom.toNatTrans.app x ≫
      (H.map f.toLoc).toFunctor.map (e.hom ≫ e'.inv) ≫
        (α.naturality f.toLoc).inv.toNatTrans.app x') :
    ((twoFiberProduct α β).map f.toLoc).toFunctor.obj ⟨x, s, e⟩ ≅
      ((twoFiberProduct α β).map f.toLoc).toFunctor.obj ⟨x', s, e'⟩ :=
  CategoricalPullback.mkIso a (Iso.refl _) (by
    -- The structure isomorphisms of the two pullbacks are `mapIso`, only definitionally.
    change (α.app (.mk Y)).toFunctor.map a.hom ≫ (mapIso α β f ⟨x', s, e'⟩).hom =
      (mapIso α β f ⟨x, s, e⟩).hom ≫ (β.app (.mk Y)).toFunctor.map (𝟙 _)
    simp [ha])

@[simp]
lemma mapObjIsoMk_hom_fst {X Y : Cᵒᵖ} (f : X ⟶ Y) {x x' : F.obj (.mk X)} {s : G.obj (.mk X)}
    (e : (α.app (.mk X)).toFunctor.obj x ≅ (β.app (.mk X)).toFunctor.obj s)
    (e' : (α.app (.mk X)).toFunctor.obj x' ≅ (β.app (.mk X)).toFunctor.obj s)
    (a : (F.map f.toLoc).toFunctor.obj x ≅ (F.map f.toLoc).toFunctor.obj x')
    (ha : (α.app (.mk Y)).toFunctor.map a.hom = (α.naturality f.toLoc).hom.toNatTrans.app x ≫
      (H.map f.toLoc).toFunctor.map (e.hom ≫ e'.inv) ≫
        (α.naturality f.toLoc).inv.toNatTrans.app x') :
    (mapObjIsoMk α β f e e' a ha).hom.fst = a.hom :=
  (rfl)

@[simp]
lemma mapObjIsoMk_hom_snd {X Y : Cᵒᵖ} (f : X ⟶ Y) {x x' : F.obj (.mk X)} {s : G.obj (.mk X)}
    (e : (α.app (.mk X)).toFunctor.obj x ≅ (β.app (.mk X)).toFunctor.obj s)
    (e' : (α.app (.mk X)).toFunctor.obj x' ≅ (β.app (.mk X)).toFunctor.obj s)
    (a : (F.map f.toLoc).toFunctor.obj x ≅ (F.map f.toLoc).toFunctor.obj x')
    (ha : (α.app (.mk Y)).toFunctor.map a.hom = (α.naturality f.toLoc).hom.toNatTrans.app x ≫
      (H.map f.toLoc).toFunctor.map (e.hom ≫ e'.inv) ≫
        (α.naturality f.toLoc).inv.toNatTrans.app x') :
    (mapObjIsoMk α β f e e' a ha).hom.snd = 𝟙 ((G.map f.toLoc).toFunctor.obj s) :=
  (rfl)

/-! ### The 2-universal property

A strong transformation `K ⟶ twoFiberProduct α β` is given by two strong transformations
`a : K ⟶ F` and `b : K ⟶ G` with an invertible modification `e : a ≫ α ≅ b ≫ β` (`lift`, with
`liftCompFst`, `liftCompSnd` and `whiskerLeft_lift_iso_hom`). A modification between two strong
transformations into `twoFiberProduct α β` is given by modifications between their composites
with `fst` and `snd`, compatible with `iso` (`homMk`, and `isoMk` for invertible ones), and is
determined by these (`hom_ext`). -/

section lift

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}}
  (a : K ⟶ F) (b : K ⟶ G) (e : a ≫ α ≅ b ≫ β)

/-- The component `α (a k) ≅ β (b k)` of `e` at an object `k` over `X`: the structure
isomorphism of the image of `k` under `lift a b e`. -/
@[simps]
def liftIso (X : LocallyDiscrete Cᵒᵖ) (k : K.obj X) :
    (α.app X).toFunctor.obj ((a.app X).toFunctor.obj k) ≅
      (β.app X).toFunctor.obj ((b.app X).toFunctor.obj k) where
  hom := (e.hom.as.app X).toNatTrans.app k
  inv := (e.inv.as.app X).toNatTrans.app k
  hom_inv_id := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) e.hom_inv_id
  inv_hom_id := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) e.inv_hom_id

/-- The naturality of `e` along `f`, on the components `liftIso`. -/
private lemma liftIso_hom_naturality {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (k : K.obj X) :
    (α.app Y).toFunctor.map ((a.naturality f).hom.toNatTrans.app k) ≫
        (α.naturality f).hom.toNatTrans.app ((a.app X).toFunctor.obj k) ≫
          (H.map f).toFunctor.map (liftIso α β a b e X k).hom =
      (liftIso α β a b e Y ((K.map f).toFunctor.obj k)).hom ≫
        (β.app Y).toFunctor.map ((b.naturality f).hom.toNatTrans.app k) ≫
          (β.naturality f).hom.toNatTrans.app ((b.app X).toFunctor.obj k) := by
  have h := congrArg (fun m ↦ m.toNatTrans.app k) (e.hom.as.naturality f)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  exact (h.trans (Category.assoc _ _ _)).symm

/-- The component over `X` of `lift a b e`: an object `k` goes to `(a k, b k, e k)`. -/
@[simps]
def liftApp (X : LocallyDiscrete Cᵒᵖ) : K.obj X ⥤ Fiber α β X.as where
  obj k := ⟨(a.app X).toFunctor.obj k, (b.app X).toFunctor.obj k, liftIso α β a b e X k⟩
  map φ :=
    { fst := (a.app X).toFunctor.map φ
      snd := (b.app X).toFunctor.map φ
      w := (e.hom.as.app X).toNatTrans.naturality φ }

/-- The naturality isomorphism of `lift a b e` at `f`, with components those of `a` and `b`. -/
@[simps!]
def liftNaturality {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) :
    (K.map f).toFunctor ⋙ liftApp α β a b e Y ≅ liftApp α β a b e X ⋙ map α β f.as :=
  NatIso.ofComponents
    (fun k ↦ CategoricalPullback.mkIso ((Cat.Hom.toNatIso (a.naturality f)).app k)
      ((Cat.Hom.toNatIso (b.naturality f)).app k) (by
        -- The structure isomorphism of the pullback is `mapIso`, only definitionally.
        change (α.app Y).toFunctor.map ((a.naturality f).hom.toNatTrans.app k) ≫
            ((α.naturality f).hom.toNatTrans.app ((a.app X).toFunctor.obj k) ≫
              (H.map f).toFunctor.map (liftIso α β a b e X k).hom ≫
                (β.naturality f).inv.toNatTrans.app ((b.app X).toFunctor.obj k)) =
          (liftIso α β a b e Y ((K.map f).toFunctor.obj k)).hom ≫
            (β.app Y).toFunctor.map ((b.naturality f).hom.toNatTrans.app k)
        rw [← cancel_mono ((β.naturality f).hom.toNatTrans.app ((b.app X).toFunctor.obj k))]
        simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
        -- The identity lives over an object that is only definitionally an `H`-pullback.
        erw [Category.comp_id]
        exact liftIso_hom_naturality α β a b e f k))
    (fun φ ↦ by
      ext
      · exact (a.naturality f).hom.toNatTrans.naturality φ
      · exact (b.naturality f).hom.toNatTrans.naturality φ)

/-- The strong transformation `K ⟶ twoFiberProduct α β` induced by strong transformations
`a : K ⟶ F` and `b : K ⟶ G` and an invertible modification `e : a ≫ α ≅ b ≫ β`. -/
def lift : K ⟶ twoFiberProduct α β where
  app X := (liftApp α β a b e X).toCatHom
  naturality f := Cat.Hom.isoMk (liftNaturality α β a b e f)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 _)
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  -- The comparisons of the pullback are by construction those of `F` and `G`, the unitors and
  -- associators of `Cat` have identity components, and all of these agree with the components
  -- of the corresponding cells of `a` and `b` only definitionally.
  naturality_id X := by
    ext k
    apply CategoricalPullback.hom_ext
    · have h : (F.mapId' (𝟙 X) rfl).hom.toNatTrans.app ((a.app X).toFunctor.obj k) =
          (F.mapId X).hom.toNatTrans.app ((a.app X).toFunctor.obj k) := by
        rw [Pseudofunctor.mapId'_eq_mapId]
      exact (congrArg ((a.naturality (𝟙 X)).hom.toNatTrans.app k ≫ ·) h).trans
        (congrArg (fun m ↦ m.toNatTrans.app k) (a.naturality_id X))
    · have h : (G.mapId' (𝟙 X) rfl).hom.toNatTrans.app ((b.app X).toFunctor.obj k) =
          (G.mapId X).hom.toNatTrans.app ((b.app X).toFunctor.obj k) := by
        rw [Pseudofunctor.mapId'_eq_mapId]
      exact (congrArg ((b.naturality (𝟙 X)).hom.toNatTrans.app k ≫ ·) h).trans
        (congrArg (fun m ↦ m.toNatTrans.app k) (b.naturality_id X))
  naturality_comp f g := by
    ext k
    apply CategoricalPullback.hom_ext
    · have h : (F.mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app ((a.app _).toFunctor.obj k) =
          (F.mapComp f g).hom.toNatTrans.app ((a.app _).toFunctor.obj k) := by
        rw [Pseudofunctor.mapComp'_eq_mapComp]
      exact (congrArg ((a.naturality (f ≫ g)).hom.toNatTrans.app k ≫ ·) h).trans
        (congrArg (fun m ↦ m.toNatTrans.app k) (a.naturality_comp f g))
    · have h : (G.mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app ((b.app _).toFunctor.obj k) =
          (G.mapComp f g).hom.toNatTrans.app ((b.app _).toFunctor.obj k) := by
        rw [Pseudofunctor.mapComp'_eq_mapComp]
      exact (congrArg ((b.naturality (f ≫ g)).hom.toNatTrans.app k ≫ ·) h).trans
        (congrArg (fun m ↦ m.toNatTrans.app k) (b.naturality_comp f g))

@[simp]
lemma lift_app_toFunctor (X : LocallyDiscrete Cᵒᵖ) :
    ((lift α β a b e).app X).toFunctor = liftApp α β a b e X :=
  (rfl)

/-- The first projection of `lift a b e` is `a`. -/
def liftCompFst : lift α β a b e ≫ fst α β ≅ a :=
  Pseudofunctor.StrongTrans.isoMk (fun X ↦ Iso.refl (a.app X)) (fun f ↦ by
    ext k
    -- The components `Iso.refl (a.app X)` have source `(lift a b e ≫ fst).app X`, which is
    -- `a.app X` only definitionally (`liftApp ⋙ π₁` reduces to `a.app X`). The whiskered
    -- components in the goal are therefore not type-correct at the transparency used by `rw` and
    -- `simp`: after `Cat.Hom₂.comp_app`, `comp_naturality_hom_app` and `Iso.refl_hom`, the rewrite
    -- `Cat.whiskerLeft_app` finds no instance. So `change` states the goal with the components
    -- evaluated. These are the naturality of `a` at `k` (`liftNaturality_hom_app_fst`) and
    -- identities: the naturality of `fst`, the associators of `Cat` and the `Iso.refl`s.
    change 𝟙 _ ≫ (a.naturality f).hom.toNatTrans.app k =
      (𝟙 _ ≫ (a.naturality f).hom.toNatTrans.app k ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
        (F.map f).toFunctor.map (𝟙 _)
    simp)

/-- The second projection of `lift a b e` is `b`. -/
def liftCompSnd : lift α β a b e ≫ snd α β ≅ b :=
  Pseudofunctor.StrongTrans.isoMk (fun X ↦ Iso.refl (b.app X)) (fun f ↦ by
    ext k
    -- As for `liftCompFst`, with `snd`, `b` and `liftNaturality_hom_app_snd`.
    change 𝟙 _ ≫ (b.naturality f).hom.toNatTrans.app k =
      (𝟙 _ ≫ (b.naturality f).hom.toNatTrans.app k ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
        (G.map f).toFunctor.map (𝟙 _)
    simp)

/-- The `2`-cell `iso` restricted along `lift a b e` is `e`, up to the identifications
`liftCompFst` and `liftCompSnd`. -/
lemma whiskerLeft_lift_iso_hom :
    lift α β a b e ◁ (iso α β).hom =
      (α_ _ _ _).inv ≫ (liftCompFst α β a b e).hom ▷ α ≫ e.hom ≫
        (liftCompSnd α β a b e).inv ▷ β ≫ (α_ _ _ _).hom := by
  ext X k
  -- As in `liftCompFst`, the components of `liftCompFst` and `liftCompSnd` are identities between
  -- `1`-morphisms that agree only definitionally. `simp only` with `whiskerLeft_as_app`,
  -- `homCategory_comp_as_app`, `whiskerRight_as_app`, `associator_hom_as_app`, `Cat.Hom₂.comp_app`
  -- and `iso_hom_as_app_toNatTrans_app` stops at `(isoMk _ _).hom.as.app X ▷ α.app X`, which
  -- `isoMk_hom_as_app` does not rewrite. So `change` states the goal with the components
  -- evaluated. The left side is the structure isomorphism `liftIso` of `lift a b e` at `k`. The
  -- right side is `e` at `k` between the images of identities and the associators of `Cat`.
  change (liftIso α β a b e X k).hom = 𝟙 _ ≫ (α.app X).toFunctor.map (𝟙 _) ≫
    (liftIso α β a b e X k).hom ≫ (β.app X).toFunctor.map (𝟙 _) ≫ 𝟙 _
  simp

end lift

section homMk

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}}
  {φ ψ : K ⟶ twoFiberProduct α β}

/-- The components of a modification `φ ≫ fst ⟶ ψ ≫ fst` are natural with respect to the
naturality isomorphisms of `φ` and `ψ`, on first components. -/
private lemma naturality_fst (m₁ : φ ≫ fst α β ⟶ ψ ≫ fst α β) {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (k : K.obj X) :
    (m₁.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
        ((ψ.naturality f).hom.toNatTrans.app k).fst =
      ((φ.naturality f).hom.toNatTrans.app k).fst ≫
        (F.map f).toFunctor.map ((m₁.as.app X).toNatTrans.app k) := by
  have h := congrArg (fun m ↦ m.toNatTrans.app k) (m₁.as.naturality f)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  -- The naturality isomorphisms of `fst` are identities.
  have h' : (m₁.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
      ((ψ.naturality f).hom.toNatTrans.app k).fst ≫ 𝟙 _ =
        (((φ.naturality f).hom.toNatTrans.app k).fst ≫ 𝟙 _) ≫
          (F.map f).toFunctor.map ((m₁.as.app X).toNatTrans.app k) := h
  simp only [Category.comp_id] at h'
  -- The remaining identity lives over a pullback in the 2-fiber product, only
  -- definitionally a pullback along `F`.
  erw [Category.comp_id] at h'
  exact h'

/-- The components of a modification `φ ≫ snd ⟶ ψ ≫ snd` are natural with respect to the
naturality isomorphisms of `φ` and `ψ`, on second components. -/
private lemma naturality_snd (m₂ : φ ≫ snd α β ⟶ ψ ≫ snd α β) {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (k : K.obj X) :
    (m₂.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
        ((ψ.naturality f).hom.toNatTrans.app k).snd =
      ((φ.naturality f).hom.toNatTrans.app k).snd ≫
        (G.map f).toFunctor.map ((m₂.as.app X).toNatTrans.app k) := by
  have h := congrArg (fun m ↦ m.toNatTrans.app k) (m₂.as.naturality f)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  -- The naturality isomorphisms of `snd` are identities.
  have h' : (m₂.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
      ((ψ.naturality f).hom.toNatTrans.app k).snd ≫ 𝟙 _ =
        (((φ.naturality f).hom.toNatTrans.app k).snd ≫ 𝟙 _) ≫
          (G.map f).toFunctor.map ((m₂.as.app X).toNatTrans.app k) := h
  simp only [Category.comp_id] at h'
  -- As for `naturality_fst`.
  erw [Category.comp_id] at h'
  exact h'

/-- The compatibility of modifications `m₁ : φ ≫ fst ⟶ ψ ≫ fst` and `m₂ : φ ≫ snd ⟶ ψ ≫ snd`
with `iso`, on components. -/
private lemma homMk_w (m₁ : φ ≫ fst α β ⟶ ψ ≫ fst α β) (m₂ : φ ≫ snd α β ⟶ ψ ≫ snd α β)
    (w : m₁ ▷ α ≫ (α_ _ _ _).hom ≫ ψ ◁ (iso α β).hom ≫ (α_ _ _ _).inv =
      (α_ _ _ _).hom ≫ φ ◁ (iso α β).hom ≫ (α_ _ _ _).inv ≫ m₂ ▷ β)
    (X : LocallyDiscrete Cᵒᵖ) (k : K.obj X) :
    (α.app X).toFunctor.map ((m₁.as.app X).toNatTrans.app k) ≫
        ((ψ.app X).toFunctor.obj k).iso.hom =
      ((φ.app X).toFunctor.obj k).iso.hom ≫
        (β.app X).toFunctor.map ((m₂.as.app X).toNatTrans.app k) := by
  have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) w
  simp only [Pseudofunctor.StrongTrans.homCategory_comp_as_app,
    Pseudofunctor.StrongTrans.whiskerLeft_as_app, Pseudofunctor.StrongTrans.whiskerRight_as_app,
    Pseudofunctor.StrongTrans.associator_hom_as_app,
    Pseudofunctor.StrongTrans.associator_inv_as_app] at h
  -- The associators of `Cat` have identity components.
  have h' : (α.app X).toFunctor.map ((m₁.as.app X).toNatTrans.app k) ≫ 𝟙 _ ≫
      ((ψ.app X).toFunctor.obj k).iso.hom ≫ 𝟙 _ =
        𝟙 _ ≫ ((φ.app X).toFunctor.obj k).iso.hom ≫ 𝟙 _ ≫
          (β.app X).toFunctor.map ((m₂.as.app X).toNatTrans.app k) := h
  simp only [Category.id_comp] at h'
  -- The remaining identity lives over `(β.app X).obj (ψ k).snd`, whose fiber is only
  -- definitionally that of the structure isomorphism.
  erw [Category.comp_id] at h'
  exact h'

/-- A modification `φ ⟶ ψ` between strong transformations into the 2-fiber product, from
modifications `m₁ : φ ≫ fst ⟶ ψ ≫ fst` and `m₂ : φ ≫ snd ⟶ ψ ≫ snd` compatible with `iso`. -/
def homMk (m₁ : φ ≫ fst α β ⟶ ψ ≫ fst α β) (m₂ : φ ≫ snd α β ⟶ ψ ≫ snd α β)
    (w : m₁ ▷ α ≫ (α_ _ _ _).hom ≫ ψ ◁ (iso α β).hom ≫ (α_ _ _ _).inv =
      (α_ _ _ _).hom ≫ φ ◁ (iso α β).hom ≫ (α_ _ _ _).inv ≫ m₂ ▷ β) : φ ⟶ ψ where
  as.app X := Cat.Hom₂.ofNatTrans
    { app k :=
        { fst := (m₁.as.app X).toNatTrans.app k
          snd := (m₂.as.app X).toNatTrans.app k
          w := by exact homMk_w α β m₁ m₂ w X k }
      naturality k l u := by
        apply CategoricalPullback.hom_ext
        · exact (m₁.as.app X).toNatTrans.naturality u
        · exact (m₂.as.app X).toNatTrans.naturality u }
  as.naturality f := by
    ext k
    apply CategoricalPullback.hom_ext
    · exact naturality_fst α β m₁ f k
    · exact naturality_snd α β m₂ f k

/-- The first projection of `homMk m₁ m₂ w` is `m₁`. -/
@[simp]
lemma homMk_whiskerRight_fst (m₁ : φ ≫ fst α β ⟶ ψ ≫ fst α β)
    (m₂ : φ ≫ snd α β ⟶ ψ ≫ snd α β)
    (w : m₁ ▷ α ≫ (α_ _ _ _).hom ≫ ψ ◁ (iso α β).hom ≫ (α_ _ _ _).inv =
      (α_ _ _ _).hom ≫ φ ◁ (iso α β).hom ≫ (α_ _ _ _).inv ≫ m₂ ▷ β) :
    homMk α β m₁ m₂ w ▷ fst α β = m₁ := by
  ext X k
  rw [Pseudofunctor.StrongTrans.whiskerRight_as_app]
  rfl

/-- The second projection of `homMk m₁ m₂ w` is `m₂`. -/
@[simp]
lemma homMk_whiskerRight_snd (m₁ : φ ≫ fst α β ⟶ ψ ≫ fst α β)
    (m₂ : φ ≫ snd α β ⟶ ψ ≫ snd α β)
    (w : m₁ ▷ α ≫ (α_ _ _ _).hom ≫ ψ ◁ (iso α β).hom ≫ (α_ _ _ _).inv =
      (α_ _ _ _).hom ≫ φ ◁ (iso α β).hom ≫ (α_ _ _ _).inv ≫ m₂ ▷ β) :
    homMk α β m₁ m₂ w ▷ snd α β = m₂ := by
  ext X k
  rw [Pseudofunctor.StrongTrans.whiskerRight_as_app]
  rfl

/-- Two modifications into the 2-fiber product agree when their composites with `fst` and `snd`
do. -/
lemma hom_ext {m n : φ ⟶ ψ} (h₁ : m ▷ fst α β = n ▷ fst α β) (h₂ : m ▷ snd α β = n ▷ snd α β) :
    m = n := by
  ext X k
  apply CategoricalPullback.hom_ext
  · have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) h₁
    simp only [Pseudofunctor.StrongTrans.whiskerRight_as_app] at h
    exact h
  · have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) h₂
    simp only [Pseudofunctor.StrongTrans.whiskerRight_as_app] at h
    exact h

/-- An isomorphism `φ ≅ ψ` between strong transformations into the 2-fiber product, from
isomorphisms `e₁ : φ ≫ fst ≅ ψ ≫ fst` and `e₂ : φ ≫ snd ≅ ψ ≫ snd` compatible with `iso`. -/
@[simps]
def isoMk (e₁ : φ ≫ fst α β ≅ ψ ≫ fst α β) (e₂ : φ ≫ snd α β ≅ ψ ≫ snd α β)
    (w : e₁.hom ▷ α ≫ (α_ _ _ _).hom ≫ ψ ◁ (iso α β).hom ≫ (α_ _ _ _).inv =
      (α_ _ _ _).hom ≫ φ ◁ (iso α β).hom ≫ (α_ _ _ _).inv ≫ e₂.hom ▷ β) : φ ≅ ψ where
  hom := homMk α β e₁.hom e₂.hom w
  inv := homMk α β e₁.inv e₂.inv (by
    rw [← cancel_epi (e₁.hom ▷ α), ← cancel_mono (e₂.hom ▷ β)]
    simp only [Category.assoc, hom_inv_whiskerRight_assoc, inv_hom_whiskerRight,
      Category.comp_id]
    exact w.symm)
  hom_inv_id := hom_ext α β (by simp) (by simp)
  inv_hom_id := hom_ext α β (by simp) (by simp)

end homMk

/-- The fibers of the 2-fiber product of transformations between pseudofunctors with groupoid
fibers are groupoids. -/
instance isGroupoid_obj (X : LocallyDiscrete Cᵒᵖ) [IsGroupoid (F.obj X)]
    [IsGroupoid (G.obj X)] : IsGroupoid ((twoFiberProduct α β).obj X) :=
  inferInstanceAs (IsGroupoid ((α.app X).toFunctor ⊡ (β.app X).toFunctor))

/-- The second projection of a 2-fiber product along a fiberwise equivalence `α` is a fiberwise
equivalence: equivalences are stable under 2-base change. -/
instance isEquivalence_snd_app (X : LocallyDiscrete Cᵒᵖ) [(α.app X).toFunctor.IsEquivalence] :
    ((snd α β).app X).toFunctor.IsEquivalence :=
  inferInstanceAs (π₂ (α.app X).toFunctor (β.app X).toFunctor).IsEquivalence

/-! ### Pasting

For `γ : K ⟶ F`, the 2-fiber product of `γ` with the first projection `fst α β` is equivalent to
the 2-fiber product of `γ ≫ α` with `β` (`pullbackRightPullbackFst`, whose components are
equivalences): the pasting law for 2-fiber products, computed fiberwise by
`CategoricalPullback.pullbackRightPullbackFstEquiv`. -/

section pasting

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (γ : K ⟶ F)

/-- The `2`-cell `fst ≫ γ ≫ α ≅ (snd ≫ snd) ≫ β` of the outer square obtained by pasting the
`2`-cells of `twoFiberProduct γ (fst α β)` and `twoFiberProduct α β`. -/
def pullbackRightPullbackFstSquareIso :
    fst γ (fst α β) ≫ γ ≫ α ≅ (snd γ (fst α β) ≫ snd α β) ≫ β :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso (iso γ (fst α β)) α ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso (snd γ (fst α β)) (iso α β) ≪≫ (α_ _ _ _).symm

/-- The component of `pullbackRightPullbackFstSquareIso` at an object `k = (t, (x, y, e), e')` is
`α e' ≫ e`. -/
@[simp]
lemma pullbackRightPullbackFstSquareIso_hom_as_app_toNatTrans_app (X : LocallyDiscrete Cᵒᵖ)
    (k : (twoFiberProduct γ (fst α β)).obj X) :
    ((pullbackRightPullbackFstSquareIso α β γ).hom.as.app X).toNatTrans.app k =
      (α.app X).toFunctor.map k.iso.hom ≫ k.snd.iso.hom := by
  -- The associators of `Cat` have identity components and the whiskered `2`-cells are those of
  -- the two 2-fiber products, but `Cat.Hom₂.comp_app` does not apply to the composite: its
  -- intermediate `1`-morphisms agree only definitionally with those of the components. So
  -- `change` states the goal with the components evaluated.
  change 𝟙 _ ≫ (α.app X).toFunctor.map k.iso.hom ≫ 𝟙 _ ≫ k.snd.iso.hom ≫ 𝟙 _ = _
  simp only [Category.id_comp]
  -- The last identity lives over an object of `H.obj X` that is only definitionally the target
  -- of `k.snd.iso.hom`.
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The comparison `twoFiberProduct γ (fst α β) ⟶ twoFiberProduct (γ ≫ α) β` of the pasting law
for 2-fiber products, induced by the pasted `2`-cell `pullbackRightPullbackFstSquareIso`. Its
components are equivalences (`isEquivalence_pullbackRightPullbackFst_app`). -/
def pullbackRightPullbackFst : twoFiberProduct γ (fst α β) ⟶ twoFiberProduct (γ ≫ α) β :=
  lift (γ ≫ α) β _ _ (pullbackRightPullbackFstSquareIso α β γ)

/-- The component of `pullbackRightPullbackFst` over `X` is the functor of the pasting
equivalence of categorical pullbacks. -/
def pullbackRightPullbackFstAppIso (X : LocallyDiscrete Cᵒᵖ) :
    (CategoricalPullback.pullbackRightPullbackFstEquiv (α.app X).toFunctor (β.app X).toFunctor
      (γ.app X).toFunctor).functor ≅ ((pullbackRightPullbackFst α β γ).app X).toFunctor :=
  -- Both functors send `k` to `(k.fst, k.snd.snd, -)`, and both structure isomorphisms are
  -- `α k.iso ≫ k.snd.iso` (`pullbackRightPullbackFstSquareIso_hom_as_app_toNatTrans_app`). The
  -- fibers of the 2-fiber products are categorical pullbacks only definitionally, so neither
  -- `simp` nor `rw` can rewrite with the categorical pullback lemmas (even `Functor.map_id` fails
  -- to fire); the identity cancellations are glued by unification instead.
  NatIso.ofComponents
    (fun k ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
      ((((congrArg (· ≫ _) (Functor.map_id _ _)).trans (Category.id_comp _)).trans
        (pullbackRightPullbackFstSquareIso_hom_as_app_toNatTrans_app α β γ X k)).trans
          ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Functor.map_id _ _).symm))))
    (fun _ ↦ CategoricalPullback.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))

instance isEquivalence_pullbackRightPullbackFst_app (X : LocallyDiscrete Cᵒᵖ) :
    ((pullbackRightPullbackFst α β γ).app X).toFunctor.IsEquivalence :=
  -- The categories of the fibers are categorical pullbacks only definitionally, so instance
  -- search does not find that the functor of the pasting equivalence is an equivalence.
  (Functor.isEquivalence_iff_of_iso (pullbackRightPullbackFstAppIso α β γ X)).1
    (CategoricalPullback.pullbackRightPullbackFstEquiv (α.app X).toFunctor
      (β.app X).toFunctor (γ.app X).toFunctor).isEquivalence_functor

end pasting

end twoFiberProduct

end TauCeti.Stack

end
