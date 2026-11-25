/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Pi.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Products of pseudofunctors

Let `C` be a category and `F i`, for `i : I`, a family of pseudofunctors
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. Their product `TauCeti.Stack.pi F` is the pseudofunctor whose fiber
over `X` is the product category `∀ i, (F i).obj X`, whose pullback functors are the products
`Functor.pi` of those of the `F i`, and whose comparisons are those of the `F i`, componentwise.
It comes with the projections `pi.π F i : pi F ⟶ F i` and has the 2-universal property of the
product: strong transformations into it are induced by families of strong transformations into
the `F i` (`pi.lift`, with `pi.liftCompπ`), and modifications between them are given by families
of modifications between their projections (`pi.homMk`, `pi.isoMk`) and are determined by these
(`pi.hom_ext`).

The product of the empty family is the terminal pseudofunctor `TauCeti.Stack.terminal`, whose
fibers are the category with one object and one morphism: every pseudofunctor has a strong
transformation to it (`terminal.lift`), and any two strong transformations to it are related by a
unique modification (`terminal.homMk`, `terminal.hom_ext`).

The construction uses no topology; that products of stacks are stacks is proved in
`TauCeti.CategoryTheory.Sites.Descent.Pi`.

The fibers of `pi F` for `I : Type w` and `F i` with values in `Cat.{v', u'}` lie in
`Cat.{max w v', max w u'}`; the construction is therefore stated for pseudofunctors with values in
`Cat.{max w v', max w u'}`, so that `pi F` takes values in the same bicategory as the `F i`.

## Main declarations

* `TauCeti.Stack.pi`: the product of a family of pseudofunctors.
* `TauCeti.Stack.pi.instIsGroupoidObj`: the fibers of a product of pseudofunctors with groupoid
  fibers are groupoids.
* `TauCeti.Stack.pi.π`: the projections.
* `TauCeti.Stack.pi.lift`: the strong transformation into the product induced by a family of
  strong transformations `a i : K ⟶ F i`, with `liftCompπ`.
* `TauCeti.Stack.pi.homMk`, `TauCeti.Stack.pi.isoMk`, `TauCeti.Stack.pi.hom_ext`: modifications
  into the product.
* `TauCeti.Stack.terminal`: the terminal pseudofunctor, with `terminal.lift`, `terminal.homMk` and
  `terminal.hom_ext`.
-/

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

universe w u' v' v u

@[expose] public section

namespace TauCeti.Stack

variable {C : Type u} [Category.{v} C] {I : Type w}
  (F : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'})

namespace pi

/-- The fiber of the product over `X`: the product of the fibers of the `F i` over `X`. -/
abbrev Fiber (X : Cᵒᵖ) : Type (max w u') :=
  ∀ i, (F i).obj (.mk X)

/-- The pullback functor of the product along `f : X ⟶ Y` in `Cᵒᵖ`. -/
abbrev map {X Y : Cᵒᵖ} (f : X ⟶ Y) : Fiber F X ⥤ Fiber F Y :=
  Functor.pi fun i ↦ ((F i).map f.toLoc).toFunctor

/-- The unit isomorphism of the product, from the unit comparisons of the `F i`. -/
abbrev mapIdIso (X : Cᵒᵖ) : map F (𝟙 X) ≅ 𝟭 (Fiber F X) :=
  NatIso.pi fun i ↦ Cat.Hom.toNatIso ((F i).mapId' (𝟙 X).toLoc)

/-- The composition isomorphism of the product at a factorization `f ≫ g = fg`, from the
composition comparisons of the `F i`. -/
abbrev mapCompIso {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    map F fg ≅ map F f ⋙ map F g :=
  NatIso.pi fun i ↦
    Cat.Hom.toNatIso ((F i).mapComp' f.toLoc g.toLoc fg.toLoc (congrArg Quiver.Hom.toLoc h))

end pi

open pi in
/-- The product of a family of pseudofunctors `F i : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`: its fiber over
`X` is the product of the fibers of the `F i`, and its pullback functors and comparisons are those
of the `F i`, componentwise. -/
def pi : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun X ↦ Cat.of (Fiber F X)) (map F)
    (mapIdIso F) (mapCompIso F)
    (fun _ _ _ _ _ _ hfg hgh hfgh hfgh' _ ↦ funext fun i ↦
      (F i).mapComp'_hom_app_comp_map_mapComp'_hom_app _ _ _ _ _ _
        (congrArg Quiver.Hom.toLoc hfg) (congrArg Quiver.Hom.toLoc hgh)
        (congrArg Quiver.Hom.toLoc hfgh) (congrArg Quiver.Hom.toLoc hfgh') _)
    (fun _ hf _ ↦ funext fun i ↦
      (F i).mapComp'_hom_app_comp_map_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _)
    (fun _ hf _ ↦ funext fun i ↦
      (F i).mapComp'_hom_app_comp_mapId'_hom_app _ rfl _ (congrArg Quiver.Hom.toLoc hf) _)

namespace pi

/-- The fibers of a product of pseudofunctors with groupoid fibers are groupoids. -/
instance instIsGroupoidObj (X : LocallyDiscrete Cᵒᵖ) [∀ i, IsGroupoid ((F i).obj X)] :
    IsGroupoid ((pi F).obj X) :=
  inferInstanceAs (IsGroupoid (∀ i, (F i).obj X))

/-! ### Components of the product

The fibers `(pi F).obj X` are product categories only after unfolding `pi`, so the following
lemmas are stated on them directly. -/

@[simp]
lemma comp_apply' {X : LocallyDiscrete Cᵒᵖ} {x y z : (pi F).obj X} (f : x ⟶ y) (g : y ⟶ z)
    (i : I) : (f ≫ g) i = f i ≫ g i :=
  (rfl)

@[simp]
lemma id_apply' {X : LocallyDiscrete Cᵒᵖ} (x : (pi F).obj X) (i : I) :
    (𝟙 x : x ⟶ x) i = 𝟙 (x i) :=
  (rfl)

@[simp]
lemma map_obj_apply {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (pi F).obj X) (i : I) :
    ((pi F).map f).toFunctor.obj x i = ((F i).map f).toFunctor.obj (x i) :=
  (rfl)

@[simp]
lemma map_map_apply {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (pi F).obj X} (φ : x ⟶ y)
    (i : I) : ((pi F).map f).toFunctor.map φ i = ((F i).map f).toFunctor.map (φ i) :=
  (rfl)

-- In the following lemmas, after `subst`, the comparison `(pi F).mapComp f g` is by construction
-- the family of the `(F i).mapComp' f g (f ≫ g) rfl`, and similarly for the unit comparisons.

@[simp]
lemma mapId'_hom_app_apply {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (pi F).obj X) (i : I) :
    ((pi F).mapId' f hf).hom.toNatTrans.app x i = ((F i).mapId' f hf).hom.toNatTrans.app (x i) := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (pi F)]
  rfl

@[simp]
lemma mapId'_inv_app_apply {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (pi F).obj X) (i : I) :
    ((pi F).mapId' f hf).inv.toNatTrans.app x i = ((F i).mapId' f hf).inv.toNatTrans.app (x i) := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (pi F)]
  rfl

@[simp]
lemma mapComp'_hom_app_apply {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (pi F).obj X) (i : I) :
    ((pi F).mapComp' f g fg h).hom.toNatTrans.app x i =
      ((F i).mapComp' f g fg h).hom.toNatTrans.app (x i) := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (pi F)]
  rfl

@[simp]
lemma mapComp'_inv_app_apply {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (pi F).obj X) (i : I) :
    ((pi F).mapComp' f g fg h).inv.toNatTrans.app x i =
      ((F i).mapComp' f g fg h).inv.toNatTrans.app (x i) := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (pi F)]
  rfl

/-! ### The projections -/

/-- The projection `pi F ⟶ F i`, with components the evaluation functors at `i`. -/
def π (i : I) : pi F ⟶ F i where
  app X := (Pi.eval (fun i ↦ (F i).obj X) i).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := Pseudofunctor.naturality_naturality_of_locallyDiscrete (pi F) (F i)
    (fun X ↦ (Pi.eval (fun i ↦ (F i).obj X) i).toCatHom) (fun _ ↦ Iso.refl _) η
  naturality_id X := by
    ext x
    -- The naturality isomorphisms are identities between `1`-morphisms that agree only
    -- definitionally, so the whiskered identities are evaluated by `change`.
    change 𝟙 _ ≫ ((F i).mapId X).hom.toNatTrans.app (x i) =
      ((pi F).mapId X).hom.toNatTrans.app x i ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (pi F), mapId'_hom_app_apply,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 ((F i).obj X)).toFunctor.obj (x i)`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `naturality_id`.
    change 𝟙 _ ≫ ((F i).mapComp f g).hom.toNatTrans.app (x i) =
      ((pi F).mapComp f g).hom.toNatTrans.app x i ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        ((F i).map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (pi F), mapComp'_hom_app_apply,
      Pseudofunctor.mapComp'_eq_mapComp]
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    -- The remaining identities live over objects that are only definitionally `F i`-pullbacks.
    erw [Category.comp_id, Category.comp_id]

@[simp]
lemma π_app_toFunctor (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    ((π F i).app X).toFunctor = Pi.eval (fun i ↦ (F i).obj X) i :=
  (rfl)

/-- The naturality isomorphisms of the projections are identities. -/
@[simp]
lemma π_naturality_hom_app (i : I) {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (pi F).obj X) :
    ((π F i).naturality f).hom.toNatTrans.app x = 𝟙 _ :=
  (rfl)

/-- The naturality isomorphisms of the projections are identities. -/
@[simp]
lemma π_naturality_inv_app (i : I) {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (pi F).obj X) :
    ((π F i).naturality f).inv.toNatTrans.app x = 𝟙 _ :=
  (rfl)

/-! ### The 2-universal property

A strong transformation `K ⟶ pi F` is given by a family of strong transformations `a i : K ⟶ F i`
(`lift`, with `liftCompπ`). A modification between two strong transformations into `pi F` is given
by a family of modifications between their composites with the projections (`homMk`, and `isoMk`
for invertible ones), and is determined by these (`hom_ext`). -/

section lift

variable {F} {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
  (a : ∀ i, K ⟶ F i)

/-- The component over `X` of `lift a`: an object `k` goes to the family of its images under the
`a i`. -/
abbrev liftApp (X : LocallyDiscrete Cᵒᵖ) : K.obj X ⥤ Fiber F X.as :=
  Functor.pi' fun i ↦ ((a i).app X).toFunctor

/-- The naturality isomorphism of `lift a` at `f`, with components those of the `a i`. -/
@[simps!]
def liftNaturality {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) :
    (K.map f).toFunctor ⋙ liftApp a Y ≅ liftApp a X ⋙ map F f.as :=
  NatIso.ofComponents (fun k ↦ Pi.isoMk fun i ↦ (Cat.Hom.toNatIso ((a i).naturality f)).app k)
    (fun φ ↦ funext fun i ↦ ((a i).naturality f).hom.toNatTrans.naturality φ)

/-- The strong transformation `K ⟶ pi F` induced by a family of strong transformations
`a i : K ⟶ F i`. -/
def lift : K ⟶ pi F where
  app X := (liftApp a X).toCatHom
  naturality f := Cat.Hom.isoMk (liftNaturality a f)
  naturality_naturality η := Pseudofunctor.naturality_naturality_of_locallyDiscrete K (pi F)
    (fun X ↦ (liftApp a X).toCatHom) (fun f ↦ Cat.Hom.isoMk (liftNaturality a f)) η
  -- The comparisons of the product are by construction those of the `F i`, the unitors and
  -- associators of `Cat` have identity components, and all of these agree with the components
  -- of the corresponding cells of the `a i` only definitionally.
  naturality_id X := by
    ext k
    funext i
    have h : ((F i).mapId' (𝟙 X) rfl).hom.toNatTrans.app (((a i).app X).toFunctor.obj k) =
        ((F i).mapId X).hom.toNatTrans.app (((a i).app X).toFunctor.obj k) := by
      rw [Pseudofunctor.mapId'_eq_mapId]
    exact (congrArg (((a i).naturality (𝟙 X)).hom.toNatTrans.app k ≫ ·) h).trans
      (congrArg (fun m ↦ m.toNatTrans.app k) ((a i).naturality_id X))
  naturality_comp f g := by
    ext k
    funext i
    have h : ((F i).mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app
          (((a i).app _).toFunctor.obj k) =
        ((F i).mapComp f g).hom.toNatTrans.app (((a i).app _).toFunctor.obj k) := by
      rw [Pseudofunctor.mapComp'_eq_mapComp]
    exact (congrArg (((a i).naturality (f ≫ g)).hom.toNatTrans.app k ≫ ·) h).trans
      (congrArg (fun m ↦ m.toNatTrans.app k) ((a i).naturality_comp f g))

@[simp]
lemma lift_app_toFunctor (X : LocallyDiscrete Cᵒᵖ) :
    ((lift a).app X).toFunctor = liftApp a X :=
  (rfl)

/-- The naturality isomorphisms of `lift a` have the naturality isomorphisms of the `a i` as
components. -/
@[simp]
lemma lift_naturality_hom_app {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (k : K.obj X) (i : I) :
    ((lift a).naturality f).hom.toNatTrans.app k i = ((a i).naturality f).hom.toNatTrans.app k :=
  (rfl)

/-- The naturality isomorphisms of `lift a` have the naturality isomorphisms of the `a i` as
components. -/
@[simp]
lemma lift_naturality_inv_app {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (k : K.obj X) (i : I) :
    ((lift a).naturality f).inv.toNatTrans.app k i = ((a i).naturality f).inv.toNatTrans.app k :=
  (rfl)

/-- The `i`-th projection of `lift a` is `a i`. -/
def liftCompπ (i : I) : lift a ≫ π F i ≅ a i :=
  Pseudofunctor.StrongTrans.isoMk (fun X ↦ Iso.refl ((a i).app X)) (fun f ↦ by
    ext k
    -- The components `Iso.refl ((a i).app X)` have source `(lift a ≫ π F i).app X`, which is
    -- `(a i).app X` only definitionally, so `change` states the goal with the components
    -- evaluated: the naturality of `a i` at `k`, and identities from the naturality of `π F i`,
    -- the associators of `Cat` and the `Iso.refl`s.
    change 𝟙 _ ≫ ((a i).naturality f).hom.toNatTrans.app k =
      (𝟙 _ ≫ ((a i).naturality f).hom.toNatTrans.app k ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
        ((F i).map f).toFunctor.map (𝟙 _)
    simp)

@[simp]
lemma liftCompπ_hom_as_app (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    (liftCompπ a i).hom.as.app X = 𝟙 _ :=
  rfl

@[simp]
lemma liftCompπ_inv_as_app (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    (liftCompπ a i).inv.as.app X = 𝟙 _ :=
  rfl

end lift

section homMk

variable {F} {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
  {φ ψ : K ⟶ pi F}

/-- The components of a modification `φ ≫ π F i ⟶ ψ ≫ π F i` are natural with respect to the
naturality isomorphisms of `φ` and `ψ`, on `i`-th components. -/
private lemma naturality_apply {i : I} (m : φ ≫ π F i ⟶ ψ ≫ π F i) {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (k : K.obj X) :
    (m.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
        (ψ.naturality f).hom.toNatTrans.app k i =
      (φ.naturality f).hom.toNatTrans.app k i ≫
        ((F i).map f).toFunctor.map ((m.as.app X).toNatTrans.app k) := by
  have h := congrArg (fun m ↦ m.toNatTrans.app k) (m.as.naturality f)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  -- The naturality isomorphisms of `π F i` are identities.
  have h' : (m.as.app Y).toNatTrans.app ((K.map f).toFunctor.obj k) ≫
      (ψ.naturality f).hom.toNatTrans.app k i ≫ 𝟙 _ =
        ((φ.naturality f).hom.toNatTrans.app k i ≫ 𝟙 _) ≫
          ((F i).map f).toFunctor.map ((m.as.app X).toNatTrans.app k) := h
  simp only [Category.comp_id] at h'
  -- The remaining identity lives over a pullback in the product, only definitionally a pullback
  -- along `F i`.
  erw [Category.comp_id] at h'
  exact h'

/-- A modification `φ ⟶ ψ` between strong transformations into the product, from a family of
modifications `m i : φ ≫ π F i ⟶ ψ ≫ π F i`. -/
def homMk (m : ∀ i, φ ≫ π F i ⟶ ψ ≫ π F i) : φ ⟶ ψ where
  as.app X := Cat.Hom₂.ofNatTrans
    { app k i := ((m i).as.app X).toNatTrans.app k
      naturality k l u := funext fun i ↦ ((m i).as.app X).toNatTrans.naturality u }
  as.naturality f := by
    ext k
    funext i
    exact naturality_apply (m i) f k

/-- The components of `homMk m` are those of the `m i`. -/
@[simp]
lemma homMk_as_app_app (m : ∀ i, φ ≫ π F i ⟶ ψ ≫ π F i) (X : LocallyDiscrete Cᵒᵖ) (k : K.obj X)
    (i : I) : ((homMk m).as.app X).toNatTrans.app k i = ((m i).as.app X).toNatTrans.app k :=
  (rfl)

/-- The `i`-th projection of `homMk m` is `m i`. -/
@[simp]
lemma homMk_whiskerRight_π (m : ∀ i, φ ≫ π F i ⟶ ψ ≫ π F i) (i : I) :
    homMk m ▷ π F i = m i := by
  ext X k
  rw [Pseudofunctor.StrongTrans.whiskerRight_as_app]
  rfl

/-- Two modifications into the product agree when their composites with all projections do. -/
lemma hom_ext {m n : φ ⟶ ψ} (h : ∀ i, m ▷ π F i = n ▷ π F i) : m = n := by
  ext X k
  funext i
  have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) (h i)
  simp only [Pseudofunctor.StrongTrans.whiskerRight_as_app] at h
  exact h

/-- An isomorphism `φ ≅ ψ` between strong transformations into the product, from a family of
isomorphisms `e i : φ ≫ π F i ≅ ψ ≫ π F i`. -/
@[simps]
def isoMk (e : ∀ i, φ ≫ π F i ≅ ψ ≫ π F i) : φ ≅ ψ where
  hom := homMk fun i ↦ (e i).hom
  inv := homMk fun i ↦ (e i).inv
  hom_inv_id := hom_ext fun i ↦ by simp
  inv_hom_id := hom_ext fun i ↦ by simp

end homMk

end pi

/-! ### The terminal pseudofunctor -/

/-- The terminal pseudofunctor `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, the product of the empty family: its
fibers have exactly one object and one morphism. -/
def terminal : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'} :=
  pi (C := C) (I := PEmpty.{1}) fun i ↦ i.elim

namespace terminal

instance instUniqueObj (X : LocallyDiscrete Cᵒᵖ) :
    Unique ((terminal.{u', v'} (C := C)).obj X) where
  default := fun i ↦ i.elim
  uniq _ := funext fun i ↦ i.elim

/-- The fibers of the terminal pseudofunctor are groupoids. -/
instance instIsGroupoidObj (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((terminal.{u', v'} (C := C)).obj X) :=
  @pi.instIsGroupoidObj _ _ _ _ X fun i ↦ i.elim

variable (K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- The strong transformation from a pseudofunctor to the terminal pseudofunctor. -/
def lift : K ⟶ terminal :=
  pi.lift fun i ↦ i.elim

variable {K} (φ ψ : K ⟶ terminal)

/-- The modification between two strong transformations to the terminal pseudofunctor. -/
def homMk : φ ⟶ ψ :=
  pi.homMk fun i ↦ i.elim

/-- Any two modifications between strong transformations to the terminal pseudofunctor agree. -/
lemma hom_ext (m n : φ ⟶ ψ) : m = n :=
  pi.hom_ext fun i ↦ i.elim

end terminal

end TauCeti.Stack

end
