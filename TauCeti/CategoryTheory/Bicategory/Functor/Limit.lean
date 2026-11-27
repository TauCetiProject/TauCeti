/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Groupoid
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Pseudo-limits of diagrams of pseudofunctors

Let `C` be a category, `I` a small category and
`D : LocallyDiscrete I ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat)` a diagram of pseudofunctors indexed by
`I`: pseudofunctors `D i` with strong transformations `D(f) : D i ⟶ D j` for `f : i ⟶ j`, and
invertible modifications comparing `D(𝟙 i)` with the identity and `D(f ≫ g)` with `D(f) ≫ D(g)`.
Its pseudo-limit `TauCeti.Stack.limit D` is computed fiberwise: an object of its fiber over `T`
(`limit.Fiber D T`) is a family of objects `x i` of the fibers of the `D i` over `T` with
isomorphisms `D(f) (x i) ≅ x j`, compatible with the comparisons of `D`, and a morphism is a
family of morphisms compatible with these isomorphisms. This is the pseudo-limit of the diagram
of fiber categories over `T`; its pullback functors are those of the `D i`, componentwise.

The pseudo-limit comes with projections `limit.π D i : limit D ⟶ D i` and invertible
modifications `limit.πCompMap D f : π D i ≫ D(f) ≅ π D j` compatible with the comparisons of `D`
(`limit.πCompMap_id`, `limit.πCompMap_comp`), that is, with the pseudo-cone `limit.cone D`. It has
the 2-universal property of the pseudo-limit: every pseudo-cone `c : limit.Cone D K` factors
through it (`limit.lift c`, with `limit.liftCompπ` and `limit.lift_whiskerLeft_πCompMap_hom`),
every other such factorization is isomorphic to it (`limit.isoLift`), and modifications between
strong transformations into it are given by compatible families of modifications between their
projections (`limit.homMk`, `limit.isoMk`) and are determined by these (`limit.hom_ext`,
`limit.whiskerRight_π_comp_whiskerLeft_πCompMap`). The fibers of the pseudo-limit of a diagram
with groupoid fibers are groupoids (`limit.instIsGroupoidObj`).

Mathematically, the products `TauCeti.Stack.pi` and the 2-fiber products
`TauCeti.Stack.twoFiberProduct` of pseudofunctors are, up to equivalence, the pseudo-limits over a
discrete category and over a cospan; this file does not compare them. The construction uses no
topology.

The fibers of `limit D` contain, besides the objects and morphisms of the fibers of the `D i`,
families indexed by `I` and by its morphisms, and their morphisms are families indexed by `I`. The
construction is therefore stated for diagrams with values in `Cat.{max w v', max w v' z}` for
`I : Type w`, so that `limit D` takes values in the same bicategory as the `D i`. This includes the
big site of schemes, with `I` in the universe `u` of the schemes and values in `Cat.{u, u + 1}`
(`limit.{u, u + 1, u}`), as well as finite diagrams with values in `Cat.{u, u + 1}`
(`limit.{0, u + 1, u}`); the universes have to be given explicitly there, since the elaborator
does not solve the constraints on `max`. For the same reason the fiber is not taken to be the
category of strong transformations from the constant pseudofunctor at the point: its morphisms,
modifications of `Cat`-valued strong transformations, would lie in the universe of the objects of
the fibers.

## Main declarations

* `TauCeti.Stack.limit.Fiber`: the fibers of the pseudo-limit, with `Fiber.isoMk` and
  `Fiber.isIso_of_isIso_hom`.
* `TauCeti.Stack.limit`: the pseudo-limit of a diagram of pseudofunctors.
* `TauCeti.Stack.limit.π`, `TauCeti.Stack.limit.πCompMap`: the projections and their `2`-cells.
* `TauCeti.Stack.limit.Cone`, `TauCeti.Stack.limit.cone`: pseudo-cones, and the pseudo-cone of
  the pseudo-limit.
* `TauCeti.Stack.limit.lift`, `TauCeti.Stack.limit.liftCompπ`, `TauCeti.Stack.limit.isoLift`,
  `TauCeti.Stack.limit.homMk`, `TauCeti.Stack.limit.isoMk`, `TauCeti.Stack.limit.hom_ext`: the
  2-universal property.

## References

* G. M. Kelly, *Elementary observations on 2-categorical limits*, Bull. Austral. Math. Soc. 39
  (1989), 301–317, for pseudo-limits.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  Chapter 4, for strong transformations and modifications.
-/

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

-- The universe of the objects of the fibers is named `z` so that it comes after `v'` and `w` in
-- the order in which Lean normalizes `max w v' z`: with a name coming before them, unifying
-- `max w v' ?z` with `max w v' z` gets stuck at every use of `D`.
universe w z v' v u

public section

namespace TauCeti.Stack

variable {C : Type u} [Category.{v} C] {I : Type w} [SmallCategory I]
  (D : Pseudofunctor (LocallyDiscrete I)
    (Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z}))

namespace limit

/-- The transition functor `D(f)` over `T` of the diagram, for `f : i ⟶ j`. -/
abbrev transition {i j : I} (f : i ⟶ j) (T : Cᵒᵖ) :
    (D.obj (.mk i)).obj (.mk T) ⥤ (D.obj (.mk j)).obj (.mk T) :=
  ((D.map f.toLoc).app (.mk T)).toFunctor

/-- The unit comparison `D(𝟙 i) X ≅ X` of the diagram over `T`. -/
def transitionIdIso (i : I) (T : Cᵒᵖ) (X : (D.obj (.mk i)).obj (.mk T)) :
    (transition D (𝟙 i) T).obj X ≅ X :=
  (Cat.Hom.toNatIso (Pseudofunctor.StrongTrans.isoApp (D.mapId (.mk i)) (.mk T))).app X

/-- The composition comparison `D(f ≫ g) X ≅ D(g) (D(f) X)` of the diagram over `T`. -/
def transitionCompIso {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (T : Cᵒᵖ)
    (X : (D.obj (.mk i)).obj (.mk T)) :
    (transition D (f ≫ g) T).obj X ≅ (transition D g T).obj ((transition D f T).obj X) :=
  (Cat.Hom.toNatIso (Pseudofunctor.StrongTrans.isoApp (D.mapComp f.toLoc g.toLoc) (.mk T))).app X

lemma transitionIdIso_hom (i : I) (T : Cᵒᵖ) (X : (D.obj (.mk i)).obj (.mk T)) :
    (transitionIdIso D i T X).hom = ((D.mapId (.mk i)).hom.as.app (.mk T)).toNatTrans.app X := by
  simp only [transitionIdIso, Iso.app_hom, Cat.Hom.toNatIso_hom,
    Pseudofunctor.StrongTrans.isoApp_hom]
  -- The two sides differ only in the implicit target `(𝟙 _).app (.mk T)`, which is the identity
  -- functor only definitionally.
  rfl

lemma transitionCompIso_hom {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (T : Cᵒᵖ)
    (X : (D.obj (.mk i)).obj (.mk T)) :
    (transitionCompIso D f g T X).hom =
      ((D.mapComp f.toLoc g.toLoc).hom.as.app (.mk T)).toNatTrans.app X := by
  simp only [transitionCompIso, Iso.app_hom, Cat.Hom.toNatIso_hom,
    Pseudofunctor.StrongTrans.isoApp_hom]
  -- The two sides differ only in the implicit target, a composite of strong transformations
  -- evaluated at `T`, which is the composite of the components only definitionally.
  rfl

/-- The unit comparisons of the diagram commute with the pullback along `a : T ⟶ T'`. -/
lemma transitionIdIso_naturality (i : I) {T T' : Cᵒᵖ} (a : T ⟶ T')
    (X : (D.obj (.mk i)).obj (.mk T)) :
    (transitionIdIso D i T' (((D.obj (.mk i)).map a.toLoc).toFunctor.obj X)).hom =
      ((D.map (𝟙 i).toLoc).naturality a.toLoc).hom.toNatTrans.app X ≫
        ((D.obj (.mk i)).map a.toLoc).toFunctor.map (transitionIdIso D i T X).hom := by
  have h := Pseudofunctor.StrongTrans.Modification.naturality_app (D.mapId (.mk i)).hom.as
    a.toLoc X
  rw [Pseudofunctor.StrongTrans.id_naturality_hom_app] at h
  rw [transitionIdIso_hom, transitionIdIso_hom]
  -- The identity in `h` lives over an object that is only definitionally the target of the
  -- component of `D.mapId`.
  exact (Category.comp_id _).symm.trans h

/-- The composition comparisons of the diagram commute with the pullback along `a : T ⟶ T'`. -/
@[reassoc]
lemma transitionCompIso_naturality {i j k : I} (f : i ⟶ j) (g : j ⟶ k) {T T' : Cᵒᵖ}
    (a : T ⟶ T') (X : (D.obj (.mk i)).obj (.mk T)) :
    ((D.map (f ≫ g).toLoc).naturality a.toLoc).hom.toNatTrans.app X ≫
        ((D.obj (.mk k)).map a.toLoc).toFunctor.map (transitionCompIso D f g T X).hom =
      (transitionCompIso D f g T' (((D.obj (.mk i)).map a.toLoc).toFunctor.obj X)).hom ≫
        (transition D g T').map (((D.map f.toLoc).naturality a.toLoc).hom.toNatTrans.app X) ≫
          ((D.map g.toLoc).naturality a.toLoc).hom.toNatTrans.app
            ((transition D f T).obj X) := by
  have h := Pseudofunctor.StrongTrans.Modification.naturality_app
    (D.mapComp f.toLoc g.toLoc).hom.as a.toLoc X
  rw [Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  rw [transitionCompIso_hom, transitionCompIso_hom]
  exact h.symm

/-- An object of the fiber over `T` of the pseudo-limit of `D`: a family of objects `obj i` of the
fibers over `T` of the `D i`, with isomorphisms `iso f : D(f) (obj i) ≅ obj j` for `f : i ⟶ j`,
compatible with the unit and composition comparisons of `D`. -/
structure Fiber (T : Cᵒᵖ) : Type (max w v' z) where
  /-- The component in the fiber of `D i` over `T`. -/
  obj (i : I) : (D.obj (.mk i)).obj (.mk T)
  /-- The transition isomorphism along `f : i ⟶ j`. -/
  iso {i j : I} (f : i ⟶ j) : (transition D f T).obj (obj i) ≅ obj j
  iso_id (i : I) : (iso (𝟙 i)).hom = (transitionIdIso D i T (obj i)).hom
  iso_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (iso (f ≫ g)).hom = (transitionCompIso D f g T (obj i)).hom ≫
      (transition D g T).map (iso f).hom ≫ (iso g).hom

variable {D}

namespace Fiber

variable {T : Cᵒᵖ}

/-- A morphism in the fiber over `T` of the pseudo-limit: a family of morphisms of the components,
compatible with the transition isomorphisms. -/
@[ext]
structure Hom (x y : Fiber D T) where
  /-- The component in the fiber of `D i` over `T`. -/
  hom (i : I) : x.obj i ⟶ y.obj i
  comm {i j : I} (f : i ⟶ j) :
    (transition D f T).map (hom i) ≫ (y.iso f).hom = (x.iso f).hom ≫ hom j

attribute [reassoc] Hom.comm

instance : Category (Fiber D T) where
  Hom := Hom
  id x := { hom i := 𝟙 (x.obj i), comm f := by simp }
  comp φ ψ :=
    { hom i := φ.hom i ≫ ψ.hom i
      comm f := by simp [Hom.comm, Hom.comm_assoc] }

@[ext]
lemma hom_ext {x y : Fiber D T} {φ ψ : x ⟶ y} (h : ∀ i, φ.hom i = ψ.hom i) : φ = ψ :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (x : Fiber D T) (i : I) : Hom.hom (𝟙 x) i = 𝟙 (x.obj i) :=
  rfl

@[simp, reassoc]
lemma comp_hom {x y z : Fiber D T} (φ : x ⟶ y) (ψ : y ⟶ z) (i : I) :
    (φ ≫ ψ).hom i = φ.hom i ≫ ψ.hom i :=
  rfl

/-- An isomorphism in the fiber over `T`, from isomorphisms of the components compatible with the
transition isomorphisms. -/
def isoMk {x y : Fiber D T} (e : ∀ i, x.obj i ≅ y.obj i)
    (comm : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      (transition D f T).map (e i).hom ≫ (y.iso f).hom = (x.iso f).hom ≫ (e j).hom) :
    x ≅ y where
  hom := { hom i := (e i).hom, comm f := comm f }
  inv :=
    { hom i := (e i).inv
      comm {i j} f := by
        rw [← cancel_epi ((transition D f T).map (e i).hom), ← Functor.map_comp_assoc,
          Iso.hom_inv_id, Functor.map_id, Category.id_comp, reassoc_of% (comm f),
          Iso.hom_inv_id, Category.comp_id] }

section isoMk

variable {x y : Fiber D T} (e : ∀ i, x.obj i ≅ y.obj i)
  (comm : ∀ ⦃i j : I⦄ (f : i ⟶ j),
    (transition D f T).map (e i).hom ≫ (y.iso f).hom = (x.iso f).hom ≫ (e j).hom)

@[simp]
lemma isoMk_hom_hom (i : I) : (isoMk e comm).hom.hom i = (e i).hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom (i : I) : (isoMk e comm).inv.hom i = (e i).inv :=
  (rfl)

end isoMk

/-- A morphism of the fiber over `T` whose components are isomorphisms is an isomorphism. -/
lemma isIso_of_isIso_hom {x y : Fiber D T} (φ : x ⟶ y) [∀ i, IsIso (φ.hom i)] : IsIso φ :=
  (isoMk (fun i ↦ asIso (φ.hom i)) fun _ _ f ↦ φ.comm f).isIso_hom

/-- The fibers of the pseudo-limit of a diagram with groupoid fibers are groupoids. -/
instance [∀ i, IsGroupoid ((D.obj (.mk i)).obj (.mk T))] : IsGroupoid (Fiber D T) where
  all_isIso φ := isIso_of_isIso_hom φ

end Fiber

variable (D) in
/-- The pullback along `a : T ⟶ T'` in `Cᵒᵖ` of an object of the fiber over `T`: its components
are the pullbacks along `a` of the components, and its transition isomorphisms are the pullbacks
of the transition isomorphisms, conjugated by the naturality isomorphisms of the `D f`. -/
-- Reducible so that the components and transition isomorphisms of a pullback are seen by `rw`
-- and `simp` as those of the original object, pulled back.
@[expose, reducible, simps]
def mapObj {T T' : Cᵒᵖ} (a : T ⟶ T') (x : Fiber D T) : Fiber D T' where
  obj i := ((D.obj (.mk i)).map a.toLoc).toFunctor.obj (x.obj i)
  iso {i j} f := (Cat.Hom.toNatIso ((D.map f.toLoc).naturality a.toLoc)).app (x.obj i) ≪≫
    ((D.obj _).map a.toLoc).toFunctor.mapIso (x.iso f)
  iso_id i := by
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, x.iso_id, Cat.Hom.toNatIso_hom,
      transitionIdIso_naturality]
  iso_comp {i j k} f g := by
    have h := ((D.map g.toLoc).naturality a.toLoc).hom.toNatTrans.naturality (x.iso f).hom
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at h
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, x.iso_comp, Functor.map_comp,
      Cat.Hom.toNatIso_hom, Category.assoc, transitionCompIso_naturality_assoc]
    rw [reassoc_of% h]

variable (D) in
/-- The pullback along `a : T ⟶ T'` of a morphism of the fiber over `T`, componentwise. -/
-- Reducible for the same reason as `mapObj`.
@[expose, reducible]
def mapHom {T T' : Cᵒᵖ} (a : T ⟶ T') {x y : Fiber D T} (φ : x ⟶ y) :
    mapObj D a x ⟶ mapObj D a y where
  hom i := ((D.obj (.mk i)).map a.toLoc).toFunctor.map (φ.hom i)
  comm {i j} f := by
    have h := ((D.map f.toLoc).naturality a.toLoc).hom.toNatTrans.naturality (φ.hom i)
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at h
    simp only [Iso.trans_hom, Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.mapIso_hom]
    rw [Category.assoc, reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp, φ.comm f]

variable (D) in
/-- The pullback functor of the pseudo-limit along `a : T ⟶ T'` in `Cᵒᵖ`. -/
-- Reducible for the same reason as `mapObj`.
@[expose, reducible]
def map {T T' : Cᵒᵖ} (a : T ⟶ T') : Fiber D T ⥤ Fiber D T' where
  obj := mapObj D a
  map := mapHom D a
  map_id x := by ext; simp
  map_comp φ ψ := by ext; simp

variable (D) in
/-- The unit isomorphism of the pseudo-limit, from the unit comparisons of the `D i`. -/
def mapIdIso (T : Cᵒᵖ) : map D (𝟙 T) ≅ 𝟭 (Fiber D T) :=
  NatIso.ofComponents
    (fun x ↦ Fiber.isoMk
      (fun i ↦ (Cat.Hom.toNatIso ((D.obj (.mk i)).mapId' (𝟙 T).toLoc)).app (x.obj i))
      (fun i j f ↦ by
        have h := ((D.obj (.mk j)).mapId' (𝟙 T).toLoc).hom.toNatTrans.naturality (x.iso f).hom
        simp only [Cat.Hom.id_toFunctor, Functor.id_map] at h
        simp only [Iso.trans_hom, Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.mapIso_hom]
        rw [Category.assoc, h,
          Pseudofunctor.StrongTrans.naturality_id'_hom_app_comp_mapId'_hom_app_assoc]
        -- The fiber of `𝟭 (Fiber D T)` at `x` is `x` only definitionally.
        rfl))
    (fun φ ↦ by
      ext i
      exact ((D.obj (.mk i)).mapId' (𝟙 T).toLoc).hom.toNatTrans.naturality (φ.hom i))

variable (D) in
/-- The composition isomorphism of the pseudo-limit at a factorization `a ≫ b = ab`, from the
composition comparisons of the `D i`. -/
def mapCompIso {T T' T'' : Cᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') (ab : T ⟶ T'') (h : a ≫ b = ab) :
    map D ab ≅ map D a ⋙ map D b :=
  NatIso.ofComponents
    (fun x ↦ Fiber.isoMk
      (fun i ↦ (Cat.Hom.toNatIso ((D.obj (.mk i)).mapComp' a.toLoc b.toLoc ab.toLoc
        (congrArg Quiver.Hom.toLoc h))).app (x.obj i))
      (fun i j f ↦ by
        have h' := ((D.obj (.mk j)).mapComp' a.toLoc b.toLoc ab.toLoc
          (congrArg Quiver.Hom.toLoc h)).hom.toNatTrans.naturality (x.iso f).hom
        simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at h'
        simp only [Iso.trans_hom, Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.mapIso_hom,
          Functor.comp_obj, Functor.map_comp, Category.assoc,
          Pseudofunctor.StrongTrans.naturality_comp'_hom_app (D.map f.toLoc) a.toLoc b.toLoc
            ab.toLoc (congrArg Quiver.Hom.toLoc h), h']
        simp))
    (fun φ ↦ by
      ext i
      exact ((D.obj (.mk i)).mapComp' a.toLoc b.toLoc ab.toLoc
        (congrArg Quiver.Hom.toLoc h)).hom.toNatTrans.naturality (φ.hom i))

@[simp]
lemma mapIdIso_hom_app_hom (T : Cᵒᵖ) (x : Fiber D T) (i : I) :
    ((mapIdIso D T).hom.app x).hom i =
      ((D.obj (.mk i)).mapId' (𝟙 T).toLoc).hom.toNatTrans.app (x.obj i) :=
  (rfl)

@[simp]
lemma mapIdIso_inv_app_hom (T : Cᵒᵖ) (x : Fiber D T) (i : I) :
    ((mapIdIso D T).inv.app x).hom i =
      ((D.obj (.mk i)).mapId' (𝟙 T).toLoc).inv.toNatTrans.app (x.obj i) :=
  (rfl)

@[simp]
lemma mapCompIso_hom_app_hom {T T' T'' : Cᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') (ab : T ⟶ T'')
    (h : a ≫ b = ab) (x : Fiber D T) (i : I) :
    ((mapCompIso D a b ab h).hom.app x).hom i =
      ((D.obj (.mk i)).mapComp' a.toLoc b.toLoc ab.toLoc
        (congrArg Quiver.Hom.toLoc h)).hom.toNatTrans.app (x.obj i) :=
  (rfl)

@[simp]
lemma mapCompIso_inv_app_hom {T T' T'' : Cᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') (ab : T ⟶ T'')
    (h : a ≫ b = ab) (x : Fiber D T) (i : I) :
    ((mapCompIso D a b ab h).inv.app x).hom i =
      ((D.obj (.mk i)).mapComp' a.toLoc b.toLoc ab.toLoc
        (congrArg Quiver.Hom.toLoc h)).inv.toNatTrans.app (x.obj i) :=
  (rfl)

end limit

open limit in
/-- The **pseudo-limit** of a diagram `D : LocallyDiscrete I ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat)` of
pseudofunctors, computed fiberwise: its fiber over `T` is the pseudo-limit of the fibers over `T`
of the `D i` (`limit.Fiber D T`), and its pullback functors and comparisons are those of the
`D i`, componentwise. -/
-- Exposed so that the fibers of `limit D` are seen as the categories `Fiber D X.as` in the
-- statements of the lemmas on their objects and morphisms.
@[expose]
def limit : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun T ↦ Cat.of (Fiber D T)) (map D)
    (mapIdIso D) (mapCompIso D)
    (fun _ _ _ _ _ _ hfg hgh hfgh hfgh' x ↦ by
      refine Fiber.hom_ext fun i ↦ ?_
      exact (D.obj (.mk i)).mapComp'_hom_app_comp_map_mapComp'_hom_app _ _ _ _ _ _
        (congrArg Quiver.Hom.toLoc hfg) (congrArg Quiver.Hom.toLoc hgh)
        (congrArg Quiver.Hom.toLoc hfgh) (congrArg Quiver.Hom.toLoc hfgh') (x.obj i))
    (fun _ hf x ↦ by
      refine Fiber.hom_ext fun i ↦ ?_
      exact (D.obj (.mk i)).mapComp'_hom_app_comp_map_mapId'_hom_app _ rfl _
        (congrArg Quiver.Hom.toLoc hf) (x.obj i))
    (fun _ hf x ↦ by
      refine Fiber.hom_ext fun i ↦ ?_
      exact (D.obj (.mk i)).mapComp'_hom_app_comp_mapId'_hom_app _ rfl _
        (congrArg Quiver.Hom.toLoc hf) (x.obj i))

namespace limit

variable {D}

/-! ### Components of the pseudo-limit

The fibers `(limit D).obj X` are the categories `Fiber D X.as` only after unfolding `limit`, so the
following lemmas are stated on them directly. -/

@[simp]
lemma comp_hom' {X : LocallyDiscrete Cᵒᵖ} {x y z : (limit D).obj X} (φ : x ⟶ y) (ψ : y ⟶ z)
    (i : I) : Fiber.Hom.hom (φ ≫ ψ) i = Fiber.Hom.hom φ i ≫ Fiber.Hom.hom ψ i :=
  rfl

@[simp]
lemma id_hom' {X : LocallyDiscrete Cᵒᵖ} (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (𝟙 x) i = 𝟙 (Fiber.obj x i) :=
  rfl

@[simp]
lemma map_obj_obj {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (limit D).obj X) (i : I) :
    Fiber.obj (((limit D).map f).toFunctor.obj x) i =
      ((D.obj (.mk i)).map f).toFunctor.obj (Fiber.obj x i) :=
  rfl

@[simp]
lemma map_obj_iso_hom {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (limit D).obj X) {i j : I}
    (g : i ⟶ j) :
    (Fiber.iso (((limit D).map f).toFunctor.obj x) g).hom =
      ((D.map g.toLoc).naturality f).hom.toNatTrans.app (Fiber.obj x i) ≫
        ((D.obj (.mk j)).map f).toFunctor.map (Fiber.iso x g).hom :=
  rfl

@[simp]
lemma map_map_hom {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) {x y : (limit D).obj X} (φ : x ⟶ y)
    (i : I) :
    Fiber.Hom.hom (((limit D).map f).toFunctor.map φ) i =
      ((D.obj (.mk i)).map f).toFunctor.map (Fiber.Hom.hom φ i) :=
  rfl

-- In the following lemmas, after `subst`, the comparison `(limit D).mapComp f g` is by
-- construction the family of the `(D i).mapComp' f g (f ≫ g) rfl`, and similarly for the unit
-- comparisons.

@[simp]
lemma mapId'_hom_app_hom {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapId' f hf).hom.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapId' f hf).hom.toNatTrans.app (Fiber.obj x i) := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (limit D)]
  rfl

@[simp]
lemma mapId'_inv_app_hom {X : LocallyDiscrete Cᵒᵖ} (f : X ⟶ X) (hf : f = 𝟙 X)
    (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapId' f hf).inv.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapId' f hf).inv.toNatTrans.app (Fiber.obj x i) := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId (limit D)]
  rfl

@[simp]
lemma mapComp'_hom_app_hom {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapComp' f g fg h).hom.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapComp' f g fg h).hom.toNatTrans.app (Fiber.obj x i) := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (limit D)]
  rfl

@[simp]
lemma mapComp'_inv_app_hom {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapComp' f g fg h).inv.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapComp' f g fg h).inv.toNatTrans.app (Fiber.obj x i) := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp (limit D)]
  rfl

@[simp]
lemma mapId_hom_app_hom (X : LocallyDiscrete Cᵒᵖ) (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapId X).hom.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapId X).hom.toNatTrans.app (Fiber.obj x i) := by
  simpa only [Pseudofunctor.mapId'_eq_mapId] using mapId'_hom_app_hom (𝟙 X) rfl x i

@[simp]
lemma mapId_inv_app_hom (X : LocallyDiscrete Cᵒᵖ) (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapId X).inv.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapId X).inv.toNatTrans.app (Fiber.obj x i) := by
  simpa only [Pseudofunctor.mapId'_eq_mapId] using mapId'_inv_app_hom (𝟙 X) rfl x i

@[simp]
lemma mapComp_hom_app_hom {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapComp f g).hom.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapComp f g).hom.toNatTrans.app (Fiber.obj x i) := by
  simpa only [Pseudofunctor.mapComp'_eq_mapComp] using mapComp'_hom_app_hom f g _ rfl x i

@[simp]
lemma mapComp_inv_app_hom {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (limit D).obj X) (i : I) :
    Fiber.Hom.hom (((limit D).mapComp f g).inv.toNatTrans.app x) i =
      ((D.obj (.mk i)).mapComp f g).inv.toNatTrans.app (Fiber.obj x i) := by
  simpa only [Pseudofunctor.mapComp'_eq_mapComp] using mapComp'_inv_app_hom f g _ rfl x i

/-- The fibers of the pseudo-limit of a diagram with groupoid fibers are groupoids. -/
instance instIsGroupoidObj (X : LocallyDiscrete Cᵒᵖ) [∀ i, IsGroupoid ((D.obj (.mk i)).obj X)] :
    IsGroupoid ((limit D).obj X) :=
  inferInstanceAs (IsGroupoid (Fiber D X.as))

/-! ### The projections -/

variable (D) in
/-- The evaluation functor `Fiber D T ⥤ (D i)(T)` at `i`. -/
-- Exposed, as is `π`, so that the components of `π D i` are seen in the statements of its lemmas
-- as the components of the objects of the pseudo-limit.
@[expose, simps]
def Fiber.eval (T : Cᵒᵖ) (i : I) : Fiber D T ⥤ (D.obj (.mk i)).obj (.mk T) where
  obj x := x.obj i
  map φ := φ.hom i

variable (D) in
/-- The projection `limit D ⟶ D i`, with components the evaluation functors at `i`. -/
@[expose]
def π (i : I) : limit D ⟶ D.obj (.mk i) where
  app X := (Fiber.eval D X.as i).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := Pseudofunctor.naturality_naturality_of_locallyDiscrete (limit D)
    (D.obj (.mk i)) (fun X ↦ (Fiber.eval D X.as i).toCatHom) (fun _ ↦ Iso.refl _) η
  naturality_id X := by
    ext x
    -- The naturality isomorphisms are identities between `1`-morphisms that agree only
    -- definitionally, so the whiskered identities are evaluated by `change`.
    change 𝟙 _ ≫ ((D.obj (.mk i)).mapId X).hom.toNatTrans.app (Fiber.obj x i) =
      Fiber.Hom.hom (((limit D).mapId X).hom.toNatTrans.app x) i ≫ 𝟙 _ ≫ 𝟙 _
    rw [← Pseudofunctor.mapId'_eq_mapId (limit D), mapId'_hom_app_hom,
      Pseudofunctor.mapId'_eq_mapId]
    simp only [Category.id_comp]
    -- The remaining identity lives over `(𝟙 ((D i).obj X)).toFunctor.obj (x i)`.
    erw [Category.comp_id]
  naturality_comp f g := by
    ext x
    -- As for `naturality_id`.
    change 𝟙 _ ≫ ((D.obj (.mk i)).mapComp f g).hom.toNatTrans.app (Fiber.obj x i) =
      Fiber.Hom.hom (((limit D).mapComp f g).hom.toNatTrans.app x) i ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        ((D.obj (.mk i)).map g).toFunctor.map (𝟙 _) ≫ 𝟙 _
    rw [← Pseudofunctor.mapComp'_eq_mapComp (limit D), mapComp'_hom_app_hom,
      Pseudofunctor.mapComp'_eq_mapComp]
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    -- The remaining identities live over objects that are only definitionally `D i`-pullbacks.
    erw [Category.comp_id, Category.comp_id]

@[simp]
lemma π_app_toFunctor (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    ((π D i).app X).toFunctor = Fiber.eval D X.as i :=
  rfl

/-- The naturality isomorphisms of the projections are identities. -/
@[simp]
lemma π_naturality_hom_app (i : I) {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (limit D).obj X) :
    ((π D i).naturality f).hom.toNatTrans.app x = 𝟙 _ :=
  rfl

/-- The naturality isomorphisms of the projections are identities. -/
@[simp]
lemma π_naturality_inv_app (i : I) {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (limit D).obj X) :
    ((π D i).naturality f).inv.toNatTrans.app x = 𝟙 _ :=
  rfl

variable (D) in
/-- The invertible modification `π i ≫ D(f) ≅ π j` of the pseudo-limit, for `f : i ⟶ j`, with
components the transition isomorphisms of the objects of the pseudo-limit. -/
def πCompMap {i j : I} (f : i ⟶ j) : π D i ≫ D.map f.toLoc ≅ π D j :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun x ↦ Fiber.iso (D := D) (T := X.as) x f)
      (fun φ ↦ φ.comm f)))
    (fun {X Y} g ↦ by
      ext x
      -- The naturality isomorphisms of the projections and the associators of `Cat` have
      -- identity components, which agree with the identities below only definitionally, so the
      -- components of both sides are evaluated by `change`.
      change (Fiber.iso (((limit D).map g).toFunctor.obj x) f).hom ≫ 𝟙 _ =
        (𝟙 _ ≫ ((D.map f.toLoc).app Y).toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
          ((D.map f.toLoc).naturality g).hom.toNatTrans.app (Fiber.obj x i) ≫ 𝟙 _) ≫
            ((D.obj (.mk j)).map g).toFunctor.map (Fiber.iso x f).hom
      simp)

@[simp]
lemma πCompMap_hom_as_app {i j : I} (f : i ⟶ j) (X : LocallyDiscrete Cᵒᵖ) (x : (limit D).obj X) :
    ((πCompMap D f).hom.as.app X).toNatTrans.app x = (Fiber.iso x f).hom :=
  (rfl)

@[simp]
lemma πCompMap_inv_as_app {i j : I} (f : i ⟶ j) (X : LocallyDiscrete Cᵒᵖ) (x : (limit D).obj X) :
    ((πCompMap D f).inv.as.app X).toNatTrans.app x = (Fiber.iso x f).inv :=
  (rfl)

/-- The `2`-cell of the pseudo-limit at an identity is the unit comparison of `D`. -/
lemma πCompMap_id (i : I) :
    (πCompMap D (𝟙 i)).hom = π D i ◁ (D.mapId (.mk i)).hom ≫ (ρ_ (π D i)).hom := by
  ext X x
  -- The right unitor of `Cat` has identity components, which agree with the identity below only
  -- definitionally.
  change (Fiber.iso x (𝟙 i)).hom =
    ((D.mapId (.mk i)).hom.as.app X).toNatTrans.app (Fiber.obj x i) ≫ 𝟙 _
  exact (Fiber.iso_id x i).trans ((transitionIdIso_hom D i X.as _).trans (Category.comp_id _).symm)

/-- The `2`-cell of the pseudo-limit at a composite is the composite of the `2`-cells, up to the
composition comparison of `D`. -/
lemma πCompMap_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (πCompMap D (f ≫ g)).hom = π D i ◁ (D.mapComp f.toLoc g.toLoc).hom ≫ (α_ _ _ _).inv ≫
      (πCompMap D f).hom ▷ D.map g.toLoc ≫ (πCompMap D g).hom := by
  ext X x
  -- As for `πCompMap_id`, for the associator of `Cat`.
  change (Fiber.iso x (f ≫ g)).hom =
    ((D.mapComp f.toLoc g.toLoc).hom.as.app X).toNatTrans.app (Fiber.obj x i) ≫ 𝟙 _ ≫
      ((D.map g.toLoc).app X).toFunctor.map (Fiber.iso x f).hom ≫ (Fiber.iso x g).hom
  refine (Fiber.iso_comp x f g).trans ?_
  rw [transitionCompIso_hom, Category.id_comp]
  -- The two sides differ by the eta-expansion `{ as := X.as }` of `X`.
  rfl

/-! ### The 2-universal property

A pseudo-cone over `D` with apex `K` (`limit.Cone D K`) is a family of strong transformations
`π i : K ⟶ D i` with invertible modifications `π i ≫ D(f) ≅ π j` compatible with the comparisons
of `D`; the projections of the pseudo-limit form one (`limit.cone D`). Every pseudo-cone factors
through the pseudo-limit (`lift`, with `liftCompπ` and `lift_whiskerLeft_πCompMap_hom`), and
every other such factorization is isomorphic to `lift` (`isoLift`). A
modification between two strong transformations into `limit D` is given by a family of
modifications between their composites with the projections, compatible with the `2`-cells
`πCompMap` (`homMk`, and `isoMk` for invertible ones), and is determined by these (`hom_ext`). -/

variable (D) in
/-- A pseudo-cone over the diagram `D` with apex `K`: strong transformations `π i : K ⟶ D i` with
invertible modifications `iso f : π i ≫ D(f) ≅ π j` for `f : i ⟶ j`, compatible with the unit and
composition comparisons of `D`. -/
structure Cone (K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z}) where
  /-- The leg at `i`. -/
  π (i : I) : K ⟶ D.obj (.mk i)
  /-- The `2`-cell along `f : i ⟶ j`. -/
  iso {i j : I} (f : i ⟶ j) : π i ≫ D.map f.toLoc ≅ π j
  iso_id (i : I) : (iso (𝟙 i)).hom = π i ◁ (D.mapId (.mk i)).hom ≫ (ρ_ (π i)).hom
  iso_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (iso (f ≫ g)).hom = π i ◁ (D.mapComp f.toLoc g.toLoc).hom ≫ (α_ _ _ _).inv ≫
      (iso f).hom ▷ D.map g.toLoc ≫ (iso g).hom

variable (D) in
/-- The pseudo-cone of the pseudo-limit, formed by its projections and the `2`-cells
`πCompMap D f`. -/
-- Exposed so that the `2`-cells of `cone D`, between its legs, are seen as those of `π D`.
@[expose, simps]
def cone : Cone D (limit D) where
  π := π D
  iso := πCompMap D
  iso_id := πCompMap_id
  iso_comp := πCompMap_comp

section lift

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z}} (c : Cone D K)

/-- The image under the legs of a pseudo-cone of an object `k` of `K` over `X`: the object of the
fiber of the pseudo-limit over `X` with components the images of `k` under the legs, and with
transition isomorphisms the components of the `2`-cells of the cone. -/
-- Exposed, as are `liftApp` and `lift`, so that the components of `lift c` are seen in the
-- statements of its lemmas as the images under the legs of `c`.
@[expose, simps]
def liftObj {X : LocallyDiscrete Cᵒᵖ} (k : K.obj X) : Fiber D X.as where
  obj i := ((c.π i).app X).toFunctor.obj k
  iso f :=
    { hom := ((c.iso f).hom.as.app X).toNatTrans.app k
      inv := ((c.iso f).inv.as.app X).toNatTrans.app k
      hom_inv_id := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) (c.iso f).hom_inv_id
      inv_hom_id := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) (c.iso f).inv_hom_id }
  iso_id i := by
    have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) (c.iso_id i)
    rw [transitionIdIso_hom]
    -- The right unitor of `Cat` contributes an identity, which agrees with the identity below
    -- only definitionally.
    exact h.trans (Category.comp_id _)
  iso_comp f g := by
    have h := congrArg (fun m ↦ (m.as.app X).toNatTrans.app k) (c.iso_comp f g)
    rw [transitionCompIso_hom]
    -- As for `iso_id`, for the associator of `Cat`.
    exact h.trans (congrArg (_ ≫ ·) (Category.id_comp _))

/-- The component over `X` of `lift c`. -/
@[expose, simps]
def liftApp (X : LocallyDiscrete Cᵒᵖ) : K.obj X ⥤ Fiber D X.as where
  obj := liftObj c
  map φ :=
    { hom i := ((c.π i).app X).toFunctor.map φ
      comm f := ((c.iso f).hom.as.app X).toNatTrans.naturality φ }
  map_id _ := Fiber.hom_ext fun _ ↦ Functor.map_id _ _
  map_comp _ _ := Fiber.hom_ext fun _ ↦ Functor.map_comp _ _ _

/-- The naturality isomorphism of `lift c` at `g`, with components those of the legs of `c`. -/
def liftNaturality {X Y : LocallyDiscrete Cᵒᵖ} (g : X ⟶ Y) :
    (K.map g).toFunctor ⋙ liftApp c Y ≅ liftApp c X ⋙ map D g.as :=
  NatIso.ofComponents
    (fun k ↦ Fiber.isoMk (fun i ↦ (Cat.Hom.toNatIso ((c.π i).naturality g)).app k)
      (fun i j f ↦ by
        have h := Pseudofunctor.StrongTrans.Modification.naturality_app (c.iso f).hom.as g k
        rw [Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
        exact (Category.assoc _ _ _).symm.trans h.symm))
    (fun φ ↦ Fiber.hom_ext fun i ↦ ((c.π i).naturality g).hom.toNatTrans.naturality φ)

@[simp]
lemma liftNaturality_hom_app_hom {X Y : LocallyDiscrete Cᵒᵖ} (g : X ⟶ Y) (k : K.obj X) (i : I) :
    ((liftNaturality c g).hom.app k).hom i = ((c.π i).naturality g).hom.toNatTrans.app k :=
  (rfl)

@[simp]
lemma liftNaturality_inv_app_hom {X Y : LocallyDiscrete Cᵒᵖ} (g : X ⟶ Y) (k : K.obj X) (i : I) :
    ((liftNaturality c g).inv.app k).hom i = ((c.π i).naturality g).inv.toNatTrans.app k :=
  (rfl)

/-- The strong transformation `K ⟶ limit D` induced by a pseudo-cone `c` over `D` with apex
`K`. -/
@[expose]
def lift : K ⟶ limit D where
  app X := (liftApp c X).toCatHom
  naturality g := Cat.Hom.isoMk (liftNaturality c g)
  naturality_naturality η := Pseudofunctor.naturality_naturality_of_locallyDiscrete K (limit D)
    (fun X ↦ (liftApp c X).toCatHom) (fun g ↦ Cat.Hom.isoMk (liftNaturality c g)) η
  -- The comparisons of the pseudo-limit are by construction those of the `D i`, the unitors and
  -- associators of `Cat` have identity components, and all of these agree with the components
  -- of the corresponding cells of the legs of `c` only definitionally.
  naturality_id X := by
    ext k
    refine Fiber.hom_ext fun i ↦ ?_
    change ((c.π i).naturality (𝟙 X)).hom.toNatTrans.app k ≫
        ((D.obj (.mk i)).mapId' (𝟙 X) rfl).hom.toNatTrans.app
          (((c.π i).app X).toFunctor.obj k) =
      ((c.π i).app X).toFunctor.map ((K.mapId X).hom.toNatTrans.app k) ≫ 𝟙 _ ≫ 𝟙 _
    have h : ((D.obj (.mk i)).mapId' (𝟙 X) rfl).hom.toNatTrans.app
          (((c.π i).app X).toFunctor.obj k) =
        ((D.obj (.mk i)).mapId X).hom.toNatTrans.app (((c.π i).app X).toFunctor.obj k) := by
      rw [Pseudofunctor.mapId'_eq_mapId]
    exact (congrArg (((c.π i).naturality (𝟙 X)).hom.toNatTrans.app k ≫ ·) h).trans
      (congrArg (fun m ↦ m.toNatTrans.app k) ((c.π i).naturality_id X))
  naturality_comp {X Y Z} f g := by
    ext k
    refine Fiber.hom_ext fun i ↦ ?_
    change ((c.π i).naturality (f ≫ g)).hom.toNatTrans.app k ≫
        ((D.obj (.mk i)).mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app
          (((c.π i).app X).toFunctor.obj k) =
      ((c.π i).app Z).toFunctor.map ((K.mapComp f g).hom.toNatTrans.app k) ≫ 𝟙 _ ≫
        ((c.π i).naturality g).hom.toNatTrans.app ((K.map f).toFunctor.obj k) ≫ 𝟙 _ ≫
          ((D.obj (.mk i)).map g).toFunctor.map (((c.π i).naturality f).hom.toNatTrans.app k) ≫
            𝟙 _
    have h : ((D.obj (.mk i)).mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app
          (((c.π i).app X).toFunctor.obj k) =
        ((D.obj (.mk i)).mapComp f g).hom.toNatTrans.app (((c.π i).app X).toFunctor.obj k) := by
      rw [Pseudofunctor.mapComp'_eq_mapComp]
    exact (congrArg (((c.π i).naturality (f ≫ g)).hom.toNatTrans.app k ≫ ·) h).trans
      (congrArg (fun m ↦ m.toNatTrans.app k) ((c.π i).naturality_comp f g))

@[simp]
lemma lift_app_toFunctor (X : LocallyDiscrete Cᵒᵖ) :
    ((lift c).app X).toFunctor = liftApp c X :=
  rfl

/-- The naturality isomorphisms of `lift c` have the naturality isomorphisms of the legs of `c`
as components. -/
@[simp]
lemma lift_naturality_hom_app_hom {X Y : LocallyDiscrete Cᵒᵖ} (g : X ⟶ Y) (k : K.obj X) (i : I) :
    Fiber.Hom.hom (((lift c).naturality g).hom.toNatTrans.app k) i =
      ((c.π i).naturality g).hom.toNatTrans.app k :=
  (rfl)

/-- The naturality isomorphisms of `lift c` have the naturality isomorphisms of the legs of `c`
as components. -/
@[simp]
lemma lift_naturality_inv_app_hom {X Y : LocallyDiscrete Cᵒᵖ} (g : X ⟶ Y) (k : K.obj X) (i : I) :
    Fiber.Hom.hom (((lift c).naturality g).inv.toNatTrans.app k) i =
      ((c.π i).naturality g).inv.toNatTrans.app k :=
  (rfl)

/-- The `i`-th projection of `lift c` is the leg `c.π i`. -/
def liftCompπ (i : I) : lift c ≫ π D i ≅ c.π i :=
  Pseudofunctor.StrongTrans.isoMk (fun X ↦ Iso.refl ((c.π i).app X)) (fun g ↦ by
    ext k
    -- The components `Iso.refl ((c.π i).app X)` have source `(lift c ≫ π D i).app X`, which is
    -- `(c.π i).app X` only definitionally, so `change` states the goal with the components
    -- evaluated: the naturality of `c.π i` at `k`, and identities from the naturality of `π D i`,
    -- the associators of `Cat` and the `Iso.refl`s.
    change 𝟙 _ ≫ ((c.π i).naturality g).hom.toNatTrans.app k =
      (𝟙 _ ≫ ((c.π i).naturality g).hom.toNatTrans.app k ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
        ((D.obj (.mk i)).map g).toFunctor.map (𝟙 _)
    simp)

@[simp]
lemma liftCompπ_hom_as_app (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    (liftCompπ c i).hom.as.app X = 𝟙 _ :=
  (rfl)

@[simp]
lemma liftCompπ_inv_as_app (i : I) (X : LocallyDiscrete Cᵒᵖ) :
    (liftCompπ c i).inv.as.app X = 𝟙 _ :=
  (rfl)

/-- Under the isomorphisms `liftCompπ`, the `2`-cells of the pseudo-limit whiskered by `lift c`
are the `2`-cells of the pseudo-cone `c`. -/
lemma lift_whiskerLeft_πCompMap_hom {i j : I} (f : i ⟶ j) :
    lift c ◁ (πCompMap D f).hom = (α_ _ _ _).inv ≫ (liftCompπ c i).hom ▷ D.map f.toLoc ≫
      (c.iso f).hom ≫ (liftCompπ c j).inv := by
  ext X k
  -- As in `liftCompπ`, both sides are evaluated by `change`: the components of `liftCompπ` and
  -- of the associators of `Cat` are identities only definitionally.
  change ((c.iso f).hom.as.app X).toNatTrans.app k =
    𝟙 _ ≫ ((D.map f.toLoc).app X).toFunctor.map (𝟙 _) ≫
      ((c.iso f).hom.as.app X).toNatTrans.app k ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end lift

section homMk

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z}} {φ ψ : K ⟶ limit D}

/-- The components of a modification `φ ≫ π D i ⟶ ψ ≫ π D i` are natural with respect to the
naturality isomorphisms of `φ` and `ψ`, on `i`-th components. -/
private lemma naturality_hom {i : I} (m : φ ≫ π D i ⟶ ψ ≫ π D i) {X Y : LocallyDiscrete Cᵒᵖ}
    (g : X ⟶ Y) (k : K.obj X) :
    (m.as.app Y).toNatTrans.app ((K.map g).toFunctor.obj k) ≫
        Fiber.Hom.hom ((ψ.naturality g).hom.toNatTrans.app k) i =
      Fiber.Hom.hom ((φ.naturality g).hom.toNatTrans.app k) i ≫
        ((D.obj (.mk i)).map g).toFunctor.map ((m.as.app X).toNatTrans.app k) := by
  have h := Pseudofunctor.StrongTrans.Modification.naturality_app m.as g k
  rw [Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app] at h
  -- The naturality isomorphisms of `π D i` are identities.
  have h' : (m.as.app Y).toNatTrans.app ((K.map g).toFunctor.obj k) ≫
      Fiber.Hom.hom ((ψ.naturality g).hom.toNatTrans.app k) i ≫ 𝟙 _ =
        (Fiber.Hom.hom ((φ.naturality g).hom.toNatTrans.app k) i ≫ 𝟙 _) ≫
          ((D.obj (.mk i)).map g).toFunctor.map ((m.as.app X).toNatTrans.app k) := h
  exact ((congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans h').trans
    (congrArg (· ≫ _) (Category.comp_id _))

/-- The compatibility condition of `homMk` on objects: the components of a family of
modifications compatible with the `2`-cells of the pseudo-limit commute with the transition
isomorphisms. -/
private lemma comm_hom (m : ∀ i, φ ≫ π D i ⟶ ψ ≫ π D i)
    (hm : ∀ ⦃i j : I⦄ (f : i ⟶ j), m i ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫
      ψ ◁ (πCompMap D f).hom = (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ m j)
    (X : LocallyDiscrete Cᵒᵖ) (k : K.obj X) {i j : I} (f : i ⟶ j) :
    (transition D f X.as).map (((m i).as.app X).toNatTrans.app k) ≫
        (Fiber.iso ((ψ.app X).toFunctor.obj k) f).hom =
      (Fiber.iso ((φ.app X).toFunctor.obj k) f).hom ≫ ((m j).as.app X).toNatTrans.app k := by
  have h := congrArg (fun n ↦ (n.as.app X).toNatTrans.app k) (hm f)
  -- The associators of `Cat` have identity components, which agree with the identities below
  -- only definitionally.
  have h' : (transition D f X.as).map (((m i).as.app X).toNatTrans.app k) ≫ 𝟙 _ ≫
      (Fiber.iso ((ψ.app X).toFunctor.obj k) f).hom =
        𝟙 _ ≫ (Fiber.iso ((φ.app X).toFunctor.obj k) f).hom ≫
          ((m j).as.app X).toNatTrans.app k := h
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).symm.trans (h'.trans (Category.id_comp _))

/-- A modification `φ ⟶ ψ` between strong transformations into the pseudo-limit, from a family
of modifications `m i : φ ≫ π D i ⟶ ψ ≫ π D i` compatible with the `2`-cells `πCompMap D f`. -/
def homMk (m : ∀ i, φ ≫ π D i ⟶ ψ ≫ π D i)
    (hm : ∀ ⦃i j : I⦄ (f : i ⟶ j), m i ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫
      ψ ◁ (πCompMap D f).hom = (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ m j) :
    φ ⟶ ψ where
  as.app X := Cat.Hom₂.ofNatTrans
    { app k :=
        { hom i := ((m i).as.app X).toNatTrans.app k
          comm f := by exact comm_hom m hm X k f }
      naturality _ _ u := Fiber.hom_ext fun i ↦ ((m i).as.app X).toNatTrans.naturality u }
  as.naturality g := by
    ext k
    exact Fiber.hom_ext fun i ↦ naturality_hom (m i) g k

variable (m : ∀ i, φ ≫ π D i ⟶ ψ ≫ π D i)
  (hm : ∀ ⦃i j : I⦄ (f : i ⟶ j), m i ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫
    ψ ◁ (πCompMap D f).hom = (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ m j)

/-- The components of `homMk m hm` are those of the `m i`. -/
@[simp]
lemma homMk_as_app_app_hom (X : LocallyDiscrete Cᵒᵖ) (k : K.obj X) (i : I) :
    Fiber.Hom.hom (((homMk m hm).as.app X).toNatTrans.app k) i =
      ((m i).as.app X).toNatTrans.app k :=
  (rfl)

/-- The `i`-th projection of `homMk m hm` is `m i`. -/
@[simp]
lemma homMk_whiskerRight_π (i : I) : homMk m hm ▷ π D i = m i := by
  ext X k
  rw [Pseudofunctor.StrongTrans.whiskerRight_as_app]
  rfl

/-- Two modifications into the pseudo-limit agree when their composites with all projections
do. -/
lemma hom_ext {n n' : φ ⟶ ψ} (h : ∀ i, n ▷ π D i = n' ▷ π D i) : n = n' := by
  ext X k
  refine Fiber.hom_ext fun i ↦ ?_
  have h := congrArg (fun n ↦ (n.as.app X).toNatTrans.app k) (h i)
  simp only [Pseudofunctor.StrongTrans.whiskerRight_as_app] at h
  exact h

/-- The composites of a modification into the pseudo-limit with the projections are compatible
with the `2`-cells `πCompMap D f`: this is the condition of `homMk`. -/
lemma whiskerRight_π_comp_whiskerLeft_πCompMap (n : φ ⟶ ψ) {i j : I} (f : i ⟶ j) :
    (n ▷ π D i) ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫ ψ ◁ (πCompMap D f).hom =
      (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ n ▷ π D j := by
  ext X k
  -- The associators of `Cat` have identity components, which agree with the identities below
  -- only definitionally.
  change (transition D f X.as).map (Fiber.Hom.hom ((n.as.app X).toNatTrans.app k) i) ≫ 𝟙 _ ≫
      (Fiber.iso ((ψ.app X).toFunctor.obj k) f).hom =
    𝟙 _ ≫ (Fiber.iso ((φ.app X).toFunctor.obj k) f).hom ≫
      Fiber.Hom.hom ((n.as.app X).toNatTrans.app k) j
  simpa using ((n.as.app X).toNatTrans.app k).comm f

/-- An isomorphism `φ ≅ ψ` between strong transformations into the pseudo-limit, from a family
of isomorphisms `e i : φ ≫ π D i ≅ ψ ≫ π D i` compatible with the `2`-cells `πCompMap D f`. -/
def isoMk (e : ∀ i, φ ≫ π D i ≅ ψ ≫ π D i)
    (he : ∀ ⦃i j : I⦄ (f : i ⟶ j), (e i).hom ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫
      ψ ◁ (πCompMap D f).hom = (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ (e j).hom) :
    φ ≅ ψ where
  hom := homMk (fun i ↦ (e i).hom) he
  inv := homMk (fun i ↦ (e i).inv) fun i j f ↦ by
    rw [← cancel_epi ((e i).hom ▷ D.map f.toLoc), ← comp_whiskerRight_assoc, Iso.hom_inv_id,
      id_whiskerRight, Category.id_comp, reassoc_of% (he f)]
    simp
  hom_inv_id := hom_ext fun i ↦ by simp
  inv_hom_id := hom_ext fun i ↦ by simp

section isoMk

variable (e : ∀ i, φ ≫ π D i ≅ ψ ≫ π D i)
  (he : ∀ ⦃i j : I⦄ (f : i ⟶ j), (e i).hom ▷ D.map f.toLoc ≫ (α_ _ _ _).hom ≫
    ψ ◁ (πCompMap D f).hom = (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ (e j).hom)

lemma isoMk_hom : (isoMk e he).hom = homMk (fun i ↦ (e i).hom) he :=
  (rfl)

/-- The `i`-th projection of `(isoMk e he).hom` is `(e i).hom`. -/
@[simp]
lemma isoMk_hom_whiskerRight_π (i : I) : (isoMk e he).hom ▷ π D i = (e i).hom :=
  homMk_whiskerRight_π _ he i

/-- The `i`-th projection of `(isoMk e he).inv` is `(e i).inv`. -/
@[simp]
lemma isoMk_inv_whiskerRight_π (i : I) : (isoMk e he).inv ▷ π D i = (e i).inv := by
  ext X k
  rw [Pseudofunctor.StrongTrans.whiskerRight_as_app]
  rfl

end isoMk

end homMk

section isoLift

variable {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z}} (c : Cone D K)
  {φ : K ⟶ limit D} (e : ∀ i, φ ≫ π D i ≅ c.π i)
  (he : ∀ ⦃i j : I⦄ (f : i ⟶ j), (e i).hom ▷ D.map f.toLoc ≫ (c.iso f).hom =
    (α_ _ _ _).hom ≫ φ ◁ (πCompMap D f).hom ≫ (e j).hom)

/-- A strong transformation `φ : K ⟶ limit D` whose composites with the projections are
identified with the legs of a pseudo-cone `c`, compatibly with the `2`-cells, is isomorphic to
`lift c`. By `hom_ext`, this isomorphism is the only one whose projections are the given
isomorphisms followed by `liftCompπ` (`isoLift_hom_whiskerRight_π`). -/
def isoLift : φ ≅ lift c :=
  isoMk (fun i ↦ e i ≪≫ (liftCompπ c i).symm) fun i j f ↦ by
    simp [lift_whiskerLeft_πCompMap_hom, reassoc_of% (he f)]

/-- The `i`-th projection of `(isoLift c e he).hom` is `(e i).hom` followed by the inverse of
`liftCompπ c i`. -/
@[simp]
lemma isoLift_hom_whiskerRight_π (i : I) :
    (isoLift c e he).hom ▷ π D i = (e i).hom ≫ (liftCompπ c i).inv :=
  isoMk_hom_whiskerRight_π _ _ i

/-- The `i`-th projection of `(isoLift c e he).inv` is `liftCompπ c i` followed by the inverse of
`e i`. -/
@[simp]
lemma isoLift_inv_whiskerRight_π (i : I) :
    (isoLift c e he).inv ▷ π D i = (liftCompπ c i).hom ≫ (e i).inv :=
  isoMk_inv_whiskerRight_π _ _ i

end isoLift

end limit

end TauCeti.Stack

end
