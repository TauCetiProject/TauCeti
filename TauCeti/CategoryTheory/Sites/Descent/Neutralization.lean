/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Neutralizations of a pseudofunctor

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `S` an object of `C`. A
neutralization of `F` over `S` is an object of the fibre of `F` over `S`; neutralizations over
`S` form a category, equivalent to that fibre, and a groupoid when `F` is a gerbe. A
neutralization over `S` pulls back to a neutralization over every `V` with an arrow `V ⟶ S`.

When `S` is a terminal object of `C`, `F` is neutral if it has a neutralization over `S` (Olsson,
Remark 31.5); for an `A`-gerbe this is the condition under which it is equivalent to the
classifying stack of `A`-torsors. This file shows that a neutral pseudofunctor has objects over
every object of `C`, and that neutrality does not depend on the chosen terminal object. A
neutralization over an object that is not terminal only gives objects over the objects of `C`
with an arrow to it.

Neutralizations are compatible with restriction to a slice: the neutralizations of the
restriction `F.over U` over `V : Over U` are those of `F` over `V.left`, compatibly with pullback.
Since `Over U` has the terminal object `Over.mk (𝟙 U)`, `F.over U` is neutral exactly when the
fibre of `F` over `U` is nonempty: an object over an arbitrary object `U` of `C` is a
neutralization of `F` on the slice over `U`, and a neutral `F` restricts to a neutral `F.over U`.

## Main declarations

* `CategoryTheory.Pseudofunctor.Neutralization`: the neutralizations of `F` over `S`.
* `CategoryTheory.Pseudofunctor.Neutralization.equivFiber`: neutralizations over `S` are
  equivalent to the fibre of `F` over `S`.
* `CategoryTheory.Pseudofunctor.Neutralization.pullback`: the pullback of a neutralization along an
  arrow `V ⟶ S`.
* `CategoryTheory.Pseudofunctor.IsNeutral`: the property of having a neutralization over a
  terminal object.
* `CategoryTheory.Pseudofunctor.IsNeutral.nonempty_obj`: a neutral pseudofunctor has objects over
  every object of `C`.
* `CategoryTheory.Pseudofunctor.isNeutral_iff_of_isTerminal`: neutrality does not depend on the
  terminal object.
* `CategoryTheory.Pseudofunctor.Neutralization.overEquiv`: neutralizations of `F.over U` over
  `V : Over U` are equivalent to neutralizations of `F` over `V.left`.
* `CategoryTheory.Pseudofunctor.isNeutral_over_iff`: `F.over U` is neutral if and only if the
  fibre of `F` over `U` is nonempty.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Remark 31.5
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory Limits

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- A neutralization of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` over an object `S` of
`C`: an object of the fibre of `F` over `S`. Its morphisms are the morphisms of the fibre. -/
@[ext]
structure Neutralization (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (S : C) where
  /-- The object of the fibre over `S`. -/
  obj : F.obj (.mk (op S))

namespace Neutralization

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {S : C}

instance : Category.{v'} (Neutralization F S) :=
  inferInstanceAs (Category (InducedCategory (F.obj (.mk (op S))) obj))

instance [IsGroupoid (F.obj (.mk (op S)))] : IsGroupoid (Neutralization F S) :=
  inferInstanceAs (IsGroupoid (InducedCategory (F.obj (.mk (op S))) obj))

@[ext]
lemma hom_ext {x y : Neutralization F S} {f g : x ⟶ y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

@[simp]
lemma id_hom (x : Neutralization F S) : (𝟙 x : x ⟶ x).hom = 𝟙 x.obj :=
  rfl

@[simp, reassoc]
lemma comp_hom {x y z : Neutralization F S} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- A morphism of neutralizations from a morphism of the underlying objects. -/
abbrev homMk {x y : Neutralization F S} (f : x.obj ⟶ y.obj) : x ⟶ y :=
  InducedCategory.homMk f

@[simp]
lemma homMk_hom {x y : Neutralization F S} (f : x.obj ⟶ y.obj) : (homMk f).hom = f :=
  rfl

/-- An isomorphism of neutralizations from an isomorphism of the underlying objects. -/
abbrev isoMk {x y : Neutralization F S} (e : x.obj ≅ y.obj) : x ≅ y :=
  InducedCategory.isoMk e

variable (F S) in
/-- Neutralizations of `F` over `S` are equivalent to the fibre of `F` over `S`. Its body is
exposed because the statements of its `simps` lemmas need its functors to reduce on objects. -/
@[expose, simps]
def equivFiber : Neutralization F S ≌ F.obj (.mk (op S)) where
  functor.obj x := x.obj
  functor.map f := f.hom
  inverse.obj x := ⟨x⟩
  inverse.map f := homMk f
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by simp

variable {V W : C}

/-- The pullback of a neutralization over `S` along an arrow `f : V ⟶ S`. Its body is exposed
because the statements of the characterization lemmas of `pullbackId` and `pullbackComp` need
`(pullback f x).obj` to reduce to `(F.map f.op.toLoc).toFunctor.obj x.obj`. -/
@[expose] def pullback (f : V ⟶ S) (x : Neutralization F S) : Neutralization F V :=
  ⟨(F.map f.op.toLoc).toFunctor.obj x.obj⟩

@[simp]
lemma pullback_obj (f : V ⟶ S) (x : Neutralization F S) :
    (pullback f x).obj = (F.map f.op.toLoc).toFunctor.obj x.obj :=
  (rfl)

/-- The pullback of neutralizations along an arrow `f : V ⟶ S`, as a functor. Its body is
exposed because the statement of `pullbackFunctor_map_hom` needs it to reduce on objects. -/
@[expose] def pullbackFunctor (f : V ⟶ S) : Neutralization F S ⥤ Neutralization F V where
  obj := pullback f
  map g := homMk ((F.map f.op.toLoc).toFunctor.map g.hom)
  map_id x := by ext; exact Functor.map_id _ _
  map_comp g g' := by ext; exact Functor.map_comp _ _ _

@[simp]
lemma pullbackFunctor_obj (f : V ⟶ S) (x : Neutralization F S) :
    (pullbackFunctor f).obj x = pullback f x :=
  (rfl)

@[simp]
lemma pullbackFunctor_map_hom (f : V ⟶ S) {x y : Neutralization F S} (g : x ⟶ y) :
    ((pullbackFunctor f).map g).hom = (F.map f.op.toLoc).toFunctor.map g.hom :=
  (rfl)

/-- The pullback of a neutralization along the identity is isomorphic to it. -/
def pullbackId (x : Neutralization F S) : pullback (𝟙 S) x ≅ x :=
  isoMk ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).app x.obj)

@[simp]
lemma pullbackId_hom_hom (x : Neutralization F S) :
    (pullbackId x).hom.hom = (F.mapId (.mk (op S))).hom.toNatTrans.app x.obj :=
  (rfl)

@[simp]
lemma pullbackId_inv_hom (x : Neutralization F S) :
    (pullbackId x).inv.hom = (F.mapId (.mk (op S))).inv.toNatTrans.app x.obj :=
  (rfl)

/-- The pullback of a neutralization along a composite `g ≫ f` is isomorphic to the pullback along
`g` of its pullback along `f`. -/
def pullbackComp (f : V ⟶ S) (g : W ⟶ V) (x : Neutralization F S) :
    pullback (g ≫ f) x ≅ pullback g (pullback f x) :=
  isoMk ((Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).app x.obj)

@[simp]
lemma pullbackComp_hom_hom (f : V ⟶ S) (g : W ⟶ V) (x : Neutralization F S) :
    (pullbackComp f g x).hom.hom = (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app x.obj :=
  (rfl)

@[simp]
lemma pullbackComp_inv_hom (f : V ⟶ S) (g : W ⟶ V) (x : Neutralization F S) :
    (pullbackComp f g x).inv.hom = (F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app x.obj :=
  (rfl)

section Over

variable {U : C}

/-- Neutralizations of the restriction `F.over U` over an object `V` of `Over U` are equivalent to
neutralizations of `F` over `V.left`: both are objects of the fibre of `F` over `V.left`, and the
functors keep the objects and the morphisms. Its body is exposed because the statements of its
`simps` lemmas need its functors to reduce on objects. -/
@[expose, simps! functor_obj_obj inverse_obj_obj functor_map_hom inverse_map_hom]
def overEquiv (V : Over U) : Neutralization (F.over U) V ≌ Neutralization F V.left :=
  (equivFiber (F.over U) V).trans (equivFiber F V.left).symm

/-- The equivalence `overEquiv` is compatible with pullback: pulling back a neutralization of
`F.over U` along a morphism `g` of `Over U` corresponds to pulling back along `g.left`. -/
@[simp]
lemma overEquiv_functor_obj_pullback {V W : Over U} (g : W ⟶ V)
    (x : Neutralization (F.over U) V) :
    (overEquiv W).functor.obj (pullback g x) = pullback g.left ((overEquiv V).functor.obj x) :=
  (rfl)

end Over

end Neutralization

/-- A pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` is neutral, relative to a terminal object `S`
of `C` with terminality witness `hS`, if it has a neutralization over `S` (Olsson, Remark 31.5). -/
structure IsNeutral (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (S : C) (hS : IsTerminal S) :
    Prop where
  /-- There is a neutralization over the terminal object. -/
  nonempty : Nonempty (Neutralization F S)

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {S : C} {hS : IsTerminal S}

/-- `F` is neutral if and only if its fibre over the terminal object is nonempty. -/
lemma isNeutral_iff : IsNeutral F S hS ↔ Nonempty (F.obj (.mk (op S))) :=
  ⟨fun ⟨⟨x⟩⟩ ↦ ⟨x.obj⟩, fun ⟨x⟩ ↦ ⟨⟨⟨x⟩⟩⟩⟩

/-- A neutral pseudofunctor has an object over every object of `C`, the pullback of a
neutralization along the arrow to the terminal object. -/
lemma IsNeutral.nonempty_obj (h : IsNeutral F S hS) (U : C) : Nonempty (F.obj (.mk (op U))) :=
  h.nonempty.map fun x ↦ (x.pullback (hS.from U)).obj

/-- Neutrality relative to one terminal object implies neutrality relative to any other. -/
lemma IsNeutral.of_isTerminal (h : IsNeutral F S hS) {S' : C} (hS' : IsTerminal S') :
    IsNeutral F S' hS' :=
  isNeutral_iff.2 (h.nonempty_obj S')

/-- Neutrality does not depend on the terminal object. -/
lemma isNeutral_iff_of_isTerminal {S' : C} (hS' : IsTerminal S') :
    IsNeutral F S hS ↔ IsNeutral F S' hS' :=
  ⟨fun h ↦ h.of_isTerminal hS', fun h ↦ h.of_isTerminal hS⟩

/-- The restriction `F.over U` of `F` to the slice over `U` is neutral, relative to any terminal
object of `Over U`, if and only if the fibre of `F` over `U` is nonempty. -/
lemma isNeutral_over_iff {U : C} {T : Over U} (hT : IsTerminal T) :
    IsNeutral (F.over U) T hT ↔ Nonempty (F.obj (.mk (op U))) := by
  rw [isNeutral_iff_of_isTerminal Over.mkIdTerminal, isNeutral_iff]
  -- The fibre of `F.over U` over `Over.mk (𝟙 U)` is the fibre of `F` over `U` by definition.
  exact Iff.rfl

/-- The restriction of a neutral pseudofunctor to any slice is neutral. -/
lemma IsNeutral.over (h : IsNeutral F S hS) (U : C) {T : Over U} (hT : IsTerminal T) :
    IsNeutral (F.over U) T hT :=
  (isNeutral_over_iff hT).2 (h.nonempty_obj U)

end CategoryTheory.Pseudofunctor
