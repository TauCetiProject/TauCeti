/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Topology.Category.TopCat.EpiMono
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Morphisms of presheafed spaces determined by sections

Two morphisms `α β : X ⟶ Y` of presheafed spaces with the same underlying continuous map agree
once their maps on sections `Γ(Y, U) ⟶ Γ(X, α⁻¹ U)` and `Γ(Y, U) ⟶ Γ(X, β⁻¹ U)` agree up to the
identification `α⁻¹ U = β⁻¹ U`. This is the presheafed-space form of Mathlib's
`AlgebraicGeometry.Scheme.Hom.ext`, and is convenient when a morphism of presheafed spaces is
built by hand before its locality on stalks is known, so that it is not yet a morphism of
locally ringed spaces or of schemes.

For an open `V ≤ f⁻¹ U`, `AlgebraicGeometry.PresheafedSpace.Hom.appLE` packages the restricted
section map `Γ(Y, U) ⟶ Γ(X, V)` obtained by composing `f.c.app (op U)` with the presheaf
restriction on `X`, avoiding `eqToHom` transports on open preimages.

A morphism `f : X ⟶ Y` of presheafed spaces which is surjective on points and whose maps on sections
`Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` are all monomorphisms is an epimorphism: two morphisms out of `Y` which
agree after composing with `f` agree on points because `f` is surjective, and then on sections
because the maps on sections of `f` can be cancelled. This is the sectionwise analogue of
Mathlib's `AlgebraicGeometry.SheafedSpace.epi_of_base_surjective_of_stalk_mono`, and applies when
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.Hom.appLE`: restricted section map `Γ(Y, U) ⟶ Γ(X, V)` for
  `V ≤ f⁻¹ U`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.ext_of_app`: morphisms of presheafed spaces agreeing on the
  underlying map and on sections over every open are equal.
* `AlgebraicGeometry.PresheafedSpace.comp_c_app_apply`: on sections in a concrete category, the
  section map of a composite morphism of presheafed spaces is the composite of the section maps.
* `AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`: a morphism which is
  surjective on points and a monomorphism on sections over every open is an epimorphism.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.PresheafedSpace

universe w v u

section

variable {C : Type u} [Category.{v} C] {X Y : PresheafedSpace.{_, _, w} C}

/-- Two morphisms of presheafed spaces are equal if they have the same underlying continuous map
and the same maps on sections over every open subset, up to the induced identification of
preimages. -/
theorem ext_of_app {α β : X ⟶ Y} (w : α.base = β.base)
    (h : ∀ U, α.c.app (op U) ≫ X.presheaf.map (eqToHom congr((Opens.map $w.symm).obj U)).op =
      β.c.app (op U)) : α = β :=
  PresheafedSpace.ext α β w <| TopCat.Presheaf.ext fun U ↦ by simpa using h U

/-- On sections in a concrete category, the section map of a composite morphism of presheafed spaces
is the composite of the section maps. -/
theorem comp_c_app_apply {FC : C → C → Type*} {CC : C → Type*}
    [∀ R S, FunLike (FC R S) (CC R) (CC S)] [ConcreteCategory C FC]
    {Z : PresheafedSpace.{_, _, w} C} (α : X ⟶ Y) (β : Y ⟶ Z)
    (U : (Opens Z)ᵒᵖ) (s : ToType (Z.presheaf.obj U)) :
    (α ≫ β).c.app U s = α.c.app (op ((Opens.map β.base).obj U.unop)) (β.c.app U s) :=
  (ConcreteCategory.congr_hom (comp_c_app α β U) s).trans (ConcreteCategory.comp_apply _ _ s)

/-- **A morphism of presheafed spaces which is surjective on points and a monomorphism on
sections is an epimorphism.** -/
theorem epi_of_base_surjective_of_c_app_mono (f : X ⟶ Y) (h₁ : Function.Surjective f.base)
    (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  refine ⟨fun {Z} g g' e ↦ ?_⟩
  obtain ⟨gb, gc⟩ := g
  obtain ⟨gb', gc'⟩ := g'
  obtain rfl : gb = gb' := ((TopCat.epi_iff_surjective f.base).2 h₁).left_cancellation _ _
    congr(Hom.base $e)
  congr
  ext U
  rw [← cancel_mono (f.c.app _)]
  exact congr(NatTrans.app (Hom.c $e) (op U))

end

namespace Hom

variable {C : Type u} [Category.{v} C]

/-- Given a morphism of presheafed spaces `f : X ⟶ Y` and open sets `U : Opens Y`, `V : Opens X`
with `V ≤ f⁻¹ U`, this is the induced restriction map `Γ(Y, U) ⟶ Γ(X, V)` on sections. -/
def appLE {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (U : Opens Y) (V : Opens X)
    (e : V ≤ (Opens.map f.base).obj U) :
    Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op V) :=
  f.c.app (op U) ≫ X.presheaf.map (homOfLE e).op

/-- Unfolding rule for `PresheafedSpace.Hom.appLE`. -/
theorem appLE_def {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (U : Opens Y) (V : Opens X)
    (e : V ≤ (Opens.map f.base).obj U) :
    f.appLE U V e = f.c.app (op U) ≫ X.presheaf.map (homOfLE e).op := (rfl)

@[reassoc (attr := simp)]
theorem appLE_map {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) {U : Opens Y} {V V' : Opens X}
    (e : V ≤ (Opens.map f.base).obj U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e) :=
  (Category.assoc _ _ _).trans <|
    congrArg (f.c.app (op U) ≫ ·) (TopCat.Presheaf.map_comp_map_eq X.presheaf _ i _)

@[reassoc (attr := simp)]
theorem map_appLE {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) {U U' : Opens Y} {V : Opens X}
    (e : V ≤ (Opens.map f.base).obj U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) := by
  rw [appLE, ← Category.assoc, f.c.naturality i, Category.assoc]
  exact congrArg (f.c.app (op U') ≫ ·) (TopCat.Presheaf.map_comp_map_eq X.presheaf _ _ _)

theorem app_eq_appLE {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (U : Opens Y) :
    (f.c.app (op U) : Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op ((Opens.map f.base).obj U))) =
      f.appLE U ((Opens.map f.base).obj U) le_rfl := by
  simp [appLE]

@[simp]
theorem appLE_eq_app {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (U : Opens Y) :
    f.appLE U ((Opens.map f.base).obj U) le_rfl = f.c.app (op U) :=
  (app_eq_appLE f U).symm

@[simp]
theorem id_appLE (X : PresheafedSpace.{v, u, w} C) {U V : Opens X}
    (e : V ≤ (Opens.map (𝟙 X : X ⟶ X).base).obj U) :
    (𝟙 X : X ⟶ X).appLE U V e = X.presheaf.map (homOfLE e).op := by
  rw [appLE, id_c_app]
  exact TopCat.Presheaf.map_comp_map_eq X.presheaf _ _ _

@[reassoc]
theorem appLE_comp_appLE {X Y Z : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Opens Z) (V : Opens Y) (W : Opens X)
    (e₁ : V ≤ (Opens.map g.base).obj U) (e₂ : W ≤ (Opens.map f.base).obj V) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W
        ((e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le).trans
          (eqToHom (by rw [comp_base, Opens.map_comp_obj])).le) := by
  rw [appLE, appLE, appLE, comp_c_app, Category.assoc]
  refine (congrArg (g.c.app (op U) ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  rw [← Category.assoc, f.c.naturality]
  exact (Category.assoc _ _ _).trans <|
    congrArg (f.c.app _ ≫ ·) (TopCat.Presheaf.map_comp_map_eq X.presheaf _ _ _)

@[simp, reassoc]
theorem comp_appLE {X Y Z : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Opens Z) (W : Opens X) (e : W ≤ (Opens.map (f ≫ g).base).obj U) :
    (f ≫ g).appLE U W e =
      g.c.app (op U) ≫ f.appLE ((Opens.map g.base).obj U) W
        (e.trans (eqToHom (by rw [comp_base, Opens.map_comp_obj])).le) := by
  rw [appLE, appLE, comp_c_app]
  refine (Category.assoc _ _ _).trans (congrArg (g.c.app (op U) ≫ ·) ?_)
  exact congrArg (f.c.app _ ≫ X.presheaf.map ·) (Subsingleton.elim _ _)

theorem appLE_congr {X Y : PresheafedSpace.{v, u, w} C} (f : X ⟶ Y) {U U' : Opens Y}
    {V V' : Opens X} (e : V ≤ (Opens.map f.base).obj U) (hU : U = U') (hV : V = V')
    (P : ∀ {R S : C} (_ : R ⟶ S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (hU ▸ hV ▸ e)) := by
  subst hU; subst hV; rfl

theorem congr_appLE {X Y : PresheafedSpace.{v, u, w} C} {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
    {U : Opens Y} {V : Opens X}
    (h₁ : V ≤ (Opens.map k₁.base).obj U) (h₂ : V ≤ (Opens.map k₂.base).obj U) :
    k₁.appLE U V h₁ = k₂.appLE U V h₂ := by
  subst hk; rfl

end Hom

end AlgebraicGeometry.PresheafedSpace
