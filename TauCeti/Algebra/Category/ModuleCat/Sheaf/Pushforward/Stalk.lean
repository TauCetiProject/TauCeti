/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Skyscraper

/-!
# Stalk maps of morphisms of ringed spaces and pushforwards of skyscrapers

A morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` is a continuous map `f : Y → X`
with a morphism of sheaves of rings `φ : 𝒪_X → f_* 𝒪_Y`. Following Mathlib's module pullback
`SheafOfModules.pullback φ` and pushforward `SheafOfModules.pushforward φ`, `φ` is a morphism from
`ringCatSheaf 𝒪_X` to the pushforward of `ringCatSheaf 𝒪_Y` along `Opens.map f`. This file
constructs the stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of `(f, φ)`, a morphism of commutative rings,
and computes it on germs; `TauCeti.SheafOfModules.stalkAlgebra` makes `𝒪_{Y,y}` an algebra over
`𝒪_{X,f(y)}` through it. Stalks of module pushforwards and pullbacks are compared along it.

For a point `y` of `Y` and an `𝒪_{Y,y}`-module `T`, the pushforward along `φ` of the skyscraper at
`y` with value `T` is the skyscraper at `f y` with value `T`, an `𝒪_{X,f(y)}`-module by restriction
of scalars along the stalk map (`TauCeti.SheafOfModules.pushforwardSkyscraperIso`). Together with
the adjunction between pullback and pushforward, this computes linear maps out of the stalks of a
pulled-back module.

## Main declarations

* `TauCeti.SheafOfModules.ringStalkMap`: the stalk map `𝒪_{X,f(y)} ⟶ 𝒪_{Y,y}` of `(f, φ)`,
  computed on germs by `TauCeti.SheafOfModules.ringStalkMap_germ`;
* `TauCeti.SheafOfModules.pushforwardSkyscraperIso`: `f_* (y_* T) ≅ (f y)_* T`.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))

/-- The stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of a morphism of ringed spaces `(f, φ)`: Mathlib's
stalk map `PresheafedSpace.Hom.stalkMap` of the morphism of presheafed spaces given by `f` and the
morphism of presheaves of commutative rings `commRingCatHom φ : 𝒪_X ⟶ f_* 𝒪_Y`. -/
def ringStalkMap (y : Y) :
    TopCat.Presheaf.stalk 𝒪X.obj (f y) ⟶ TopCat.Presheaf.stalk 𝒪Y.obj y :=
  AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
    (X := ⟨Y, 𝒪Y.obj⟩) (Y := ⟨X, 𝒪X.obj⟩) ⟨f, (commRingCatHom φ :)⟩ y

/-- The stalk map of `(f, φ)` sends the germ of `r` at `f y` to the germ of `φ r` at `y`. -/
@[simp]
theorem ringStalkMap_germ (y : Y) (U : Opens X) (hy : f y ∈ U) (r : 𝒪X.obj.obj (op U)) :
    ringStalkMap φ y (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) =
      TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r) :=
  AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply
    (X := ⟨Y, 𝒪Y.obj⟩) (Y := ⟨X, 𝒪X.obj⟩) ⟨f, (commRingCatHom φ :)⟩ U y hy r

/-- The stalk `𝒪_{Y,y}` as an algebra over `𝒪_{X,f(y)}` through the stalk map of `(f, φ)`. It
is not an instance, since `φ` cannot be found by instance search; statements over it introduce
it with `letI`. -/
abbrev stalkAlgebra (y : Y) :
    Algebra ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) :=
  (ringStalkMap φ y).hom.toAlgebra

section Pushforward

variable (y : Y) (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) T]
  [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) T]

/-- The pushforward along `(f, φ)` of the skyscraper at `y` with value `T` is the skyscraper at
`f y` with value `T`, for any `𝒪_{X,f(y)}`-module structure on `T` that is restriction of scalars
along the stalk map `ringStalkMap φ y`. On sections over `U` both sides are `T` when `f y ∈ U` and
`0` otherwise. -/
def pushforwardSkyscraperIso (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T),
      a • t = ringStalkMap φ y a • t) :
    (_root_.SheafOfModules.pushforward φ).obj (skyscraper 𝒪Y y T) ≅ skyscraper 𝒪X (f y) T :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (_root_.PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (R := (ringCatSheaf 𝒪X).obj.obj U)
      (X₁ := ((_root_.SheafOfModules.pushforward φ).obj (skyscraper 𝒪Y y T)).val.obj U)
      (m₁ := ModuleCat.isModule _)
      (X₂ := (skyscraper 𝒪X (f y) T).val.obj U) (m₂ := ModuleCat.isModule _)
      { toFun s p := s ⟨p.down⟩
        invFun s p := s ⟨p.down⟩
        map_add' _ _ := rfl
        map_smul' r s := funext fun p ↦ by
          refine (congrArg (· • s ⟨p.down⟩) (ringStalkMap_germ φ y U.unop p.down r).symm).trans ?_
          exact (hT _ _).symm
        left_inv _ := rfl
        right_inv _ := rfl }) (fun _ _ _ ↦ rfl))

/-- On sections, `pushforwardSkyscraperIso` is the identity of the values at `y`. -/
@[simp]
lemma pushforwardSkyscraperIso_hom_val_app_apply
    (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T), a • t = ringStalkMap φ y a • t)
    (U : (Opens X)ᵒᵖ)
    (s : (skyscraper 𝒪Y y T).val.obj (op ((Opens.map f).obj U.unop))) (p : PLift (f y ∈ U.unop)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      skyscraper_val]
    ((pushforwardSkyscraperIso φ y T hT).hom.val.app U s p = s ⟨p.down⟩) :=
  (rfl)

/-- On sections, the inverse of `pushforwardSkyscraperIso` is the identity of the values at `y`. -/
@[simp]
lemma pushforwardSkyscraperIso_inv_val_app_apply
    (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T), a • t = ringStalkMap φ y a • t)
    (U : (Opens X)ᵒᵖ) (s : (skyscraper 𝒪X (f y) T).val.obj U)
    (p : PLift (y ∈ (Opens.map f).obj U.unop)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      skyscraper_val]
    ((pushforwardSkyscraperIso φ y T hT).inv.val.app U s p = s ⟨p.down⟩) :=
  (rfl)

end Pushforward

end SheafOfModules

end

end TauCeti
