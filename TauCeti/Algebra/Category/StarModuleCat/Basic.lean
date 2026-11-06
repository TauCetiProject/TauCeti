/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Star.Module

/-!
# Modules with a compatible additive involution

`TauCeti.StarModuleCat R` bundles the native `StarAddMonoid` and `StarModule R`
structures. Its morphisms are linear maps commuting with star, and its faithful
forgetful functor takes values in `ModuleCat R`. For `R = ℂ`, these are complex
modules with conjugation, the natural category for descent to real modules.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- Modules with an additive involution compatible with the scalar involution.
Morphisms are linear maps preserving that involution. -/
structure StarModuleCat (R : Type*) [Ring R] [StarRing R] where
  /-- The underlying module. -/
  toModuleCat : ModuleCat.{u} R
  /-- The additive involution on the module. -/
  starAddMonoid : StarAddMonoid toModuleCat
  /-- Compatibility of the two involutions with scalar multiplication. -/
  starModule : @StarModule R toModuleCat _ starAddMonoid.toStar _

namespace StarModuleCat

variable {R : Type*} [Ring R] [StarRing R]

instance : CoeSort (StarModuleCat.{u} R) (Type u) := ⟨fun V => V.toModuleCat⟩
instance (V : StarModuleCat R) : AddCommGroup V := inferInstanceAs (AddCommGroup V.toModuleCat)
instance (V : StarModuleCat R) : Module R V := inferInstanceAs (Module R V.toModuleCat)
instance (V : StarModuleCat R) : StarAddMonoid V := V.starAddMonoid
instance (V : StarModuleCat R) : StarModule R V := V.starModule

/-- Bundle a module with its native star structures. -/
abbrev of (R : Type*) [Ring R] [StarRing R] (V : Type u)
    [AddCommGroup V] [Module R V] [StarAddMonoid V] [StarModule R V] : StarModuleCat R :=
  ⟨ModuleCat.of R V, inferInstance, inferInstance⟩

/-- A linear map commuting with the additive involutions. -/
@[ext]
structure Hom (V W : StarModuleCat R) where
  /-- The underlying linear map. -/
  hom : V →ₗ[R] W
  /-- Preservation of conjugation. -/
  map_star' : ∀ v, hom (star v) = star (hom v)

attribute [simp] Hom.map_star'

instance : Category (StarModuleCat.{u} R) where
  Hom := Hom
  id V := ⟨LinearMap.id, fun _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun v => by simp⟩

/-- Morphisms are determined by their underlying linear maps. -/
@[ext] theorem hom_ext {V W : StarModuleCat R} {f g : V ⟶ W}
    (h : f.hom = g.hom) : f = g := Hom.ext h

@[simp] theorem id_hom (V : StarModuleCat R) : (𝟙 V : V ⟶ V).hom = LinearMap.id := rfl

@[simp] theorem comp_hom {V W X : StarModuleCat R} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- The forgetful functor discarding the involution. -/
def forget : StarModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj V := V.toModuleCat
  map f := ModuleCat.ofHom f.hom

instance : (forget (R := R)).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

end StarModuleCat

end TauCeti
