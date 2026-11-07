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

instance {V W : StarModuleCat R} : FunLike (Hom V W) V W where
  coe f := f.hom
  coe_injective _ _ h := Hom.ext (DFunLike.coe_injective h)

instance : Category (StarModuleCat.{u} R) where
  Hom := Hom
  id V := ⟨LinearMap.id, fun _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun v => by simp⟩

instance : ConcreteCategory (StarModuleCat.{u} R) Hom where
  hom f := f
  ofHom f := f

@[simp] theorem Hom.coe_hom_apply {V W : StarModuleCat R} (f : V ⟶ W) (v : V) :
    f v = f.hom v := rfl

/-- Bundle a linear map that commutes with star as a morphism. -/
abbrev ofHom {V W : StarModuleCat R} (f : V →ₗ[R] W)
    (hf : ∀ v, f (star v) = star (f v)) : V ⟶ W := ⟨f, hf⟩

@[simp] theorem hom_ofHom {V W : StarModuleCat R} (f : V →ₗ[R] W)
    (hf : ∀ v, f (star v) = star (f v)) : (ofHom f hf).hom = f := rfl

@[simp] theorem ofHom_hom {V W : StarModuleCat R} (f : V ⟶ W) :
    ofHom f.hom f.map_star' = f := rfl

/-- Morphisms are determined by their underlying linear maps. -/
@[ext] theorem hom_ext {V W : StarModuleCat R} {f g : V ⟶ W}
    (h : f.hom = g.hom) : f = g := Hom.ext h

@[simp] theorem hom_id (V : StarModuleCat R) : (𝟙 V : V ⟶ V).hom = LinearMap.id := rfl

@[simp] theorem hom_comp {V W X : StarModuleCat R} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- A star-preserving linear equivalence gives an isomorphism of star modules. -/
def isoMk {V W : StarModuleCat R} (e : V ≃ₗ[R] W)
    (he : ∀ v, e (star v) = star (e v)) : V ≅ W where
  hom := ofHom e.toLinearMap he
  inv := ofHom e.symm.toLinearMap (fun w => by
    apply e.injective
    rw [he]
    simp)
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

@[simp] theorem isoMk_hom_hom {V W : StarModuleCat R} (e : V ≃ₗ[R] W)
    (he : ∀ v, e (star v) = star (e v)) : (isoMk e he).hom.hom = e.toLinearMap := by rfl

@[simp] theorem isoMk_inv_hom {V W : StarModuleCat R} (e : V ≃ₗ[R] W)
    (he : ∀ v, e (star v) = star (e v)) : (isoMk e he).inv.hom = e.symm.toLinearMap := by rfl

/-- The forgetful functor discarding the involution. -/
instance : HasForget₂ (StarModuleCat.{u} R) (ModuleCat.{u} R) where
  forget₂ :=
    { obj V := V.toModuleCat
      map f := ModuleCat.ofHom f.hom }

@[simp] theorem forget₂_obj (V : StarModuleCat.{u} R) :
    (forget₂ (StarModuleCat R) (ModuleCat R)).obj V = V.toModuleCat := rfl

@[simp] theorem forget₂_map {V W : StarModuleCat.{u} R} (f : V ⟶ W) :
    ((forget₂ (StarModuleCat R) (ModuleCat R)).map f).hom = f.hom := rfl

instance : (forget₂ (StarModuleCat.{u} R) (ModuleCat.{u} R)).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

end StarModuleCat

end TauCeti
