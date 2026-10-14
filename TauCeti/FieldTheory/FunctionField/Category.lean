/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The category of algebraic function fields

This file defines the category `TauCeti.FunctionFieldCat k` of algebraic function fields of one
variable over a field `k` (`TauCeti.IsFunctionField`), with the `k`-algebra homomorphisms as
morphisms. A `k`-algebra homomorphism of fields is injective, so the morphisms are the
`k`-embeddings of function fields.

This is the field side of the correspondence between function fields of one variable and regular
proper curves: taking the function field is an anti-equivalence from the category of regular
proper curves over `k` with dominant morphisms onto this category.

## Main definitions

* `TauCeti.FunctionFieldCat k`: the category of algebraic function fields over `k`.
* `TauCeti.FunctionFieldCat.of`: bundle a function field as an object.
* `TauCeti.FunctionFieldCat.ofHom`: a `k`-algebra homomorphism as a morphism.
* `TauCeti.FunctionFieldCat.isoMk`: a `k`-algebra isomorphism as an isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable (k : Type u) [Field k]

/-- The category of algebraic function fields of one variable over `k`, with `k`-algebra
homomorphisms (the `k`-embeddings) as morphisms. -/
structure FunctionFieldCat where
  /-- Bundle an algebraic function field over `k` as an object of `FunctionFieldCat k`. -/
  of ::
  /-- The underlying field. -/
  carrier : Type v
  [field : Field carrier]
  [algebra : Algebra k carrier]
  /-- The underlying field is an algebraic function field of one variable over `k`. -/
  isFunctionField : IsFunctionField k carrier

namespace FunctionFieldCat

attribute [instance] field algebra

initialize_simps_projections FunctionFieldCat (-field, -algebra)

instance : CoeSort (FunctionFieldCat.{u, v} k) (Type v) := ⟨carrier⟩

attribute [coe] carrier

variable {k}

@[simp]
theorem coe_of (F : Type v) [Field F] [Algebra k F] (hF : IsFunctionField k F) :
    (of F hF : Type v) = F :=
  (rfl)

/-- The type of morphisms in `FunctionFieldCat k`. -/
@[ext]
structure Hom (F F' : FunctionFieldCat.{u, v} k) where
  mk ::
  /-- The underlying `k`-algebra homomorphism. -/
  hom' : F →ₐ[k] F'

instance : Category (FunctionFieldCat.{u, v} k) where
  Hom F F' := Hom F F'
  id F := ⟨AlgHom.id k F⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (FunctionFieldCat.{u, v} k) (· →ₐ[k] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {F F' F'' : FunctionFieldCat.{u, v} k}

/-- The `k`-algebra homomorphism underlying a morphism of `FunctionFieldCat k`. -/
abbrev Hom.hom (f : F ⟶ F') : F →ₐ[k] F' :=
  ConcreteCategory.hom (C := FunctionFieldCat k) f

/-- A `k`-algebra homomorphism of function fields as a morphism of `FunctionFieldCat k`. -/
abbrev ofHom (f : F →ₐ[k] F') : F ⟶ F' :=
  ConcreteCategory.ofHom (C := FunctionFieldCat k) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (F F' : FunctionFieldCat.{u, v} k) (f : Hom F F') : F →ₐ[k] F' :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
theorem hom_id : (𝟙 F : F ⟶ F).hom = AlgHom.id k F :=
  (rfl)

@[simp]
theorem hom_comp (f : F ⟶ F') (g : F' ⟶ F'') : (f ≫ g).hom = g.hom.comp f.hom :=
  (rfl)

@[ext]
theorem hom_ext {f g : F ⟶ F'} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- A `k`-algebra isomorphism of function fields as an isomorphism of `FunctionFieldCat k`. -/
def isoMk (e : F ≃ₐ[k] F') : F ≅ F' where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
theorem isoMk_hom (e : F ≃ₐ[k] F') : (isoMk e).hom = ofHom e :=
  (rfl)

@[simp]
theorem isoMk_inv (e : F ≃ₐ[k] F') : (isoMk e).inv = ofHom e.symm :=
  (rfl)

end FunctionFieldCat

end TauCeti
