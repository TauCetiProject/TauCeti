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

For a field `k`, the algebraic function fields of one variable over `k` (fields `F` with a
`k`-algebra structure satisfying `TauCeti.IsFunctionField k F`) form a category whose morphisms
are the `k`-algebra homomorphisms. Every such homomorphism is injective, so the morphisms are the
`k`-embeddings of function fields. This is the field side of the anti-equivalence between
algebraic function fields of one variable over `k` and regular proper curves over `k`.

The bundled objects and the morphism structure follow Mathlib's `AlgCat`.

## Main definitions

* `TauCeti.FunctionFieldCat k`: the category of algebraic function fields over `k`.
* `TauCeti.FunctionFieldCat.of`: the object of `FunctionFieldCat k` given by a function field.
* `TauCeti.FunctionFieldCat.Hom.hom` and `TauCeti.FunctionFieldCat.ofHom`: the passage between
  morphisms of `FunctionFieldCat k` and `k`-algebra homomorphisms.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TauCeti

/-- The category of algebraic function fields of one variable over a field `k`: fields `F` with a
`k`-algebra structure satisfying `IsFunctionField k F`, with `k`-algebra homomorphisms as
morphisms. -/
structure FunctionFieldCat (k : Type u) [Field k] where
  /-- The underlying field. -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  /-- The underlying field is an algebraic function field over `k`. -/
  isFunctionField : IsFunctionField k carrier

attribute [instance] FunctionFieldCat.field FunctionFieldCat.algebra

namespace FunctionFieldCat

variable {k : Type u} [Field k]

instance : CoeSort (FunctionFieldCat k) (Type u) :=
  ⟨FunctionFieldCat.carrier⟩

attribute [coe] FunctionFieldCat.carrier

/-- The object of `FunctionFieldCat k` given by an algebraic function field `F` over `k`. -/
abbrev of (F : Type u) [Field F] [Algebra k F] (hF : IsFunctionField k F) : FunctionFieldCat k :=
  ⟨F, hF⟩

lemma coe_of (F : Type u) [Field F] [Algebra k F] (hF : IsFunctionField k F) :
    (of F hF : Type u) = F :=
  rfl

/-- The type of morphisms in `FunctionFieldCat k`. -/
@[ext]
structure Hom (F G : FunctionFieldCat k) where
  /-- The underlying `k`-algebra homomorphism. -/
  hom' : F →ₐ[k] G

instance : Category (FunctionFieldCat k) where
  Hom := Hom
  id F := ⟨AlgHom.id k F⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (FunctionFieldCat k) (· →ₐ[k] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- The `k`-algebra homomorphism underlying a morphism of `FunctionFieldCat k`. -/
abbrev Hom.hom {F G : FunctionFieldCat k} (f : Hom F G) : F →ₐ[k] G :=
  ConcreteCategory.hom (C := FunctionFieldCat k) f

/-- The morphism of `FunctionFieldCat k` given by a `k`-algebra homomorphism. -/
abbrev ofHom {F G : FunctionFieldCat k} (f : F →ₐ[k] G) : F ⟶ G :=
  ConcreteCategory.ofHom (C := FunctionFieldCat k) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (F G : FunctionFieldCat k) (f : Hom F G) : F →ₐ[k] G :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id {F : FunctionFieldCat k} : (𝟙 F : F ⟶ F).hom = AlgHom.id k F :=
  rfl

@[simp]
lemma hom_comp {F G H : FunctionFieldCat k} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[ext]
lemma hom_ext {F G : FunctionFieldCat k} {f g : F ⟶ G} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma hom_ofHom {F G : FunctionFieldCat k} (f : F →ₐ[k] G) : (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {F G : FunctionFieldCat k} (f : F ⟶ G) : ofHom f.hom = f :=
  rfl

@[simp]
lemma ofHom_id {F : FunctionFieldCat k} : ofHom (AlgHom.id k F) = 𝟙 F :=
  rfl

@[simp]
lemma ofHom_comp {F G H : FunctionFieldCat k} (f : F →ₐ[k] G) (g : G →ₐ[k] H) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/-- An isomorphism of `FunctionFieldCat k` from a `k`-algebra isomorphism. -/
def isoMk {F G : FunctionFieldCat k} (e : F ≃ₐ[k] G) : F ≅ G where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
lemma isoMk_hom {F G : FunctionFieldCat k} (e : F ≃ₐ[k] G) : (isoMk e).hom = ofHom e :=
  (rfl)

@[simp]
lemma isoMk_inv {F G : FunctionFieldCat k} (e : F ≃ₐ[k] G) : (isoMk e).inv = ofHom e.symm :=
  (rfl)

end FunctionFieldCat

end TauCeti
