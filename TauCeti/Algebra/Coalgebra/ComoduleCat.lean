/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Semi
import TauCeti.Algebra.Coalgebra.Comodule.Hom

/-!
# The category of comodules over a coalgebra

This file bundles the right comodules defined in `TauCeti.Algebra.Coalgebra.Comodule` into a
category. For a fixed coalgebra `C` over a commutative semiring `R`, objects are
`R`-semimodules with a right `C`-coaction and morphisms are the comodule morphisms already
defined by `Comodule.Hom`.

The reductive-groups roadmap asks for the category of finite-dimensional comodules over a
Hopf algebra as the representation category of an affine group scheme. This file supplies the
underlying bundled category and its forgetful functor to `SemimoduleCat`; finiteness, tensor
products, duals, and the Hopf-algebra specialization can be added on top.

## Main definitions

* `TauCeti.ComoduleCat`: bundled right comodules over a fixed coalgebra.
* `TauCeti.ComoduleCat.of`: build a bundled comodule from an unbundled one.
* `TauCeti.ComoduleCat.ofHom`: view an unbundled comodule morphism as a categorical morphism.
* `forget₂ (ComoduleCat R C) (SemimoduleCat R)`: the forgetful functor to semimodules.

## References

This is the categorical packaging of the standard right-comodule definition, added for
Layer 1 of the Tau Ceti reductive-groups roadmap: "Comodules over a coalgebra/Hopf algebra".
The bundled-category API follows the pattern of `Mathlib.Algebra.Category.CoalgCat.Basic` and
`Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.
-/

open CategoryTheory

namespace TauCeti

universe u v w

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The category of right comodules over a fixed `R`-coalgebra `C`. -/
structure ComoduleCat extends SemimoduleCat.{w} R where
  /-- The right `C`-comodule structure on the underlying module. -/
  instComodule : Comodule R C carrier

attribute [instance] ComoduleCat.instComodule

namespace ComoduleCat

instance : CoeSort (ComoduleCat.{u, v, w} R C) (Type w) :=
  ⟨fun M => M.toSemimoduleCat⟩

instance (M : ComoduleCat.{u, v, w} R C) : AddCommMonoid M :=
  M.isAddCommMonoid

instance (M : ComoduleCat.{u, v, w} R C) : Module R M :=
  M.isModule

/-- Build a bundled comodule from a type carrying the usual unbundled typeclasses. -/
abbrev of (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M] :
    ComoduleCat.{u, v, w} R C where
  carrier := M
  instComodule := inferInstance

/-- The coaction on `ComoduleCat.of` is the original unbundled coaction. -/
@[simp]
theorem of_coact {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M] :
    Comodule.coact (R := R) (C := C) (M := of R C M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  rfl

/-- Morphisms in `ComoduleCat` are morphisms of the underlying right comodules. -/
abbrev Hom (M N : ComoduleCat.{u, v, w} R C) :=
  Comodule.Hom R C M N

instance category : Category (ComoduleCat.{u, v, w} R C) where
  Hom M N := Hom R C M N
  id M := Comodule.Hom.id R C M
  comp f g := Comodule.Hom.comp g f

instance homZero (M N : ComoduleCat.{u, v, w} R C) : Zero (M ⟶ N) :=
  inferInstanceAs (Zero (Comodule.Hom R C M N))

instance homAdd (M N : ComoduleCat.{u, v, w} R C) : Add (M ⟶ N) :=
  inferInstanceAs (Add (Comodule.Hom R C M N))

instance homAddCommMonoid (M N : ComoduleCat.{u, v, w} R C) : AddCommMonoid (M ⟶ N) :=
  inferInstanceAs (AddCommMonoid (Comodule.Hom R C M N))

/-- `ComoduleCat` is concrete, with concrete morphisms the bundled comodule morphisms. -/
instance concreteCategory :
    ConcreteCategory (ComoduleCat.{u, v, w} R C)
      (fun M N => Comodule.Hom R C M N) where
  hom f := f
  ofHom f := f

/-- Turn a morphism in `ComoduleCat` back into its underlying comodule morphism. -/
abbrev hom {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    Comodule.Hom R C M N :=
  f

/-- Typecheck an unbundled comodule morphism as a morphism in `ComoduleCat`. -/
abbrev ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) :
    of R C M ⟶ of R C N :=
  f

/-- Turning an unbundled comodule morphism into a categorical morphism and back is the identity. -/
@[simp]
theorem hom_ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) :
    ConcreteCategory.hom (C := ComoduleCat R C) (ofHom (R := R) (C := C) f) = f :=
  rfl

/-- Turning a categorical morphism into an unbundled comodule morphism and back is the identity. -/
@[simp]
theorem ofHom_hom {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    ofHom (R := R) (C := C) (ConcreteCategory.hom (C := ComoduleCat R C) f) = f :=
  rfl

/-- The categorical identity is the bundled form of the identity comodule morphism. -/
@[simp]
theorem ofHom_id {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M] :
    ofHom (R := R) (C := C) (Comodule.Hom.id R C M) = 𝟙 (of R C M) :=
  rfl

/-- Categorical composition is the bundled form of composition of comodule morphisms. -/
@[simp]
theorem ofHom_comp {M N P : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid P] [Module R P] [Comodule R C P] (f : Comodule.Hom R C M N)
    (g : Comodule.Hom R C N P) :
    ofHom (R := R) (C := C) (Comodule.Hom.comp g f) =
      ofHom (R := R) (C := C) f ≫ ofHom (R := R) (C := C) g :=
  rfl

/-- The bundled form of a comodule morphism applies as the original morphism. -/
@[simp]
theorem ofHom_apply {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) (m : M) :
    ofHom (R := R) (C := C) f m = f m :=
  rfl

/-- The underlying linear map of a `ComoduleCat` morphism. -/
abbrev homLinearMap {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) : M →ₗ[R] N :=
  f.toLinearMap

/-- Two morphisms of bundled comodules are equal when their underlying functions are equal. -/
@[ext]
theorem hom_ext {M N : ComoduleCat.{u, v, w} R C} {f g : M ⟶ N}
    (h : ∀ m, f m = g m) : f = g :=
  Comodule.Hom.ext h

/-- The identity morphism has the identity linear map underneath. -/
@[simp]
theorem toLinearMap_id (M : ComoduleCat.{u, v, w} R C) :
    (𝟙 M : M ⟶ M).toLinearMap = LinearMap.id :=
  rfl

/-- Composition in `ComoduleCat` is composition of the underlying linear maps. -/
@[simp]
theorem toLinearMap_comp {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

/-- The identity morphism acts as the identity function. -/
@[simp]
theorem id_apply (M : ComoduleCat.{u, v, w} R C) (m : M) :
    (𝟙 M : M ⟶ M) m = m :=
  rfl

/-- Composition of morphisms acts by ordinary function composition. -/
@[simp]
theorem comp_apply {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g : N ⟶ P)
    (m : M) :
    (f ≫ g) m = g (f m) :=
  rfl

/-- The zero morphism has the zero linear map underneath. -/
@[simp]
theorem toLinearMap_zero (M N : ComoduleCat.{u, v, w} R C) :
    (0 : M ⟶ N).toLinearMap = 0 :=
  rfl

/-- Addition of morphisms is addition of the underlying linear maps. -/
@[simp]
theorem toLinearMap_add {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- The zero morphism acts as the zero function. -/
@[simp]
theorem zero_apply {M N : ComoduleCat.{u, v, w} R C} (m : M) :
    (0 : M ⟶ N) m = 0 :=
  rfl

/-- Addition of morphisms acts by pointwise addition. -/
@[simp]
theorem add_apply {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) (m : M) :
    (f + g) m = f m + g m :=
  rfl

/-- Composition in `ComoduleCat` is additive in the left morphism. -/
@[simp]
theorem add_comp {M N P : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) (h : N ⟶ P) :
    (f + g) ≫ h = f ≫ h + g ≫ h := by
  ext m
  exact map_add h.toLinearMap (f m) (g m)

/-- Composition in `ComoduleCat` is additive in the right morphism. -/
@[simp]
theorem comp_add {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g h : N ⟶ P) :
    f ≫ (g + h) = f ≫ g + f ≫ h := by
  ext m
  rfl

/-- Composing the zero morphism on the left gives the zero morphism. -/
@[simp]
theorem zero_comp {M N P : ComoduleCat.{u, v, w} R C} (f : N ⟶ P) :
    (0 : M ⟶ N) ≫ f = 0 := by
  ext m
  exact map_zero f.toLinearMap

/-- Composing the zero morphism on the right gives the zero morphism. -/
@[simp]
theorem comp_zero {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    f ≫ (0 : N ⟶ P) = 0 := by
  ext m
  rfl

/-- The forgetful functor from comodules to their underlying semimodules. -/
instance hasForgetToSemimodule : HasForget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R) where
  forget₂ :=
    { obj M := SemimoduleCat.of R M
      map f := SemimoduleCat.ofHom f.toLinearMap }

/-- The forgetful functor sends a comodule to its underlying semimodule. -/
@[simp]
theorem forget₂_obj (M : ComoduleCat.{u, v, w} R C) :
    (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).obj M =
      SemimoduleCat.of R M :=
  rfl

/-- The forgetful functor sends a comodule morphism to its underlying linear map. -/
@[simp]
theorem forget₂_map {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).map f =
      SemimoduleCat.ofHom f.toLinearMap :=
  rfl

end ComoduleCat

end TauCeti
