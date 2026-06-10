/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import TauCeti.Algebra.Coalgebra.ComoduleCat

/-!
# Finitely generated comodules

This file packages finitely generated right comodules over a coalgebra as a full subcategory
of `ComoduleCat`. An object of `FGComoduleCat R C` is a right `C`-comodule whose underlying
`R`-module is finitely generated; over a field this is the finite-dimensional comodule
category requested by the reductive-groups roadmap.

This is a small Layer 1 prerequisite for the finite-dimensional representation category of an
affine group scheme: later tensor products, duals, matrix coefficients, and Tannakian
reconstruction should be built on this full subcategory rather than on all comodules.

## Main definitions

* `TauCeti.ComoduleCat.isFG`: the finite-generation object property on `ComoduleCat`.
* `TauCeti.FGComoduleCat`: finitely generated right comodules as a full subcategory.
* `TauCeti.FGComoduleCat.of`: build a finitely generated bundled comodule from unbundled data.
* `TauCeti.FGComoduleCat.ofHom`: lift an unbundled comodule morphism between finitely generated
  comodules.

## References

This supplies the finite-dimensional-category part of
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra". The construction follows Mathlib's `FGModuleCat` pattern: finite objects are a full
subcategory defined by the object property `Module.Finite`.
-/

open CategoryTheory

namespace TauCeti

universe u v w

section Semiring

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace ComoduleCat

/-- Finite-generation as an object property on the category of right comodules. -/
def isFG : ObjectProperty (ComoduleCat.{u, v, w} R C) :=
  fun M => Module.Finite R M

/-- The finitely generated comodule property is exactly finite generation of the underlying
module. -/
theorem isFG_iff (M : ComoduleCat.{u, v, w} R C) :
    isFG (R := R) (C := C) M ↔ Module.Finite R M :=
  Iff.rfl

end ComoduleCat

/-- The category of finitely generated right comodules over a fixed coalgebra.

For a field base, this is the category of finite-dimensional right comodules. -/
abbrev FGComoduleCat :=
  (ComoduleCat.isFG.{u, v, w} R C).FullSubcategory

namespace FGComoduleCat

variable {R C}

/-- The underlying type of a finitely generated comodule. -/
@[reducible]
def carrier (M : FGComoduleCat.{u, v, w} R C) : Type w :=
  M.obj

instance : CoeSort (FGComoduleCat.{u, v, w} R C) (Type w) :=
  ⟨carrier⟩

attribute [coe] carrier

instance (M : FGComoduleCat.{u, v, w} R C) : AddCommMonoid M :=
  inferInstanceAs (AddCommMonoid M.obj)

instance (M : FGComoduleCat.{u, v, w} R C) : Module R M :=
  inferInstanceAs (Module R M.obj)

instance (M : FGComoduleCat.{u, v, w} R C) : Comodule R C M :=
  inferInstanceAs (Comodule R C M.obj)

/-- The underlying module of a finitely generated comodule is finitely generated. -/
instance (M : FGComoduleCat.{u, v, w} R C) : Module.Finite R M :=
  M.property

/-- Lift an unbundled finitely generated right comodule to `FGComoduleCat`. -/
abbrev of (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] : FGComoduleCat.{u, v, w} R C :=
  ⟨ComoduleCat.of R C M, inferInstanceAs (Module.Finite R M)⟩

/-- The object of `ComoduleCat` underlying `FGComoduleCat.of` is `ComoduleCat.of`. -/
@[simp]
theorem of_obj (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    (of (R := R) (C := C) M).obj = ComoduleCat.of R C M :=
  rfl

/-- The coaction on `FGComoduleCat.of` is the original unbundled coaction. -/
@[simp]
theorem of_coact {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    Comodule.coact (R := R) (C := C) (M := of (R := R) (C := C) M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  rfl

/-- Typecheck an unbundled comodule morphism between finitely generated comodules as a
categorical morphism in `FGComoduleCat`. -/
abbrev ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    of (R := R) (C := C) M ⟶ of (R := R) (C := C) N :=
  ObjectProperty.homMk (ComoduleCat.ofHom (R := R) (C := C) f)

/-- Turning an unbundled comodule morphism into an `FGComoduleCat` morphism and projecting to
the ambient comodule category recovers the original bundled morphism. -/
@[simp]
theorem ofHom_hom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    (ofHom (R := R) (C := C) f).hom = ComoduleCat.ofHom (R := R) (C := C) f :=
  rfl

/-- The categorical identity on a finitely generated bundled comodule is the bundled form of
the identity comodule morphism. -/
@[simp]
theorem ofHom_id {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    ofHom (R := R) (C := C) (Comodule.Hom.id R C M) = 𝟙 (of (R := R) (C := C) M) :=
  rfl

/-- Categorical composition of finitely generated bundled comodule morphisms is the bundled
form of composition of comodule morphisms. -/
@[simp]
theorem ofHom_comp {M N P : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] [AddCommMonoid P] [Module R P] [Comodule R C P]
    [Module.Finite R P] (f : Comodule.Hom R C M N) (g : Comodule.Hom R C N P) :
    ofHom (R := R) (C := C) (Comodule.Hom.comp g f) =
      ofHom (R := R) (C := C) f ≫ ofHom (R := R) (C := C) g :=
  rfl

/-- The `FGComoduleCat` morphism induced by an unbundled morphism applies as that morphism. -/
@[simp]
theorem ofHom_apply {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) (m : M) :
    ofHom (R := R) (C := C) f m = f m :=
  rfl

end FGComoduleCat

end Semiring

section Ring

variable (R : Type u) [CommRing R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {R C}

namespace FGComoduleCat

instance (M : FGComoduleCat.{u, v, w} R C) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

end FGComoduleCat

end Ring

end TauCeti
