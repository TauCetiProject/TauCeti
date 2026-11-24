/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Preadditive and linear structure on finitely generated comodules

This file makes the preadditive and `R`-linear structures on the category of finitely generated
right comodules over a coalgebra over a commutative ring available from a finite-comodule import.
The category is a full subcategory of all comodules, so Mathlib transfers the preadditive
structure from `ComoduleCat`. The forgetful functor to `ModuleCat R` is additive and `R`-linear.

It also records concrete simp lemmas computing negation and subtraction through the underlying
ambient comodule morphism `.hom` and pointwise on elements. The additive monoid, scalar
multiplication, and their corresponding simp lemmas are available over a commutative semiring
in `Finite.Basic`.

## Main declarations

* `TauCeti.FGComoduleCat.instLinear`: finitely generated comodules form an `R`-linear category.
* `TauCeti.FGComoduleCat.hom_neg`, `hom_sub`: negation and subtraction agree with those
  of the ambient `ComoduleCat` morphism underneath.
* `TauCeti.FGComoduleCat.neg_apply`, `sub_apply`: the same operations computed pointwise.

## References

The transfer mechanism is Mathlib's `ObjectProperty.FullSubcategory` preadditive instance.

## Implementation notes

Mathlib's `CategoryTheory.Linear.fullSubcategory` would also make `FGComoduleCat R C` linear, but
with a module structure on morphisms that agrees with `TauCeti.FGComoduleCat.homModule` only up
to unfolding definitions. `instLinear` uses `homModule` itself, so that the scalar multiplication
of the linear structure is the one the existing simp lemmas `hom_smul` and `smul_apply` describe.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Forget a finite comodule to its underlying module. -/
noncomputable instance : HasForget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R) :=
  HasForget₂.trans _ (ComoduleCat.{u, v, w} R C) _

instance : (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).Additive :=
  inferInstanceAs ((incl ⋙ forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).Additive)

/-- Finitely generated comodules over a coalgebra over a commutative ring `R` form an `R`-linear
category, with the scalar multiplication `homModule` inherited from all comodules. -/
instance instLinear : Linear R (FGComoduleCat.{u, v, w} R C) where
  homModule := homModule
  smul_comp _ _ _ r f g := by
    ext1
    exact ComoduleCat.smul_comp R C r f.hom g.hom
  comp_smul _ _ _ f r g := by
    ext1
    exact ComoduleCat.comp_smul R C r f.hom g.hom

instance : (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).Linear R where
  map_smul _ _ := rfl

variable {M N : FGComoduleCat.{u, v, w} R C}

/-- The ambient comodule morphism underlying a negation is the negation of the underlying
morphism. -/
@[simp]
theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

/-- The ambient comodule morphism underlying a difference is the difference of the underlying
morphisms. -/
@[simp]
theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom :=
  rfl

/-- Negation of morphisms acts by pointwise negation. -/
@[simp]
theorem neg_apply (f : M ⟶ N) (m : M) : (-f) m = -f m :=
  rfl

/-- Subtraction of morphisms acts by pointwise subtraction. -/
@[simp]
theorem sub_apply (f g : M ⟶ N) (m : M) : (f - g) m = f m - g m :=
  rfl

end FGComoduleCat

end TauCeti
