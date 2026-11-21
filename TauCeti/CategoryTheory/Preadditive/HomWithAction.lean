/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Morphism groups equipped with a target endomorphism action

Let `C` be a preadditive category, `Y : C`, and `ρ : R →+* End Y` a ring homomorphism from a
semiring `R`. For any `X : C`, postcomposition by `(ρ r).asHom` equips `X ⟶ Y` with a left
`R`-module structure (`TauCeti.HomWithAction`), making precomposition by any `φ : X ⟶ X'` an
`R`-linear map (`TauCeti.HomWithAction.precompLinearMap`) and precomposition by an isomorphism
an `R`-linear equivalence (`TauCeti.HomWithAction.precompLinearEquiv`).

## Main definitions

* `TauCeti.HomWithAction`: type synonym for `X ⟶ Y` carrying the left `R`-module structure
  induced by `ρ : R →+* End Y`.
* `TauCeti.HomWithAction.toHom`: the underlying additive equivalence `HomWithAction ρ X ≃+ (X ⟶ Y)`.
* `TauCeti.HomWithAction.precompLinearMap` and `TauCeti.HomWithAction.precompLinearEquiv`:
  `R`-linear contravariant functoriality in `X`.

## Implementation notes

The `@[expose]` type-synonym pattern for carrying a target endomorphism action adapts the design of
`TauCeti.Abelian.ExtWithAction` in `TauCeti/Algebra/Homology/DerivedCategory/Ext/WithAction.lean`
(Axel Delaval, Jie Xu, Shitan Xu).
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

section HomWithAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type*} [Semiring R] {Y : C} (ρ : R →+* End Y)

/-- `X ⟶ Y` equipped with the left `R`-module structure induced by `ρ : R →+* End Y`:
`r • f = f ≫ (ρ r).asHom`. -/
-- Expose the synonym so additive and scalar instances share the `X ⟶ Y` carrier.
@[expose]
def HomWithAction (_ρ : R →+* End Y) (X : C) : Type v := X ⟶ Y

namespace HomWithAction

instance (X : C) : AddCommGroup (HomWithAction ρ X) := inferInstanceAs (AddCommGroup (X ⟶ Y))

instance (X : C) : Module R (HomWithAction ρ X) := Module.compHom (X ⟶ Y) ρ

/-- The underlying additive equivalence `HomWithAction ρ X ≃+ (X ⟶ Y)`. -/
def toHom {X : C} : HomWithAction ρ X ≃+ (X ⟶ Y) := AddEquiv.refl _

@[simp]
lemma toHom_smul {X : C} (r : R) (f : HomWithAction ρ X) :
    toHom ρ (r • f) = toHom ρ f ≫ (ρ r).asHom := (rfl)

@[simp]
lemma toHom_symm_comp_asHom {X : C} (r : R) (f : X ⟶ Y) :
    (toHom ρ).symm (f ≫ (ρ r).asHom) = r • (toHom ρ).symm f := (rfl)

/-- Precomposition with `φ : X ⟶ X'` is `R`-linear on `HomWithAction ρ`. -/
def precompLinearMap {X X' : C} (φ : X ⟶ X') :
    HomWithAction ρ X' →ₗ[R] HomWithAction ρ X where
  toFun f := (toHom ρ).symm (φ ≫ toHom ρ f)
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := (Category.assoc φ (toHom ρ f) (ρ r).asHom).symm

@[simp]
lemma toHom_precompLinearMap {X X' : C} (φ : X ⟶ X') (f : HomWithAction ρ X') :
    toHom ρ (precompLinearMap ρ φ f) = φ ≫ toHom ρ f := (rfl)

/-- Precomposition with an isomorphism `e : X ≅ X'` as an `R`-linear equivalence on
`HomWithAction ρ`. -/
def precompLinearEquiv {X X' : C} (e : X ≅ X') :
    HomWithAction ρ X' ≃ₗ[R] HomWithAction ρ X :=
  LinearEquiv.ofLinearMap (precompLinearMap ρ e.hom) (precompLinearMap ρ e.inv)
    (LinearMap.ext fun f ↦ (toHom ρ).injective (e.hom_inv_id_assoc (toHom ρ f)))
    (LinearMap.ext fun f ↦ (toHom ρ).injective (e.inv_hom_id_assoc (toHom ρ f)))

@[simp]
lemma toHom_precompLinearEquiv {X X' : C} (e : X ≅ X') (f : HomWithAction ρ X') :
    toHom ρ (precompLinearEquiv ρ e f) = e.hom ≫ toHom ρ f := (rfl)

@[simp]
lemma toHom_precompLinearEquiv_symm {X X' : C} (e : X ≅ X') (f : HomWithAction ρ X) :
    toHom ρ ((precompLinearEquiv ρ e).symm f) = e.inv ≫ toHom ρ f := (rfl)

end HomWithAction

end HomWithAction

end TauCeti
