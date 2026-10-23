/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-!
# Finite types form a cartesian monoidal category

A limit of a finite diagram of finite types is finite: it is a set of compatible families, a
subset of the finite product of the objects of the diagram. So the finite types are closed under
finite limits in `Type u`, and the full subcategory `FintypeCat` inherits the cartesian monoidal
structure of `Type u`: the tensor product of two finite types is their product and the unit is
`PUnit`. Monoid and group objects in `FintypeCat`, and in categories of actions on finite types,
are taken with respect to this structure.

## Main results

* `TauCeti.isClosedUnderFiniteLimits_finite`: the finite types are closed under finite limits.
* The instance `CartesianMonoidalCategory FintypeCat`, restricted from `Type u`, and the braiding
  `BraidedCategory FintypeCat` it determines.
* `FintypeCat.tensorHom_apply`, `FintypeCat.lift_apply` and their companions: the structure
  morphisms act on pairs as in `Type u`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace TauCeti

/-- **Finite types are closed under finite limits.** The apex of a limit cone over a finite
diagram of finite types is finite. -/
instance isClosedUnderFiniteLimits_finite :
    ObjectProperty.IsClosedUnderFiniteLimits (Finite : ObjectProperty (Type u)) where
  isClosedUnderLimitsOfShape J _ _ := ⟨fun X ⟨p⟩ ↦ by
    have := p.prop_diag_obj
    have : Finite J := inferInstance
    exact Finite.of_equiv _ (Types.isLimitEquivSections p.isLimit).symm⟩

end TauCeti

namespace FintypeCat

/-- The braiding of the cartesian monoidal structure on finite types, which swaps the factors of a
product. -/
noncomputable instance braidedCategory : BraidedCategory FintypeCat.{u} :=
  .ofCartesianMonoidalCategory

/-! ### The cartesian monoidal structure on elements

The tensor product of finite types is their product, so the structure morphisms act on pairs
exactly as in `Type u`. -/

@[simp]
theorem tensorHom_apply {W X Y Z : FintypeCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    dsimp% (f ⊗ₘ g) p = (f p.1, g p.2) :=
  rfl

@[simp]
theorem whiskerLeft_apply (X : FintypeCat.{u}) {Y Z : FintypeCat.{u}} (f : Y ⟶ Z) (p : X ⊗ Y) :
    dsimp% (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : FintypeCat.{u}} (f : Y ⟶ Z) (X : FintypeCat.{u}) (p : Y ⊗ X) :
    dsimp% (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {X : FintypeCat.{u}} (p : 𝟙_ FintypeCat.{u} ⊗ X) :
    dsimp% (λ_ X).hom p = p.2 :=
  rfl

@[simp]
theorem leftUnitor_inv_apply {X : FintypeCat.{u}} (x : X) :
    dsimp% (λ_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
theorem rightUnitor_hom_apply {X : FintypeCat.{u}} (p : X ⊗ 𝟙_ FintypeCat.{u}) :
    dsimp% (ρ_ X).hom p = p.1 :=
  rfl

@[simp]
theorem rightUnitor_inv_apply {X : FintypeCat.{u}} (x : X) :
    dsimp% (ρ_ X).inv x = (x, PUnit.unit) :=
  rfl

@[simp]
theorem associator_hom_apply {X Y Z : FintypeCat.{u}} (p : (X ⊗ Y) ⊗ Z) :
    dsimp% (α_ X Y Z).hom p = (p.1.1, (p.1.2, p.2)) :=
  rfl

@[simp]
theorem associator_inv_apply {X Y Z : FintypeCat.{u}} (p : X ⊗ (Y ⊗ Z)) :
    dsimp% (α_ X Y Z).inv p = ((p.1, p.2.1), p.2.2) :=
  rfl

@[simp]
theorem fst_apply {X Y : FintypeCat.{u}} (p : X ⊗ Y) :
    dsimp% fst X Y p = p.1 :=
  rfl

@[simp]
theorem snd_apply {X Y : FintypeCat.{u}} (p : X ⊗ Y) :
    dsimp% snd X Y p = p.2 :=
  rfl

@[simp]
theorem lift_apply {T X Y : FintypeCat.{u}} (f : T ⟶ X) (g : T ⟶ Y) (t : T) :
    dsimp% lift f g t = (f t, g t) :=
  rfl

end FintypeCat
