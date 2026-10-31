/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Center

/-!
# Basic identities for half-braidings

A half-braiding `b : HalfBraiding X` on an object `X` of a monoidal category `C` is a natural
family of isomorphisms `b.β U : X ⊗ U ≅ U ⊗ X`, monoidal in `U`. This file records consequences of
these axioms that Mathlib does not state: the component at the unit object is forced to be the
composite of the unitors, and the inverse components are again monoidal and natural in `U`.

## Main declarations

* `CategoryTheory.HalfBraiding.β_tensorUnit_hom`: a half-braiding at the unit is the composite of
  the unitors;
* `CategoryTheory.HalfBraiding.monoidal_inv`: the inverse of a half-braiding at a tensor product,
  computed from the factors;
* `CategoryTheory.HalfBraiding.naturality_inv`: naturality of the inverse of a half-braiding.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace HalfBraiding

variable {X : C} (b : HalfBraiding X)

/-- A half-braiding at the unit object is the composite of the unitors. -/
@[simp]
theorem β_tensorUnit_hom : (b.β (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  have h₁ := b.naturality (λ_ (𝟙_ C)).hom
  rw [b.monoidal] at h₁
  -- Cancel the invertible `(b.β (𝟙_ C)).hom` on the right of `h₁`.
  have h₂ : X ◁ (λ_ (𝟙_ C)).hom =
      (α_ _ _ _).inv ≫ (b.β (𝟙_ C)).hom ▷ 𝟙_ C ≫ (α_ _ _ _).hom ≫ (λ_ _).hom := by
    rw [← cancel_mono (b.β (𝟙_ C)).hom, h₁]
    simp only [Category.assoc]
    monoidal
  have h₃ : ((b.β (𝟙_ C)).hom ≫ (λ_ X).hom) ▷ 𝟙_ C = (ρ_ X).hom ▷ 𝟙_ C := by
    rw [comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv]
    calc
      _ = ((α_ _ _ _).inv ≫ (b.β (𝟙_ C)).hom ▷ 𝟙_ C ≫ (α_ _ _ _).hom ≫ (λ_ _).hom) ≫
            (λ_ _).inv ≫ (α_ _ _ _).inv ≫ (λ_ X).hom ▷ 𝟙_ C := by monoidal
      _ = _ := by rw [← h₂]; monoidal
  rw [← cancel_mono (λ_ X).hom]
  simpa [whiskerRight_id] using congrArg (fun f ↦ (ρ_ _).inv ≫ f ≫ (ρ_ _).hom) h₃

/-- The inverse of a half-braiding at a tensor product, computed from the factors. -/
@[simp]
theorem monoidal_inv (U U' : C) :
    (b.β (U ⊗ U')).inv =
      (α_ _ _ _).hom ≫ U ◁ (b.β U').inv ≫ (α_ _ _ _).inv ≫ (b.β U).inv ▷ U' ≫
        (α_ _ _ _).hom := by
  apply Iso.inv_ext
  simp [b.monoidal]

/-- Naturality of the inverse of a half-braiding. -/
@[reassoc (attr := simp)]
theorem naturality_inv {U U' : C} (f : U ⟶ U') :
    f ▷ X ≫ (b.β U').inv = (b.β U).inv ≫ X ◁ f := by
  rw [Iso.comp_inv_eq, Category.assoc, b.naturality, Iso.inv_hom_id_assoc]

end HalfBraiding

end CategoryTheory
