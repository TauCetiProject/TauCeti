/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cokernels of precomposition on Hom spaces

For a morphism `f : X ⟶ P` in a linear category, `HomCokernel R f Y` is
`Hom(X, Y)` modulo the maps extending across `f`. In a projective presentation
`0 → X → P → M → 0`, this quotient computes `Ext¹(M, Y)`.

The quotient uses Mathlib's submodule quotient, so its quotient map, induction
principle and universal property are those of `Submodule`. Postcomposition gives
its covariant action on `Y`; precomposition acts contravariantly on the presenting
object. A morphism killed by the presenting map defines a restriction out of the
quotient. These operations need no abelian or projectivity hypothesis.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v t

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] {X P Y Z W : C}

/-- The cokernel of `Hom(P, Y) → Hom(X, Y)` given by precomposition with `f`.
It is defined directly as a submodule quotient. -/
abbrev HomCokernel (f : X ⟶ P) (Y : C) :=
  (X ⟶ Y) ⧸ (Linear.leftComp R Y f).range

/-- A map represents zero in the Hom cokernel exactly when it extends across `f`. -/
theorem homCokernel_mk_eq_zero_iff (f : X ⟶ P) (g : X ⟶ Y) :
    (Submodule.Quotient.mk g : HomCokernel R f Y) = 0 ↔ ∃ h : P ⟶ Y, f ≫ h = g := by
  simp [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]

namespace HomCokernel

/-- Postcomposition on the cokernel of precomposition with `f`. -/
def map (f : X ⟶ P) (g : Y ⟶ Z) : HomCokernel R f Y →ₗ[R] HomCokernel R f Z :=
  (Linear.leftComp R Y f).range.mapQ (Linear.leftComp R Z f).range
    (Linear.rightComp R X g) (by
      rintro _ ⟨h, rfl⟩
      exact ⟨h ≫ g, (Category.assoc _ _ _).symm⟩)

/-- Postcomposition sends the class of `h` to the class of `h ≫ g`. -/
@[simp]
theorem map_mk (f : X ⟶ P) (g : Y ⟶ Z) (h : X ⟶ Y) :
    map R f g (Submodule.Quotient.mk h) = Submodule.Quotient.mk (h ≫ g) := by
  simp [map]

/-- Postcomposition with an identity acts as the identity. -/
@[simp]
theorem map_id (f : X ⟶ P) : map R f (𝟙 Y) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp

/-- Postcomposition respects composition of morphisms. -/
@[simp]
theorem map_comp (f : X ⟶ P) (g : Y ⟶ Z) (h : Z ⟶ W) :
    map R f (g ≫ h) = (map R f h).comp (map R f g) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ a => simp

/-- Precomposition by `e` on the cokernel of precomposition with `f`. -/
def precomp (f : X ⟶ P) (e : W ⟶ X) :
    HomCokernel R f Y →ₗ[R] HomCokernel R (e ≫ f) Y :=
  (Linear.leftComp R Y f).range.mapQ (Linear.leftComp R Y (e ≫ f)).range
    (Linear.leftComp R Y e) (by
      rintro _ ⟨h, rfl⟩
      exact ⟨h, Category.assoc _ _ _⟩)

/-- Precomposition sends the class of `h` to the class of `e ≫ h`. -/
@[simp]
theorem precomp_mk (f : X ⟶ P) (e : W ⟶ X) (h : X ⟶ Y) :
    precomp R f e (Submodule.Quotient.mk h) = Submodule.Quotient.mk (e ≫ h) := by
  simp [precomp]

/-- Precomposition commutes with postcomposition on Hom cokernels. -/
@[simp]
theorem precomp_map (f : X ⟶ P) (e : W ⟶ X) (g : Y ⟶ Z)
    (x : HomCokernel R f Y) :
    precomp R f e (map R f g x) = map R (e ≫ f) g (precomp R f e x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp

/-- Restriction of a Hom-cokernel class to a morphism annihilated by the presenting map. -/
def restrict (f : X ⟶ P) (e : W ⟶ X) (h : e ≫ f = 0) :
    HomCokernel R f Y →ₗ[R] (W ⟶ Y) :=
  (Linear.leftComp R Y f).range.liftQ (Linear.leftComp R Y e) (by
    rintro _ ⟨g, rfl⟩
    simp [← Category.assoc, h])

/-- Restriction evaluates a representative by precomposition. -/
@[simp]
theorem restrict_mk (f : X ⟶ P) (e : W ⟶ X) (h : e ≫ f = 0) (g : X ⟶ Y) :
    restrict R f e h (Submodule.Quotient.mk g) = e ≫ g := by
  simp [restrict]

/-- Restriction commutes with postcomposition in the coefficient object. -/
@[simp]
theorem restrict_map (f : X ⟶ P) (e : W ⟶ X) (h : e ≫ f = 0) (g : Y ⟶ Z)
    (x : HomCokernel R f Y) :
    restrict R f e h (map R f g x) = restrict R f e h x ≫ g := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => simp

/-- An epimorphism induces an injection on Hom cokernels by precomposition. -/
theorem precomp_injective {X W : C} (f : X ⟶ P) (e : W ⟶ X) [Epi e] :
    Function.Injective (precomp R f e (Y := Y)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ g =>
    obtain ⟨h, hh⟩ := (homCokernel_mk_eq_zero_iff R (e ≫ f) (e ≫ g)).mp
      (by simpa using hx)
    apply (homCokernel_mk_eq_zero_iff R f g).mpr
    exact ⟨h, (cancel_epi e).mp (by simpa using hh)⟩

end HomCokernel

end TauCeti
