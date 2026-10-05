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
its covariant action on `Y`, without any abelian or projectivity hypothesis.
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

end HomCokernel

end TauCeti
