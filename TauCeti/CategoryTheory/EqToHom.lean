/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Transporting categorical identities

This file records elementary identities for morphisms transported along equalities of objects.
They isolate the equality elimination needed when categorical constructions are definitionally equal
only after changing their object types.

## Main results

* `TauCeti.eqToHom_conjugate_eq_id`: conjugating an identity along an object equality gives an
  identity.
* `TauCeti.eqToHom_conjugate_eq_comp`: conjugation distributes over composition.
* `TauCeti.eqToHom_conjugate_add`: conjugation preserves addition in a preadditive category.
-/

public section

namespace TauCeti

open CategoryTheory

/-- A morphism equal to an identity remains the identity after transport along an object
equality. -/
theorem eqToHom_conjugate_eq_id {C : Type*} [Category* C] {X Y : C} (h : X = Y)
    (f : Y ⟶ Y) (hf : f = 𝟙 Y) : eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 X := by
  subst h
  simp [hf]

/-- Transport along object equalities distributes over composition. -/
theorem eqToHom_conjugate_eq_comp {C : Type*} [Category* C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : X' ⟶ Z') (g : X' ⟶ Y')
    (h : Y' ⟶ Z') (hf : f = g ≫ h) :
    eqToHom hX ≫ f ≫ eqToHom hZ.symm =
      (eqToHom hX ≫ g ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ h ≫ eqToHom hZ.symm := by
  subst hX
  subst hY
  subst hZ
  simp [hf]

/-- Transport along object equalities preserves addition of morphisms. -/
theorem eqToHom_conjugate_add {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y' = Y) {f g h : X' ⟶ Y'}
    (hfgh : f = g + h) :
    eqToHom hX ≫ f ≫ eqToHom hY =
      (eqToHom hX ≫ g ≫ eqToHom hY) + (eqToHom hX ≫ h ≫ eqToHom hY) := by
  subst hX
  subst hY
  simp [hfgh]

end TauCeti
