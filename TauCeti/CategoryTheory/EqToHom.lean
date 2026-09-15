/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Transporting categorical morphisms along object equalities

This file provides general lemmas for removing and rearranging the conjugations by `eqToHom` that
arise when categorical objects are identified propositionally. They apply in an arbitrary category
and avoid exposing the definitional equality of the objects being transported.

## Main results

* `TauCeti.eqToHom_conjugate_cancel`: transporting a morphism and then transporting it back leaves
  it unchanged.
* `TauCeti.eqToHom_conjugate_square`: conjugating every edge preserves and reflects commutativity of
  a square.
* `TauCeti.eq_of_eqToHom_conjugate`: two morphisms with equal conjugates are equal.
* `TauCeti.eqToHom_conjugate_vertical_square_of_horizontal_square`: commutativity with conjugated
  horizontal edges gives commutativity after moving the conjugations to the vertical edges.
-/

public section

namespace TauCeti

open CategoryTheory

/-- Transporting a morphism along object equalities and then back leaves it unchanged. -/
theorem eqToHom_conjugate_cancel {C : Type*} [Category* C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    eqToHom hX.symm ≫ (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY = f := by
  subst X'
  subst Y'
  simp

/-- **Conjugating a commuting square by object equalities leaves it commuting**, and nothing else
becomes commuting that way: the square of transported edges commutes exactly when the original
one does. -/
theorem eqToHom_conjugate_square {C : Type*} [Category* C] {X X' Y Y' Z Z' W W' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hW : W = W')
    (f : X' ⟶ Y') (g : Y' ⟶ Z') (f' : X' ⟶ W') (g' : W' ⟶ Z') :
    (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ g ≫ eqToHom hZ.symm =
        (eqToHom hX ≫ f' ≫ eqToHom hW.symm) ≫ eqToHom hW ≫ g' ≫ eqToHom hZ.symm ↔
      f ≫ g = f' ≫ g' := by
  subst hX
  subst hY
  subst hZ
  subst hW
  simp

/-- **Two morphisms conjugated to the same morphism are equal**: conjugating back cancels, by
`TauCeti.eqToHom_conjugate_cancel`, on both sides at once. -/
theorem eq_of_eqToHom_conjugate {C : Type*} [Category* C] {X X' Y Y' : C} (hX : X' = X)
    (hY : Y = Y') {f g : X ⟶ Y}
    (h : eqToHom hX ≫ f ≫ eqToHom hY = eqToHom hX ≫ g ≫ eqToHom hY) : f = g :=
  (eqToHom_conjugate_cancel hX hY.symm f).symm.trans
    ((congrArg (fun u : X' ⟶ Y' ↦ eqToHom hX.symm ≫ u ≫ eqToHom hY.symm) h).trans
      (eqToHom_conjugate_cancel hX hY.symm g))

/-- **A square with conjugated horizontal edges yields a square with conjugated vertical edges.**
The horizontal conjugations cancel from the conclusion, while the vertical edges acquire the
corresponding conjugations. -/
theorem eqToHom_conjugate_vertical_square_of_horizontal_square {C : Type*} [Category* C]
    {A A' B B' D D' E E' : C} (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    (p : A' ⟶ B') (q : E' ⟶ D') (f : B ⟶ D) (g : A ⟶ E)
    (h : (eqToHom hA ≫ p ≫ eqToHom hB.symm) ≫ f = g ≫ eqToHom hE ≫ q ≫ eqToHom hD.symm) :
    p ≫ (eqToHom hB.symm ≫ f ≫ eqToHom hD) = (eqToHom hA.symm ≫ g ≫ eqToHom hE) ≫ q :=
  (eqToHom_conjugate_square hA hB hD hE p _ _ q).mp (by simpa using h)

end TauCeti
