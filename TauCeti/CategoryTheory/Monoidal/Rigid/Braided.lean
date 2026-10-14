/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Mates for braided exact pairings

The braiding turns an exact pairing `(X, X')` into an exact pairing `(X', X)`.
Taking a right mate with respect to the original pairings and then with respect to these
swapped pairings recovers the original morphism. This makes double duality natural even
when the chosen dual of `X'` is not `X`.

The swapped pairing is Mathlib's `CategoryTheory.BraidedCategory.exactPairing_swap`.
The explicit-pairing statement `rightMate_swap_rightMate` follows the API proposed in
J. McKoen's Mathlib pull request #42145; its proof uses the evaluation characterization
of mates and naturality of the braiding.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.9
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The evaluation of the swapped pairing is braided evaluation. -/
@[reassoc]
theorem exactPairing_swap_evaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.evaluation C _ _ Y X (exactPairing_swap X Y) =
      (β_ X Y).hom ≫ ε_ X Y :=
  (rfl)

/-- The coevaluation of the swapped pairing uses the inverse braiding. -/
@[reassoc]
theorem exactPairing_swap_coevaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation C _ _ Y X (exactPairing_swap X Y) =
      η_ X Y ≫ (β_ Y X).inv :=
  (rfl)

end TauCeti

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Taking a right mate and then a right mate with respect to the braided swapped pairings
recovers the original morphism. No symmetry of the braiding is needed. -/
@[simp]
theorem rightMate_swap_rightMate {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    rightMate (exactPairing_swap Y Y') (exactPairing_swap X X') (rightMate pX pY f) = f := by
  let := exactPairing_swap Y Y'
  apply rightHom_ext (X := Y')
  rw [rightMate_comp_evaluation, TauCeti.exactPairing_swap_evaluation,
    TauCeti.exactPairing_swap_evaluation, braiding_naturality_right_assoc,
    braiding_naturality_left_assoc, rightMate_comp_evaluation]

end CategoryTheory.ExactPairing
