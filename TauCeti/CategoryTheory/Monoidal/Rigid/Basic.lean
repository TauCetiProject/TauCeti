/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Exact pairings in rigid monoidal categories

This file records evaluation and coevaluation formulas for transported exact pairings and for the
adjunction associated to an exact pairing.

## Main declarations

* `TauCeti.exactPairingCongrLeft_evaluation` and
  `TauCeti.exactPairingCongrLeft_coevaluation`: the pairing transported across an isomorphism;
* `TauCeti.tensorLeftAdjunction_unit_app` and `TauCeti.tensorLeftAdjunction_counit_app`: the unit
  and counit of the adjunction associated to an exact pairing.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The evaluation of an exact pairing transported across an isomorphism in its left argument.

This is not a `simp` lemma: `CategoryTheory.exactPairingCongrLeft` is how a transported pairing
is *built*, so rewriting with it would unfold the evaluation of every such pairing and rob the
transported instance of its own normal form. -/
@[reassoc]
theorem exactPairingCongrLeft_evaluation {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') :
    @ExactPairing.evaluation C _ _ X Y (exactPairingCongrLeft i) = Y ◁ i.hom ≫ ε_ X' Y :=
  rfl

/-- The coevaluation of an exact pairing transported across an isomorphism in its left
argument. Not a `simp` lemma, for the reason given on
`TauCeti.exactPairingCongrLeft_evaluation`. -/
@[reassoc]
theorem exactPairingCongrLeft_coevaluation {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') :
    @ExactPairing.coevaluation C _ _ X Y (exactPairingCongrLeft i) = η_ X' Y ≫ i.inv ▷ Y :=
  rfl

variable (D Y : C) [ExactPairing D Y]

/-- The unit of the adjunction `tensorLeft Y ⊣ tensorLeft D` attached to an exact pairing
`ExactPairing D Y` inserts the coevaluation. -/
theorem tensorLeftAdjunction_unit_app (Z : C) :
    (tensorLeftAdjunction D Y).unit.app Z = (λ_ Z).inv ≫ η_ D Y ▷ Z ≫ (α_ D Y Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

/-- The counit of the adjunction `tensorLeft Y ⊣ tensorLeft D` attached to an exact pairing
`ExactPairing D Y` contracts the evaluation. -/
theorem tensorLeftAdjunction_counit_app (Z : C) :
    (tensorLeftAdjunction D Y).counit.app Z = (α_ Y D Z).inv ≫ ε_ D Y ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

end TauCeti
