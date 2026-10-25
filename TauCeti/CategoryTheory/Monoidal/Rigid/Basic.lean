/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Exact pairings in rigid monoidal categories

This file records evaluation and coevaluation formulas for the self-pairing of the unit, for
transported exact pairings, and for the adjunction associated to an exact pairing. It also
computes the loop obtained by closing up a tensor product `f ⊗ₘ g` of endomorphisms with the
tensor product pairings: in string diagrams, the loop of `f` sits inside the loop of `g`.

## Main declarations

* `TauCeti.ExactPairing.unit_evaluation` and `TauCeti.ExactPairing.unit_coevaluation`: the
  evaluation and coevaluation of Mathlib's self-pairing of the unit;
* `TauCeti.exactPairingCongrLeft_evaluation` and
  `TauCeti.exactPairingCongrLeft_coevaluation`: transport in the left argument;
* `TauCeti.exactPairingCongrRight_evaluation` and
  `TauCeti.exactPairingCongrRight_coevaluation`: transport in the right argument;
* `TauCeti.exactPairingCongr_evaluation` and
  `TauCeti.exactPairingCongr_coevaluation`: simultaneous transport in both arguments;
* `TauCeti.ExactPairing.coevaluation_whiskerLeft_tensorHom_evaluation` and
  `TauCeti.ExactPairing.coevaluation_tensorHom_whiskerRight_evaluation`: closing up `f ⊗ₘ g`
  with the tensor product pairings nests the loop of one factor inside the loop of the other;
* `TauCeti.tensorLeftAdjunction_unit_app` and `TauCeti.tensorLeftAdjunction_counit_app`: the unit
  and counit of the adjunction associated to an exact pairing;
* `TauCeti.ExactPairing.homUnitEquiv`: for an exact pairing of `X` and `Y`, morphisms `X ⟶ 𝟙_ C`
  correspond to morphisms `𝟙_ C ⟶ Y`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ExactPairing

/-- The evaluation of the canonical self-pairing of the unit is the right unitor. -/
@[simp]
theorem unit_evaluation : ε_ (𝟙_ C) (𝟙_ C) = (ρ_ (𝟙_ C)).hom :=
  (rfl)

/-- The coevaluation of the canonical self-pairing of the unit is the inverse right unitor. -/
@[simp]
theorem unit_coevaluation : η_ (𝟙_ C) (𝟙_ C) = (ρ_ (𝟙_ C)).inv :=
  (rfl)

end ExactPairing

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

/-- The evaluation of an exact pairing transported across an isomorphism in its right argument. -/
@[reassoc]
theorem exactPairingCongrRight_evaluation {X Y Y' : C} [ExactPairing X Y'] (j : Y ≅ Y') :
    @ExactPairing.evaluation C _ _ X Y (exactPairingCongrRight j) =
      j.hom ▷ X ≫ ε_ X Y' :=
  rfl

/-- The coevaluation of an exact pairing transported across an isomorphism in its right argument. -/
@[reassoc]
theorem exactPairingCongrRight_coevaluation {X Y Y' : C} [ExactPairing X Y'] (j : Y ≅ Y') :
    @ExactPairing.coevaluation C _ _ X Y (exactPairingCongrRight j) =
      η_ X Y' ≫ X ◁ j.inv :=
  rfl

/-- The evaluation of an exact pairing transported across isomorphisms in both arguments. -/
@[reassoc]
theorem exactPairingCongr_evaluation {X X' Y Y' : C} [ExactPairing X' Y']
    (i : X ≅ X') (j : Y ≅ Y') :
    @ExactPairing.evaluation C _ _ X Y (exactPairingCongr i j) =
      Y ◁ i.hom ≫ j.hom ▷ X' ≫ ε_ X' Y' := by
  rw [@exactPairingCongrLeft_evaluation C _ _ X X' Y (exactPairingCongrRight j) i,
    exactPairingCongrRight_evaluation]

/-- The coevaluation of an exact pairing transported across isomorphisms in both arguments. -/
@[reassoc]
theorem exactPairingCongr_coevaluation {X X' Y Y' : C} [ExactPairing X' Y']
    (i : X ≅ X') (j : Y ≅ Y') :
    @ExactPairing.coevaluation C _ _ X Y (exactPairingCongr i j) =
      η_ X' Y' ≫ X' ◁ j.inv ≫ i.inv ▷ Y := by
  rw [@exactPairingCongrLeft_coevaluation C _ _ X X' Y (exactPairingCongrRight j) i,
    exactPairingCongrRight_coevaluation]
  simp only [Category.assoc]

namespace ExactPairing

/-- Closing up `f ⊗ₘ g` between the coevaluation of the tensor product pairing of `(B, Y)` and
`(A, X)` and the evaluation of the tensor product pairing of `(X, A)` and `(Y, B)`: the result is
the loop of `g`, with the loop `η_ A X ≫ A ◁ f ≫ ε_ X A` of `f` acting on `Y` from the left,
inside it. -/
theorem coevaluation_whiskerLeft_tensorHom_evaluation {A B X Y : C}
    [ExactPairing A X] [ExactPairing X A] [ExactPairing B Y] [ExactPairing Y B]
    (f : X ⟶ X) (g : Y ⟶ Y) :
    η_ (B ⊗ A) (X ⊗ Y) ≫ (B ⊗ A) ◁ (f ⊗ₘ g) ≫ ε_ (X ⊗ Y) (B ⊗ A) =
      η_ B Y ≫ B ◁ ((λ_ Y).inv ≫ (η_ A X ≫ A ◁ f ≫ ε_ X A) ▷ Y ≫ (λ_ Y).hom ≫ g) ≫
        ε_ Y B := by
  calc _ = η_ B Y ⊗≫ B ◁ (η_ A X ▷ Y ≫ (A ◁ f) ▷ Y ≫ (A ⊗ X) ◁ g ≫ ε_ X A ▷ Y) ⊗≫
          ε_ Y B := by
        rw [CategoryTheory.ExactPairing.tensor_coevaluation,
          CategoryTheory.ExactPairing.tensor_evaluation, tensorHom_def]
        monoidal
    -- The inner loop closes before `g` is applied.
    _ = η_ B Y ⊗≫ B ◁ (η_ A X ▷ Y ≫ (A ◁ f) ▷ Y ≫ ε_ X A ▷ Y ≫ 𝟙_ C ◁ g) ⊗≫ ε_ Y B := by
        rw [whisker_exchange]
    _ = _ := by monoidal

/-- Closing up `f ⊗ₘ g` between the coevaluation of the tensor product pairing of `(X, A)` and
`(Y, B)` and the evaluation of the tensor product pairing of `(B, Y)` and `(A, X)`: the result is
the loop of `f`, with the loop `η_ Y B ≫ g ▷ B ≫ ε_ B Y` of `g` acting on `X` from the right,
inside it. -/
theorem coevaluation_tensorHom_whiskerRight_evaluation {A B X Y : C}
    [ExactPairing A X] [ExactPairing X A] [ExactPairing B Y] [ExactPairing Y B]
    (f : X ⟶ X) (g : Y ⟶ Y) :
    η_ (X ⊗ Y) (B ⊗ A) ≫ (f ⊗ₘ g) ▷ (B ⊗ A) ≫ ε_ (B ⊗ A) (X ⊗ Y) =
      η_ X A ≫ (f ≫ (ρ_ X).inv ≫ X ◁ (η_ Y B ≫ g ▷ B ≫ ε_ B Y) ≫ (ρ_ X).hom) ▷ A ≫
        ε_ A X := by
  calc _ = η_ X A ⊗≫ (X ◁ η_ Y B ≫ f ▷ (Y ⊗ B) ≫ X ◁ g ▷ B ≫ X ◁ ε_ B Y) ▷ A ⊗≫
          ε_ A X := by
        rw [CategoryTheory.ExactPairing.tensor_coevaluation,
          CategoryTheory.ExactPairing.tensor_evaluation, tensorHom_def]
        monoidal
    -- The inner loop opens after `f` is applied.
    _ = η_ X A ⊗≫ (f ▷ 𝟙_ C ≫ X ◁ η_ Y B ≫ X ◁ g ▷ B ≫ X ◁ ε_ B Y) ▷ A ⊗≫ ε_ A X := by
        rw [whisker_exchange_assoc]
    _ = _ := by monoidal

end ExactPairing

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

namespace ExactPairing

variable (X Y : C) [ExactPairing X Y]

/-- For an exact pairing of `X` and `Y`, morphisms `X ⟶ 𝟙_ C` correspond to morphisms
`𝟙_ C ⟶ Y`: a functional `φ` on `X` goes to the coevaluation followed by `φ`, and a morphism
`s : 𝟙_ C ⟶ Y` goes to evaluation against `s`. It is Mathlib's
`CategoryTheory.tensorRightHomEquiv` with both outer objects the unit, up to the unitors. -/
def homUnitEquiv : (X ⟶ 𝟙_ C) ≃ (𝟙_ C ⟶ Y) :=
  ((λ_ X).homCongr (Iso.refl _)).symm.trans
    ((tensorRightHomEquiv (𝟙_ C) X Y (𝟙_ C)).trans ((Iso.refl _).homCongr (λ_ Y)))

/-- The morphism `𝟙_ C ⟶ Y` of a functional `φ : X ⟶ 𝟙_ C` applies `φ` after the
coevaluation. -/
@[simp]
theorem homUnitEquiv_apply (φ : X ⟶ 𝟙_ C) :
    homUnitEquiv X Y φ = η_ X Y ≫ φ ▷ Y ≫ (λ_ Y).hom := by
  simp [homUnitEquiv, tensorRightHomEquiv, unitors_equal, unitors_inv_equal]

/-- The functional `X ⟶ 𝟙_ C` of a morphism `s : 𝟙_ C ⟶ Y` is evaluation against `s`. -/
@[simp]
theorem homUnitEquiv_symm_apply (s : 𝟙_ C ⟶ Y) :
    (homUnitEquiv X Y).symm s = (λ_ X).inv ≫ s ▷ X ≫ ε_ X Y := by
  simp [homUnitEquiv, tensorRightHomEquiv, unitors_equal, unitors_inv_equal]

end ExactPairing

end TauCeti
