/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The Drinfeld isomorphism

In a braided monoidal category, an object `X` with a right dual whose right dual also exists
is canonically isomorphic to its double right dual. The Drinfeld isomorphism compares two
right duals of `Xᘁ`: the chosen double dual, and `X` with the braided swapped pairing.
Its evaluation and coevaluation identities and naturality are recorded here.

This is only a natural isomorphism at this level of generality: an arbitrary braiding does
not make it monoidal. In a symmetric rigid category it is the underlying isomorphism of
the canonical pivotal structure.

The construction uses Mathlib's `CategoryTheory.ExactPairing.rightDualIso` and
`CategoryTheory.BraidedCategory.exactPairing_swap`. The name `drinfeldIso` follows
J. McKoen's Mathlib pull request #42192.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.9
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The Drinfeld isomorphism identifies `X` with its double right dual by comparing
its braided pairing with `Xᘁ` to the chosen right pairing of `Xᘁ`. -/
def drinfeldIso (X : C) [HasRightDual X] [HasRightDual Xᘁ] : X ≅ ((Xᘁ : C)ᘁ : C) :=
  rightDualIso (exactPairing_swap X Xᘁ) HasRightDual.exact

variable (X : C) [HasRightDual X] [HasRightDual Xᘁ]

/-- Evaluating the Drinfeld isomorphism against the right dual is braided evaluation. -/
@[reassoc (attr := simp)]
theorem drinfeldIso_hom_comp_evaluation :
    (drinfeldIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [drinfeldIso, rightDualIso_hom, rightMate_comp_evaluation,
    exactPairing_swap_evaluation]
  simp

/-- The Drinfeld isomorphism inserts the coevaluation of `Xᘁ` and contracts `X`
against `Xᘁ` using the braiding. -/
theorem drinfeldIso_hom_eq :
    (drinfeldIso X).hom = (ρ_ X).inv ≫ X ◁ η_ Xᘁ Xᘁᘁ ≫ (α_ X Xᘁ Xᘁᘁ).inv ≫
      (β_ X Xᘁ).hom ▷ ((Xᘁ : C)ᘁ : C) ≫ ε_ X Xᘁ ▷ ((Xᘁ : C)ᘁ : C) ≫
        (λ_ Xᘁᘁ).hom := by
  calc
    (drinfeldIso X).hom =
        tensorRightHomEquiv X Xᘁ Xᘁᘁ (𝟙_ C)
          ((drinfeldIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ) ≫ (λ_ Xᘁᘁ).hom := by
      rw [tensorRightHomEquiv_whiskerRight_comp_evaluation]
      simp
    _ = _ := by
      rw [drinfeldIso_hom_comp_evaluation]
      simp [tensorRightHomEquiv]

/-- The inverse Drinfeld isomorphism transforms braided evaluation into double-dual
evaluation. -/
@[reassoc (attr := simp)]
theorem drinfeldIso_inv_comp_evaluation :
    (β_ Xᘁᘁ Xᘁ).hom ≫ Xᘁ ◁ (drinfeldIso X).inv ≫ ε_ X Xᘁ = ε_ Xᘁ Xᘁᘁ := by
  rw [← braiding_naturality_left_assoc, ← drinfeldIso_hom_comp_evaluation,
    ← comp_whiskerRight_assoc]
  simp

/-- Coevaluation into the double dual is obtained by applying the Drinfeld isomorphism
after the braided swapped coevaluation. -/
@[reassoc (attr := simp)]
theorem coevaluation_comp_drinfeldIso_hom :
    η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ (drinfeldIso X).hom = η_ Xᘁ Xᘁᘁ := by
  rw [drinfeldIso, rightDualIso_hom]
  simpa [exactPairing_swap_coevaluation] using
    coevaluation_comp_rightMate HasRightDual.exact (exactPairing_swap X Xᘁ) (𝟙 Xᘁ)

/-- The inverse Drinfeld isomorphism transforms double-dual coevaluation into the
braided swapped coevaluation. -/
@[reassoc (attr := simp)]
theorem coevaluation_comp_drinfeldIso_inv :
    η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ (drinfeldIso X).inv = η_ X Xᘁ ≫ (β_ Xᘁ X).inv := by
  rw [← coevaluation_comp_drinfeldIso_hom]
  simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id,
    Category.comp_id]

/-- The Drinfeld isomorphism is natural with respect to double right adjoint mates. -/
@[reassoc]
theorem drinfeldIso_hom_naturality {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual Xᘁ] [HasRightDual Yᘁ] (f : X ⟶ Y) :
    f ≫ (drinfeldIso Y).hom = (drinfeldIso X).hom ≫ fᘁᘁ := by
  apply rightHom_ext (X := Yᘁ)
  simp only [comp_whiskerRight, Category.assoc, drinfeldIso_hom_comp_evaluation,
    rightAdjointMate_comp_evaluation]
  rw [braiding_naturality_left_assoc, ← whisker_exchange_assoc,
    drinfeldIso_hom_comp_evaluation, braiding_naturality_right_assoc,
    rightAdjointMate_comp_evaluation]

/-- Naturality of the inverse Drinfeld isomorphism. -/
@[reassoc]
theorem drinfeldIso_inv_naturality {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual Xᘁ] [HasRightDual Yᘁ] (f : X ⟶ Y) :
    fᘁᘁ ≫ (drinfeldIso Y).inv = (drinfeldIso X).inv ≫ f := by
  rw [← cancel_epi (drinfeldIso X).hom]
  rw [← drinfeldIso_hom_naturality_assoc]
  simp

end TauCeti
