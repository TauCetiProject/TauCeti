/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Right adjoint mates for explicit exact pairings

Mathlib's `CategoryTheory.rightAdjointMate` sends `f : X ⟶ Y` to `fᘁ : Yᘁ ⟶ Xᘁ`, where the duals
are the ambient `HasRightDual` choices. Several right duals are not of that form: the tensor
product pairing `ExactPairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ)`, the self-pairing of the unit, or a pairing
transported along an isomorphism. This file takes the exact pairings as explicit arguments
instead: for `pX : ExactPairing X X'` and `pY : ExactPairing Y Y'`, the mate of `f : X ⟶ Y` is
`ExactPairing.rightMate pX pY f : Y' ⟶ X'`.

A morphism into a right dual is determined by its composite with the evaluation
(`CategoryTheory.ExactPairing.rightHom_ext`), and the mate is characterized by
`CategoryTheory.ExactPairing.rightMate_comp_evaluation`. From these we compute the mates of the
monoidal structure morphisms with respect to the tensor product pairings: the mate of a
tensor product of morphisms is the reversed tensor product of their mates, and the mates of the
associator and the unitors are again an associator and unitors. These are the identities that
make the right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` monoidal.

## Main declarations

* `CategoryTheory.ExactPairing.rightHom_ext`: morphisms into a right dual agree once they agree
  after evaluation;
* `CategoryTheory.ExactPairing.rightMate`: the right adjoint mate with respect to explicit exact
  pairings, characterized by `CategoryTheory.ExactPairing.rightMate_comp_evaluation` and
  `CategoryTheory.ExactPairing.coevaluation_comp_rightMate`, with `rightMate_id` and
  `comp_rightMate`;
* `CategoryTheory.ExactPairing.rightMate_whiskerLeft`,
  `CategoryTheory.ExactPairing.rightMate_whiskerRight` and
  `CategoryTheory.ExactPairing.rightMate_tensorHom`: mates with respect to tensor product
  pairings;
* `CategoryTheory.ExactPairing.rightMate_associator_hom`,
  `CategoryTheory.ExactPairing.rightMate_leftUnitor_hom` and
  `CategoryTheory.ExactPairing.rightMate_rightUnitor_hom`: mates of the structure morphisms;
* `TauCeti.rightAdjointMate_eq_rightMate` and `TauCeti.rightDualIso_hom`: Mathlib's
  `rightAdjointMate` and `rightDualIso` as mates.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Two morphisms into a right dual `Y` of `X` agree as soon as they agree after evaluation
against `X`. -/
theorem rightHom_ext {X Y A : C} [ExactPairing X Y] {f g : A ⟶ Y}
    (h : f ▷ X ≫ ε_ X Y = g ▷ X ≫ ε_ X Y) : f = g := by
  -- Mathlib states the transposition formula for an ambient right dual; `⟨Y⟩` makes the given
  -- pairing the ambient one, and its right dual is `Y` by definition.
  have := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X A ⟨Y⟩
  rw [← cancel_mono (λ_ Y).inv]
  exact (this f).symm.trans ((congrArg _ h).trans (this g))

/-- The right adjoint mate `Y' ⟶ X'` of `f : X ⟶ Y`, with respect to explicitly given exact
pairings `(X, X')` and `(Y, Y')`. For the ambient right duals this is
`CategoryTheory.rightAdjointMate` (`TauCeti.rightAdjointMate_eq_rightMate`). -/
def rightMate {X X' Y Y' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    Y' ⟶ X' :=
  (ρ_ Y').inv ≫ Y' ◁ η_ X X' ≫ Y' ◁ f ▷ X' ≫ (α_ Y' Y X').inv ≫ ε_ Y Y' ▷ X' ≫ (λ_ X').hom

/-- The characteristic property of the right adjoint mate: evaluating it against `X` is the
same as evaluating against `Y` after applying `f`. -/
@[reassoc]
theorem rightMate_comp_evaluation {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    rightMate pX pY f ▷ X ≫ ε_ X X' = Y' ◁ f ≫ ε_ Y Y' :=
  calc
    _ = 𝟙 _ ⊗≫ Y' ◁ η_ X X' ▷ X ⊗≫ Y' ◁ f ▷ (X' ⊗ X) ⊗≫
        ((Y' ⊗ Y) ◁ ε_ X X' ≫ ε_ Y Y' ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      dsimp [rightMate]; rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ Y' ◁ η_ X X' ▷ X ⊗≫ Y' ◁ (f ▷ (X' ⊗ X) ≫ Y ◁ ε_ X X') ⊗≫ ε_ Y Y' := by
      monoidal
    _ = 𝟙 _ ⊗≫ Y' ◁ (η_ X X' ▷ X ⊗≫ X ◁ ε_ X X') ⊗≫ Y' ◁ f ⊗≫ ε_ Y Y' := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

/-- The dual characterization of the right adjoint mate: applying it after the coevaluation of
`(Y, Y')` is the same as applying `f` after the coevaluation of `(X, X')`. -/
@[reassoc]
theorem coevaluation_comp_rightMate {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    η_ Y Y' ≫ Y ◁ rightMate pX pY f = η_ X X' ≫ f ▷ X' := by
  -- `⟨X'⟩` and `⟨Y'⟩` make the given pairings ambient, so that Mathlib's formula for
  -- `rightAdjointMate` applies; the two mates agree by `rightHom_ext`.
  have h : rightMate pX pY f = @rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f :=
    rightHom_ext (X := X) (by
      rw [rightMate_comp_evaluation]
      exact (@rightAdjointMate_comp_evaluation C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f).symm)
  rw [h]
  exact @coevaluation_comp_rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The mate of an identity is an identity. -/
@[simp]
theorem rightMate_id {X X' : C} (p : ExactPairing X X') : rightMate p p (𝟙 X) = 𝟙 X' :=
  rightHom_ext (X := X) (by simp [rightMate_comp_evaluation])

/-- Taking mates reverses composition. -/
theorem comp_rightMate {X X' Y Y' Z Z' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y')
    (pZ : ExactPairing Z Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightMate pX pZ (f ≫ g) = rightMate pY pZ g ≫ rightMate pX pY f :=
  rightHom_ext (X := X) (by simp [rightMate_comp_evaluation, ← whisker_exchange_assoc])

/-- The mate of `f ▷ Z` with respect to the tensor product pairings is `Z' ◁ fᘁ`. -/
theorem rightMate_whiskerRight {X X' Y Y' Z Z' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (pZ : ExactPairing Z Z') (f : X ⟶ Y) :
    rightMate (tensor : ExactPairing (X ⊗ Z) (Z' ⊗ X')) (tensor : ExactPairing (Y ⊗ Z) (Z' ⊗ Y'))
      (f ▷ Z) = Z' ◁ rightMate pX pY f := by
  refine rightHom_ext (X := X ⊗ Z) ?_
  rw [rightMate_comp_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ Z' ◁ ((Y' ◁ f ≫ ε_ Y Y') ▷ Z) ⊗≫ ε_ Z Z' := by
      rw [tensor_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ Z' ◁ ((rightMate pX pY f ▷ X ≫ ε_ X X') ▷ Z) ⊗≫ ε_ Z Z' := by
      rw [rightMate_comp_evaluation]
    _ = _ := by
      rw [tensor_evaluation]; monoidal

/-- The mate of `Z ◁ f` with respect to the tensor product pairings is `fᘁ ▷ Z'`. -/
theorem rightMate_whiskerLeft {X X' Y Y' Z Z' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (pZ : ExactPairing Z Z') (f : X ⟶ Y) :
    rightMate (tensor : ExactPairing (Z ⊗ X) (X' ⊗ Z')) (tensor : ExactPairing (Z ⊗ Y) (Y' ⊗ Z'))
      (Z ◁ f) = rightMate pX pY f ▷ Z' := by
  refine rightHom_ext (X := Z ⊗ X) ?_
  rw [rightMate_comp_evaluation]
  -- Slide `f` past the evaluation of `(Z, Z')`, take its mate, and slide the mate back.
  calc
    _ = (α_ (Y' ⊗ Z') Z X).inv ≫ ((Y' ⊗ Z') ⊗ Z) ◁ f ≫
          ((α_ Y' Z' Z).hom ≫ Y' ◁ ε_ Z Z' ≫ (ρ_ Y').hom) ▷ Y ≫ ε_ Y Y' := by
      rw [tensor_evaluation]; monoidal
    _ = (α_ (Y' ⊗ Z') Z X).inv ≫ ((α_ Y' Z' Z).hom ≫ Y' ◁ ε_ Z Z' ≫ (ρ_ Y').hom) ▷ X ≫
          rightMate pX pY f ▷ X ≫ ε_ X X' := by
      rw [whisker_exchange_assoc, rightMate_comp_evaluation]
    _ = (α_ (Y' ⊗ Z') Z X).inv ≫
          ((α_ Y' Z' Z).hom ≫ (rightMate pX pY f ▷ (Z' ⊗ Z) ≫ X' ◁ ε_ Z Z') ≫ (ρ_ X').hom) ▷ X ≫
          ε_ X X' := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [tensor_evaluation]; monoidal

/-- The mate of a tensor product of morphisms with respect to the tensor product pairings is the
tensor product of their mates, in the reverse order. -/
theorem rightMate_tensorHom {X₁ X₁' X₂ X₂' Y₁ Y₁' Y₂ Y₂' : C} (pX₁ : ExactPairing X₁ X₁')
    (pX₂ : ExactPairing X₂ X₂') (pY₁ : ExactPairing Y₁ Y₁') (pY₂ : ExactPairing Y₂ Y₂')
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    rightMate (tensor : ExactPairing (X₁ ⊗ X₂) (X₂' ⊗ X₁'))
      (tensor : ExactPairing (Y₁ ⊗ Y₂) (Y₂' ⊗ Y₁')) (f ⊗ₘ g) =
        rightMate pX₂ pY₂ g ⊗ₘ rightMate pX₁ pY₁ f := by
  rw [tensorHom_def, comp_rightMate (pY := (tensor : ExactPairing (Y₁ ⊗ X₂) (X₂' ⊗ Y₁'))),
    rightMate_whiskerLeft pX₂ pY₂ pY₁, rightMate_whiskerRight pX₁ pY₁ pX₂, ← tensorHom_def]

/-- The mate of the associator of `X`, `Y`, `Z` with respect to the tensor product pairings is the
associator of their duals. -/
theorem rightMate_associator_hom {X X' Y Y' Z Z' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (pZ : ExactPairing Z Z') :
    rightMate (tensor : ExactPairing ((X ⊗ Y) ⊗ Z) (Z' ⊗ Y' ⊗ X'))
      (tensor : ExactPairing (X ⊗ Y ⊗ Z) ((Z' ⊗ Y') ⊗ X')) (α_ X Y Z).hom =
        (α_ Z' Y' X').hom := by
  refine rightHom_ext (X := (X ⊗ Y) ⊗ Z) ?_
  rw [rightMate_comp_evaluation]
  simp only [tensor_evaluation]
  monoidal

/-- The mate of the left unitor of `X` with respect to the tensor product of the self-pairing
of the unit with `(X, X')` is the inverse right unitor of `X'`. -/
theorem rightMate_leftUnitor_hom {X X' : C} (pX : ExactPairing X X') :
    rightMate (tensor : ExactPairing (𝟙_ C ⊗ X) (X' ⊗ 𝟙_ C)) pX (λ_ X).hom = (ρ_ X').inv := by
  refine rightHom_ext (X := 𝟙_ C ⊗ X) ?_
  rw [rightMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

/-- The mate of the right unitor of `X` with respect to the tensor product of `(X, X')` with the
self-pairing of the unit is the inverse left unitor of `X'`. -/
theorem rightMate_rightUnitor_hom {X X' : C} (pX : ExactPairing X X') :
    rightMate (tensor : ExactPairing (X ⊗ 𝟙_ C) (𝟙_ C ⊗ X')) pX (ρ_ X).hom = (λ_ X').inv := by
  refine rightHom_ext (X := X ⊗ 𝟙_ C) ?_
  rw [rightMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

end CategoryTheory.ExactPairing

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Mathlib's right adjoint mate is the mate with respect to the ambient right duals. -/
theorem rightAdjointMate_eq_rightMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    fᘁ = ExactPairing.rightMate HasRightDual.exact HasRightDual.exact f :=
  ExactPairing.rightHom_ext (X := X) (by
    rw [rightAdjointMate_comp_evaluation, ExactPairing.rightMate_comp_evaluation])

/-- The comparison `rightDualIso p₁ p₂ : Y₁ ≅ Y₂` between two right duals of `X` is the mate of
the identity of `X`. -/
theorem rightDualIso_hom {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).hom = ExactPairing.rightMate p₂ p₁ (𝟙 X) :=
  ExactPairing.rightHom_ext (X := X) (by
    rw [ExactPairing.rightMate_comp_evaluation]
    -- `rightDualIso` is defined as the mate of `𝟙 X` with `p₂` and `p₁` made ambient.
    exact @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X))

end TauCeti
