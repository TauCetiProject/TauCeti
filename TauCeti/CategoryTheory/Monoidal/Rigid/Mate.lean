/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Adjoint mates for explicit exact pairings

Mathlib's `CategoryTheory.rightAdjointMate` sends `f : X ⟶ Y` to `fᘁ : Yᘁ ⟶ Xᘁ`, where the duals
are the ambient `HasRightDual` choices. Several right duals are not of that form: the tensor
product pairing `ExactPairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ)`, the self-pairing of the unit, or a pairing
transported along an isomorphism. This file takes the exact pairings as explicit arguments
instead: for `pX : ExactPairing X X'` and `pY : ExactPairing Y Y'`, the mate of `f : X ⟶ Y` is
`ExactPairing.rightMate pX pY f : Y' ⟶ X'`. This is Mathlib's `rightAdjointMate` with the given
pairings made ambient, and its basic properties are Mathlib's; what the definition adds is the
type `Y' ⟶ X'`, so that rewriting sees `X'` and `Y'` rather than projections out of `HasRightDual`
records.

A morphism into a right dual is determined by its composite with the evaluation
(`CategoryTheory.ExactPairing.rightHom_ext`), and the mate is characterized by
`CategoryTheory.ExactPairing.rightMate_comp_evaluation`. From these we compute the mates of the
monoidal structure morphisms with respect to the tensor product pairings: the mate of a
tensor product of morphisms is the reversed tensor product of their mates, and the mates of the
associator and the unitors are again an associator and unitors. These are the identities that
make the right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` monoidal.

The same is done for left duals: for `pX : ExactPairing X' X` and `pY : ExactPairing Y' Y`, the
left mate of `f : X ⟶ Y` is `ExactPairing.leftMate pX pY f : Y' ⟶ X'`, Mathlib's
`leftAdjointMate` with the given pairings made ambient. A morphism into a left dual is
determined by its composite with the evaluation (`CategoryTheory.ExactPairing.leftDualHom_ext`),
and the left mates of tensor products and of the structure morphisms are computed in the same
way. These are the identities that make the left dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` monoidal.

Taking a left adjoint mate and then a right adjoint mate, or conversely, recovers the original
morphism.

## Main declarations

* `CategoryTheory.ExactPairing.rightHom_ext`: morphisms into a right dual agree once they agree
  after evaluation, and `CategoryTheory.ExactPairing.leftHom_ext`: morphisms out of a left member
  agree once they agree after coevaluation;
* `CategoryTheory.leftAdjointMate_rightAdjointMate` and
  `CategoryTheory.rightAdjointMate_leftAdjointMate`: taking the opposite-handed mate recovers the
  original morphism, so `CategoryTheory.rightAdjointMate_injective`;
* `CategoryTheory.Iso.rightAdjointMate`: the isomorphism `Yᘁ ≅ Xᘁ` induced by `X ≅ Y`;
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
* `CategoryTheory.ExactPairing.rightMate_evaluation` and
  `CategoryTheory.ExactPairing.rightMate_coevaluation`: the mate of an evaluation is a
  coevaluation, and conversely;
* `TauCeti.rightAdjointMate_eq_rightMate`, `CategoryTheory.ExactPairing.rightDualIso_hom` and
  `CategoryTheory.ExactPairing.rightDualIso_inv`: Mathlib's `rightAdjointMate` and `rightDualIso`
  as mates, with the evaluation identities `rightDualIso_hom_whiskerRight_evaluation` and
  `rightDualIso_inv_whiskerRight_evaluation`;
* `CategoryTheory.ExactPairing.leftDualHom_ext`: morphisms into a left dual agree once they agree
  after evaluation;
* `CategoryTheory.ExactPairing.leftMate`: the left adjoint mate with respect to explicit exact
  pairings, characterized by `CategoryTheory.ExactPairing.leftMate_comp_evaluation` and
  `CategoryTheory.ExactPairing.coevaluation_comp_leftMate`, with `leftMate_id`, `comp_leftMate`,
  the tensor product formulas `leftMate_whiskerLeft`, `leftMate_whiskerRight` and
  `leftMate_tensorHom`, and the structure-morphism formulas `leftMate_associator_hom`,
  `leftMate_leftUnitor_hom` and `leftMate_rightUnitor_hom`;
* `TauCeti.leftAdjointMate_eq_leftMate`, `CategoryTheory.ExactPairing.leftDualIso_hom` and
  `CategoryTheory.ExactPairing.leftDualIso_inv`: Mathlib's `leftAdjointMate` and `leftDualIso`
  as left mates;
* `CategoryTheory.ExactPairing.leftMate_rightDualIso_hom` and
  `CategoryTheory.ExactPairing.rightMate_leftDualIso_hom`: the opposite-handed mate of the
  comparison between two duals is an identity.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
* [leanprover-community/mathlib4#42145](https://github.com/leanprover-community/mathlib4/pull/42145),
  for the explicit-pairing form of `CategoryTheory.ExactPairing.leftHom_ext` and the two
  mate-inverse lemmas
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

/-- Two morphisms out of the left member `X` of an exact pairing agree as soon as they agree
after the coevaluation of the pairing. -/
theorem leftHom_ext {X Y A : C} [ExactPairing X Y] {f g : X ⟶ A}
    (h : η_ X Y ≫ f ▷ Y = η_ X Y ≫ g ▷ Y) : f = g := by
  simpa using congrArg (tensorRightHomEquiv (𝟙_ C) X Y A).symm h

/-- The right adjoint mate `Y' ⟶ X'` of `f : X ⟶ Y`, with respect to explicitly given exact
pairings `(X, X')` and `(Y, Y')`: Mathlib's `CategoryTheory.rightAdjointMate` with the given
pairings made ambient. Stating it with the type `Y' ⟶ X'` keeps the duals `X'` and `Y'` visible
to rewriting: as a term `@rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f`, its source and target are the
projections `HasRightDual.rightDual ⟨Y'⟩` and `HasRightDual.rightDual ⟨X'⟩`, and Mathlib's lemmas
about it do not rewrite against the evaluation `ε_ X X'` of the given pairing. -/
def rightMate {X X' Y Y' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    Y' ⟶ X' :=
  @rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The characteristic property of the right adjoint mate: evaluating it against `X` is the
same as evaluating against `Y` after applying `f`. -/
@[reassoc]
theorem rightMate_comp_evaluation {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    rightMate pX pY f ▷ X ≫ ε_ X X' = Y' ◁ f ≫ ε_ Y Y' :=
  @rightAdjointMate_comp_evaluation C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The dual characterization of the right adjoint mate: applying it after the coevaluation of
`(Y, Y')` is the same as applying `f` after the coevaluation of `(X, X')`. -/
@[reassoc]
theorem coevaluation_comp_rightMate {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    η_ Y Y' ≫ Y ◁ rightMate pX pY f = η_ X X' ≫ f ▷ X' :=
  @coevaluation_comp_rightAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The mate of an identity is an identity. -/
@[simp]
theorem rightMate_id {X X' : C} (p : ExactPairing X X') : rightMate p p (𝟙 X) = 𝟙 X' :=
  @rightAdjointMate_id C _ _ X ⟨X'⟩

/-- Taking mates reverses composition. -/
theorem comp_rightMate {X X' Y Y' Z Z' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y')
    (pZ : ExactPairing Z Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightMate pX pZ (f ≫ g) = rightMate pY pZ g ≫ rightMate pX pY f :=
  @comp_rightAdjointMate C _ _ X Y Z ⟨X'⟩ ⟨Y'⟩ ⟨Z'⟩ f g

/-- The mate of `f ▷ Z` with respect to the tensor product pairings is `Z' ◁ fᘁ`. -/
@[simp]
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
@[simp]
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
@[simp]
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
@[simp]
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
@[simp]
theorem rightMate_leftUnitor_hom {X X' : C} (pX : ExactPairing X X') :
    rightMate (tensor : ExactPairing (𝟙_ C ⊗ X) (X' ⊗ 𝟙_ C)) pX (λ_ X).hom = (ρ_ X').inv := by
  refine rightHom_ext (X := 𝟙_ C ⊗ X) ?_
  rw [rightMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

/-- The mate of the right unitor of `X` with respect to the tensor product of `(X, X')` with the
self-pairing of the unit is the inverse left unitor of `X'`. -/
@[simp]
theorem rightMate_rightUnitor_hom {X X' : C} (pX : ExactPairing X X') :
    rightMate (tensor : ExactPairing (X ⊗ 𝟙_ C) (𝟙_ C ⊗ X')) pX (ρ_ X).hom = (λ_ X').inv := by
  refine rightHom_ext (X := X ⊗ 𝟙_ C) ?_
  rw [rightMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

/-- The comparison `rightDualIso p₁ p₂ : Y₁ ≅ Y₂` between two right duals of `X` is the mate of
the identity of `X`. -/
theorem rightDualIso_hom {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).hom = rightMate p₂ p₁ (𝟙 X) :=
  rightHom_ext (X := X) (by
    rw [rightMate_comp_evaluation]
    -- `rightDualIso` is defined as the mate of `𝟙 X` with `p₂` and `p₁` made ambient.
    exact @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X))

/-- The inverse of the comparison `rightDualIso p₁ p₂ : Y₁ ≅ Y₂` is the mate of the identity of
`X` taken in the other direction. -/
theorem rightDualIso_inv {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).inv = rightMate p₁ p₂ (𝟙 X) :=
  -- `(rightDualIso p₁ p₂).inv` and `(rightDualIso p₂ p₁).hom` are the same mate of `𝟙 X`.
  rightDualIso_hom p₂ p₁

/-- Through the comparison `rightDualIso p₁ p₂ : Y₁ ≅ Y₂`, the evaluation of `p₂` is the
evaluation of `p₁`. -/
@[reassoc]
theorem rightDualIso_hom_whiskerRight_evaluation {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) : (rightDualIso p₁ p₂).hom ▷ X ≫ ε_ X Y₂ = ε_ X Y₁ := by
  rw [rightDualIso_hom, rightMate_comp_evaluation, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- Through the inverse comparison `(rightDualIso p₁ p₂).inv : Y₂ ⟶ Y₁`, the evaluation of `p₁` is
the evaluation of `p₂`. -/
@[reassoc]
theorem rightDualIso_inv_whiskerRight_evaluation {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) : (rightDualIso p₁ p₂).inv ▷ X ≫ ε_ X Y₁ = ε_ X Y₂ := by
  rw [rightDualIso_inv, ← rightDualIso_hom, rightDualIso_hom_whiskerRight_evaluation]

/-- The mate of the evaluation `ε_ X X' : X' ⊗ X ⟶ 𝟙_ C`, taken with respect to the tensor product
pairing of `(X', X'')` with `(X, X')` and the self-pairing of the unit, is the coevaluation
`η_ X' X'' : 𝟙_ C ⟶ X' ⊗ X''`. -/
theorem rightMate_evaluation {X X' X'' : C} (pX : ExactPairing X X') (pX' : ExactPairing X' X'') :
    rightMate (tensor : ExactPairing (X' ⊗ X) (X' ⊗ X'')) exactPairingUnit (ε_ X X') =
      η_ X' X'' := by
  refine rightHom_ext (X := X' ⊗ X) ?_
  rw [rightMate_comp_evaluation, tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ (η_ X' X'' ▷ X' ⊗≫ X' ◁ ε_ X' X'') ▷ X ⊗≫ ε_ X X' := by
      rw [evaluation_coevaluation'']; monoidal
    _ = _ := by monoidal

/-- The mate of the coevaluation `η_ X X' : 𝟙_ C ⟶ X ⊗ X'`, taken with respect to the self-pairing
of the unit and the tensor product pairing of `(X, X')` with `(X', X'')`, is the evaluation
`ε_ X' X'' : X'' ⊗ X' ⟶ 𝟙_ C`. -/
theorem rightMate_coevaluation {X X' X'' : C} (pX : ExactPairing X X')
    (pX' : ExactPairing X' X'') :
    rightMate exactPairingUnit (tensor : ExactPairing (X ⊗ X') (X'' ⊗ X')) (η_ X X') =
      ε_ X' X'' := by
  refine rightHom_ext (X := 𝟙_ C) ?_
  rw [rightMate_comp_evaluation, tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ X'' ◁ (X' ◁ η_ X X' ⊗≫ ε_ X X' ▷ X') ⊗≫ ε_ X' X'' := by monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

/-! ### Left adjoint mates -/

/-- Two morphisms into the left member `X` of an exact pairing `(X, Y)`, that is into a left dual
of `Y`, agree as soon as they agree after evaluation against `Y`. -/
theorem leftDualHom_ext {X Y A : C} [ExactPairing X Y] {f g : A ⟶ X}
    (h : Y ◁ f ≫ ε_ X Y = Y ◁ g ≫ ε_ X Y) : f = g := by
  -- Mathlib states the transposition formula for an ambient left dual; `⟨X⟩` makes the given
  -- pairing the ambient one, and its left dual is `X` by definition.
  have := @tensorLeftHomEquiv_whiskerLeft_comp_evaluation C _ _ A Y ⟨X⟩
  rw [← cancel_mono (ρ_ X).inv]
  exact (this f).symm.trans ((congrArg _ h).trans (this g))

/-- The left adjoint mate `Y' ⟶ X'` of `f : X ⟶ Y`, with respect to explicitly given exact
pairings `(X', X)` and `(Y', Y)`: Mathlib's `CategoryTheory.leftAdjointMate` with the given
pairings made ambient. As for `CategoryTheory.ExactPairing.rightMate`, the type `Y' ⟶ X'` keeps
the left duals `X'` and `Y'` visible to rewriting. -/
def leftMate {X X' Y Y' : C} (pX : ExactPairing X' X) (pY : ExactPairing Y' Y) (f : X ⟶ Y) :
    Y' ⟶ X' :=
  @leftAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The characteristic property of the left adjoint mate: evaluating it against `X` is the
same as evaluating against `Y` after applying `f`. -/
@[reassoc]
theorem leftMate_comp_evaluation {X X' Y Y' : C} (pX : ExactPairing X' X)
    (pY : ExactPairing Y' Y) (f : X ⟶ Y) :
    X ◁ leftMate pX pY f ≫ ε_ X' X = f ▷ Y' ≫ ε_ Y' Y :=
  @leftAdjointMate_comp_evaluation C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The dual characterization of the left adjoint mate: applying it after the coevaluation of
`(Y', Y)` is the same as applying `f` after the coevaluation of `(X', X)`. -/
@[reassoc]
theorem coevaluation_comp_leftMate {X X' Y Y' : C} (pX : ExactPairing X' X)
    (pY : ExactPairing Y' Y) (f : X ⟶ Y) :
    η_ Y' Y ≫ leftMate pX pY f ▷ Y = η_ X' X ≫ X' ◁ f :=
  @coevaluation_comp_leftAdjointMate C _ _ X Y ⟨X'⟩ ⟨Y'⟩ f

/-- The left mate of an identity is an identity. -/
@[simp]
theorem leftMate_id {X X' : C} (p : ExactPairing X' X) : leftMate p p (𝟙 X) = 𝟙 X' :=
  @leftAdjointMate_id C _ _ X ⟨X'⟩

/-- Taking left mates reverses composition. -/
theorem comp_leftMate {X X' Y Y' Z Z' : C} (pX : ExactPairing X' X) (pY : ExactPairing Y' Y)
    (pZ : ExactPairing Z' Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftMate pX pZ (f ≫ g) = leftMate pY pZ g ≫ leftMate pX pY f :=
  @comp_leftAdjointMate C _ _ X Y Z ⟨X'⟩ ⟨Y'⟩ ⟨Z'⟩ f g

/-- The left mate of `Z ◁ f` with respect to the tensor product pairings is `ᘁf ▷ Z'`. -/
@[simp]
theorem leftMate_whiskerLeft {X X' Y Y' Z Z' : C} (pX : ExactPairing X' X)
    (pY : ExactPairing Y' Y) (pZ : ExactPairing Z' Z) (f : X ⟶ Y) :
    leftMate (tensor : ExactPairing (X' ⊗ Z') (Z ⊗ X)) (tensor : ExactPairing (Y' ⊗ Z') (Z ⊗ Y))
      (Z ◁ f) = leftMate pX pY f ▷ Z' := by
  refine leftDualHom_ext (Y := Z ⊗ X) ?_
  rw [leftMate_comp_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ Z ◁ ((f ▷ Y' ≫ ε_ Y' Y) ▷ Z') ⊗≫ ε_ Z' Z := by
      rw [tensor_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ Z ◁ ((X ◁ leftMate pX pY f ≫ ε_ X' X) ▷ Z') ⊗≫ ε_ Z' Z := by
      rw [leftMate_comp_evaluation]
    _ = _ := by
      rw [tensor_evaluation]; monoidal

/-- The left mate of `f ▷ Z` with respect to the tensor product pairings is `Z' ◁ ᘁf`. -/
@[simp]
theorem leftMate_whiskerRight {X X' Y Y' Z Z' : C} (pX : ExactPairing X' X)
    (pY : ExactPairing Y' Y) (pZ : ExactPairing Z' Z) (f : X ⟶ Y) :
    leftMate (tensor : ExactPairing (Z' ⊗ X') (X ⊗ Z)) (tensor : ExactPairing (Z' ⊗ Y') (Y ⊗ Z))
      (f ▷ Z) = Z' ◁ leftMate pX pY f := by
  refine leftDualHom_ext (Y := X ⊗ Z) ?_
  rw [leftMate_comp_evaluation]
  -- Slide `f` past the evaluation of `(Z', Z)`, take its left mate, and slide the mate back.
  calc
    _ = (α_ X Z (Z' ⊗ Y')).hom ≫ f ▷ (Z ⊗ Z' ⊗ Y') ≫
          Y ◁ ((α_ Z Z' Y').inv ≫ ε_ Z' Z ▷ Y' ≫ (λ_ Y').hom) ≫ ε_ Y' Y := by
      rw [tensor_evaluation]; monoidal
    _ = (α_ X Z (Z' ⊗ Y')).hom ≫ X ◁ ((α_ Z Z' Y').inv ≫ ε_ Z' Z ▷ Y' ≫ (λ_ Y').hom) ≫
          X ◁ leftMate pX pY f ≫ ε_ X' X := by
      rw [← whisker_exchange_assoc, leftMate_comp_evaluation]
    _ = (α_ X Z (Z' ⊗ Y')).hom ≫
          X ◁ ((α_ Z Z' Y').inv ≫ ((Z ⊗ Z') ◁ leftMate pX pY f ≫ ε_ Z' Z ▷ X') ≫ (λ_ X').hom) ≫
          ε_ X' X := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [tensor_evaluation]; monoidal

/-- The left mate of a tensor product of morphisms with respect to the tensor product pairings
is the tensor product of their left mates, in the reverse order. -/
@[simp]
theorem leftMate_tensorHom {X₁ X₁' X₂ X₂' Y₁ Y₁' Y₂ Y₂' : C} (pX₁ : ExactPairing X₁' X₁)
    (pX₂ : ExactPairing X₂' X₂) (pY₁ : ExactPairing Y₁' Y₁) (pY₂ : ExactPairing Y₂' Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    leftMate (tensor : ExactPairing (X₂' ⊗ X₁') (X₁ ⊗ X₂))
      (tensor : ExactPairing (Y₂' ⊗ Y₁') (Y₁ ⊗ Y₂)) (f ⊗ₘ g) =
        leftMate pX₂ pY₂ g ⊗ₘ leftMate pX₁ pY₁ f := by
  rw [tensorHom_def, comp_leftMate (pY := (tensor : ExactPairing (X₂' ⊗ Y₁') (Y₁ ⊗ X₂))),
    leftMate_whiskerLeft pX₂ pY₂ pY₁, leftMate_whiskerRight pX₁ pY₁ pX₂, ← tensorHom_def]

/-- The left mate of the associator of `X`, `Y`, `Z` with respect to the tensor product pairings
is the associator of their left duals. -/
@[simp]
theorem leftMate_associator_hom {X X' Y Y' Z Z' : C} (pX : ExactPairing X' X)
    (pY : ExactPairing Y' Y) (pZ : ExactPairing Z' Z) :
    leftMate (tensor : ExactPairing (Z' ⊗ Y' ⊗ X') ((X ⊗ Y) ⊗ Z))
      (tensor : ExactPairing ((Z' ⊗ Y') ⊗ X') (X ⊗ Y ⊗ Z)) (α_ X Y Z).hom =
        (α_ Z' Y' X').hom := by
  refine leftDualHom_ext (Y := (X ⊗ Y) ⊗ Z) ?_
  rw [leftMate_comp_evaluation]
  simp only [tensor_evaluation]
  monoidal

/-- The left mate of the left unitor of `X` with respect to the tensor product of the
self-pairing of the unit with `(X', X)` is the inverse right unitor of `X'`. -/
@[simp]
theorem leftMate_leftUnitor_hom {X X' : C} (pX : ExactPairing X' X) :
    leftMate (tensor : ExactPairing (X' ⊗ 𝟙_ C) (𝟙_ C ⊗ X)) pX (λ_ X).hom = (ρ_ X').inv := by
  refine leftDualHom_ext (Y := 𝟙_ C ⊗ X) ?_
  rw [leftMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

/-- The left mate of the right unitor of `X` with respect to the tensor product of `(X', X)`
with the self-pairing of the unit is the inverse left unitor of `X'`. -/
@[simp]
theorem leftMate_rightUnitor_hom {X X' : C} (pX : ExactPairing X' X) :
    leftMate (tensor : ExactPairing (𝟙_ C ⊗ X') (X ⊗ 𝟙_ C)) pX (ρ_ X).hom = (λ_ X').inv := by
  refine leftDualHom_ext (Y := X ⊗ 𝟙_ C) ?_
  rw [leftMate_comp_evaluation]
  simp only [tensor_evaluation, TauCeti.ExactPairing.unit_evaluation]
  monoidal

/-- The comparison `leftDualIso p₁ p₂ : X₁ ≅ X₂` between two left duals of `Y` is the left mate
of the identity of `Y`. -/
theorem leftDualIso_hom {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    (leftDualIso p₁ p₂).hom = leftMate p₂ p₁ (𝟙 Y) :=
  leftDualHom_ext (Y := Y) (by
    rw [leftMate_comp_evaluation]
    -- `leftDualIso` is defined as the left mate of `𝟙 Y` with `p₂` and `p₁` made ambient.
    exact @leftAdjointMate_comp_evaluation C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y))

/-- The inverse of the comparison `leftDualIso p₁ p₂ : X₁ ≅ X₂` is the left mate of the identity
of `Y` taken in the other direction. -/
theorem leftDualIso_inv {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    (leftDualIso p₁ p₂).inv = leftMate p₁ p₂ (𝟙 Y) :=
  -- `(leftDualIso p₁ p₂).inv` and `(leftDualIso p₂ p₁).hom` are the same left mate of `𝟙 Y`.
  leftDualIso_hom p₂ p₁

/-- If `X` has two right duals `Y₁` and `Y₂`, then taking the left mate with respect to `(X, Y₁)`
turns the comparison `rightDualIso p₁ p₂ : Y₁ ≅ Y₂` into the identity, transported to the pairing
`(X, Y₂)`. With `q = p₂`, the left mate of the comparison is `𝟙 X`. -/
theorem leftMate_rightDualIso_hom {X Y₁ Y₂ Z : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) (q : ExactPairing Z Y₂) :
    leftMate p₁ q (rightDualIso p₁ p₂).hom = leftMate p₂ q (𝟙 Y₂) := by
  have h : leftMate p₁ p₂ (rightDualIso p₁ p₂).hom = 𝟙 X :=
    leftDualHom_ext (Y := Y₁) (by
      rw [leftMate_comp_evaluation, rightDualIso_hom_whiskerRight_evaluation,
        MonoidalCategory.whiskerLeft_id, Category.id_comp])
  rw [← Category.comp_id (rightDualIso p₁ p₂).hom, comp_leftMate p₁ p₂ q, h, Category.comp_id]

/-- If `Y` has two left duals `X₁` and `X₂`, then taking the right mate with respect to `(X₁, Y)`
turns the comparison `leftDualIso p₁ p₂ : X₁ ≅ X₂` into the identity, transported to the pairing
`(X₂, Y)`. With `q = p₂`, the right mate of the comparison is `𝟙 Y`. -/
theorem rightMate_leftDualIso_hom {X₁ X₂ Y Z : C} (p₁ : ExactPairing X₁ Y)
    (p₂ : ExactPairing X₂ Y) (q : ExactPairing X₂ Z) :
    rightMate p₁ q (leftDualIso p₁ p₂).hom = rightMate p₂ q (𝟙 X₂) := by
  have h : rightMate p₁ p₂ (leftDualIso p₁ p₂).hom = 𝟙 Y :=
    rightHom_ext (X := X₁) (by
      rw [rightMate_comp_evaluation, leftDualIso_hom, leftMate_comp_evaluation])
  rw [← Category.comp_id (leftDualIso p₁ p₂).hom, comp_rightMate p₁ p₂ q, h, Category.comp_id]

end CategoryTheory.ExactPairing

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Taking the left adjoint mate of a right adjoint mate recovers the original morphism. -/
@[simp]
theorem leftAdjointMate_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : leftAdjointMate (fᘁ) = f := by
  apply ExactPairing.leftHom_ext (Y := Xᘁ)
  calc
    _ = η_ Y Yᘁ ≫ Y ◁ fᘁ := coevaluation_comp_leftAdjointMate (fᘁ)
    _ = _ := coevaluation_comp_rightAdjointMate f

/-- Taking the right adjoint mate of a left adjoint mate recovers the original morphism. -/
@[simp]
theorem rightAdjointMate_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : rightAdjointMate (leftAdjointMate f) = f := by
  apply ExactPairing.rightHom_ext (X := ᘁY)
  calc
    _ = X ◁ leftAdjointMate f ≫ ε_ (ᘁX) X :=
      rightAdjointMate_comp_evaluation (leftAdjointMate f)
    _ = _ := leftAdjointMate_comp_evaluation f

/-- Taking right adjoint mates is injective: the left adjoint mate is a left inverse. -/
theorem rightAdjointMate_injective {X Y : C} [HasRightDual X] [HasRightDual Y] :
    Function.Injective (rightAdjointMate : (X ⟶ Y) → (Yᘁ ⟶ Xᘁ)) :=
  Function.LeftInverse.injective leftAdjointMate_rightAdjointMate

/-- An isomorphism `X ≅ Y` induces an isomorphism `Yᘁ ≅ Xᘁ` of right duals, whose components are
the right adjoint mates of those of `X ≅ Y`. -/
def Iso.rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y) : Yᘁ ≅ Xᘁ where
  hom := e.homᘁ
  inv := e.invᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate, e.inv_hom_id, rightAdjointMate_id]
  inv_hom_id := by rw [← comp_rightAdjointMate, e.hom_inv_id, rightAdjointMate_id]

/-- The component of `Iso.rightAdjointMate e` is the right adjoint mate of that of `e`. -/
@[simp]
theorem Iso.rightAdjointMate_hom {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y) :
    e.rightAdjointMate.hom = e.homᘁ :=
  (rfl)

/-- The inverse of `Iso.rightAdjointMate e` is the right adjoint mate of the inverse of `e`. -/
@[simp]
theorem Iso.rightAdjointMate_inv {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y) :
    e.rightAdjointMate.inv = e.invᘁ :=
  (rfl)

end CategoryTheory

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Mathlib's right adjoint mate is the mate with respect to the ambient right duals. -/
theorem rightAdjointMate_eq_rightMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    fᘁ = ExactPairing.rightMate HasRightDual.exact HasRightDual.exact f :=
  ExactPairing.rightHom_ext (X := X) (by
    rw [rightAdjointMate_comp_evaluation, ExactPairing.rightMate_comp_evaluation])

/-- Mathlib's left adjoint mate is the left mate with respect to the ambient left duals. -/
theorem leftAdjointMate_eq_leftMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    (ᘁf) = ExactPairing.leftMate HasLeftDual.exact HasLeftDual.exact f :=
  ExactPairing.leftDualHom_ext (Y := X) (by
    rw [leftAdjointMate_comp_evaluation, ExactPairing.leftMate_comp_evaluation])

end TauCeti
