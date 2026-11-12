/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor

/-!
# The Drinfeld isomorphism

In a braided monoidal category, an object `X` with a right dual whose right dual also exists
is canonically isomorphic to its double right dual. The Drinfeld isomorphism compares two
right duals of `Xᘁ`: the chosen double dual, and `X` with the braided swapped pairing.
Its evaluation and coevaluation identities and naturality are recorded here.

In a braided right rigid category the Drinfeld isomorphisms form a natural isomorphism
`drinfeldNatIso : 𝟭 C ≅ doubleRightDualFunctor C`, which is always compatible with the unit
comparison of the double right dual functor. An arbitrary braiding does not make it monoidal:
the Drinfeld isomorphism of `X ⊗ Y`, precomposed with the double braiding
`β_{X,Y} ≫ β_{Y,X}`, is the tensor product of the Drinfeld isomorphisms of `X` and `Y` followed
by the tensor comparison. This rests on the computation of the swapped pairing of a tensor
product
(`TauCeti.braiding_comp_braiding_whiskerRight_comp_braiding_comp_tensor_evaluation`). When the
braiding is symmetric the double braiding is the identity, so `drinfeldNatIso` is a monoidal
natural isomorphism. In a symmetric rigid category it is therefore the underlying isomorphism of
the canonical pivotal structure.

## Main declarations

* `TauCeti.drinfeldIso`: the Drinfeld isomorphism `X ≅ Xᘁᘁ`, with `TauCeti.drinfeldIso_hom_eq`
  and `TauCeti.drinfeldIso_inv_eq` writing it and its inverse as explicit braided composites;
* `TauCeti.drinfeldNatIso`: the Drinfeld isomorphisms as a natural isomorphism
  `𝟭 C ≅ doubleRightDualFunctor C` in a braided right rigid category, with
  `TauCeti.drinfeldIso_unit_hom` its compatibility with the unit comparison;
* `TauCeti.braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom`: the double braiding of
  `X ⊗ Y` followed by the Drinfeld isomorphism of `X ⊗ Y` is the tensor product of those of `X`
  and `Y`, followed by the tensor comparison of the double right dual functor;
* `TauCeti.drinfeldNatIso_isMonoidal`: in a symmetric category, `drinfeldNatIso` is monoidal.

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

/-- The inverse Drinfeld isomorphism inserts the coevaluation of `X`, braids `Xᘁᘁ` past `X`, and
contracts `Xᘁᘁ` against `Xᘁ`. -/
theorem drinfeldIso_inv_eq :
    (drinfeldIso X).inv = (ρ_ ((Xᘁ : C)ᘁ : C)).inv ≫ ((Xᘁ : C)ᘁ : C) ◁ η_ X Xᘁ ≫
      (α_ ((Xᘁ : C)ᘁ : C) X (Xᘁ : C)).inv ≫ (β_ ((Xᘁ : C)ᘁ : C) X).hom ▷ (Xᘁ : C) ≫
        (α_ X ((Xᘁ : C)ᘁ : C) (Xᘁ : C)).hom ≫ X ◁ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ (ρ_ X).hom := by
  have h₁ : (Xᘁ : C) ◁ (drinfeldIso X).inv ≫ ε_ X Xᘁ =
      (β_ ((Xᘁ : C)ᘁ : C) (Xᘁ : C)).inv ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
    rw [← drinfeldIso_inv_comp_evaluation, Iso.inv_hom_id_assoc]
  calc
    _ = (drinfeldIso X).inv ⊗≫ (η_ X Xᘁ ▷ X ⊗≫ X ◁ ε_ X Xᘁ) ⊗≫ 𝟙 X := by
      rw [evaluation_coevaluation'']; monoidal
    _ = 𝟙 _ ⊗≫ (η_ X Xᘁ ▷ ((Xᘁ : C)ᘁ : C) ≫ (X ⊗ (Xᘁ : C)) ◁ (drinfeldIso X).inv) ⊗≫
          X ◁ ε_ X Xᘁ ⊗≫ 𝟙 X := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ η_ X Xᘁ ▷ ((Xᘁ : C)ᘁ : C) ⊗≫ X ◁ ((Xᘁ : C) ◁ (drinfeldIso X).inv ≫ ε_ X Xᘁ) ⊗≫
          𝟙 X := by
      monoidal
    -- Braiding `Xᘁᘁ` past the coevaluation of `X` and back under `Xᘁ` moves it to the right of
    -- the coevaluation.
    _ = _ := by rw [h₁, whiskerLeft_comp_braiding_whiskerRight_assoc]; monoidal

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

namespace TauCeti

open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Braided

variable [BraidedCategory C] [RightRigidCategory C]

/-- The Drinfeld isomorphisms `X ≅ Xᘁᘁ` of a braided right rigid category, as a natural
isomorphism from the identity functor to the double right dual functor. -/
noncomputable def drinfeldNatIso : 𝟭 C ≅ doubleRightDualFunctor C :=
  NatIso.ofComponents (fun X => drinfeldIso X) fun f => drinfeldIso_hom_naturality f

/-- The components of `drinfeldNatIso` are the Drinfeld isomorphisms. -/
@[simp]
theorem drinfeldNatIso_hom_app (X : C) :
    (drinfeldNatIso (C := C)).hom.app X = (drinfeldIso X).hom :=
  (rfl)

/-- The components of the inverse of `drinfeldNatIso` are the inverse Drinfeld isomorphisms. -/
@[simp]
theorem drinfeldNatIso_inv_app (X : C) :
    (drinfeldNatIso (C := C)).inv.app X = (drinfeldIso X).inv :=
  (rfl)

/-- At the unit, the Drinfeld isomorphism is the unit comparison of the double right dual
functor. This holds for any braiding. The right dual of `𝟙_ C` is explicit because it is the one
chosen by the rigid structure, which need not be Mathlib's `hasRightDualUnit`. -/
theorem drinfeldIso_unit_hom :
    (@drinfeldIso C _ _ _ (𝟙_ C) (RightRigidCategory.rightDual _) _).hom =
      ε (doubleRightDualFunctor C) := by
  refine Eq.trans ?_ (doubleRightDualFunctor_ε C).symm
  -- The dual of `𝟙_ C` here is the one chosen by the rigid structure, not `hasRightDualUnit`.
  refine rightHom_ext (X := (RightRigidCategory.rightDual (𝟙_ C)).rightDual) ?_
  -- The evaluation of `(𝟙_ C, (𝟙_ C)ᘁ)` through the identification `(𝟙_ C)ᘁ ≅ 𝟙_ C`.
  have h := rightDualIso_hom_whiskerRight_evaluation (RightRigidCategory.rightDual (𝟙_ C)).exact
    exactPairingUnit
  rw [ExactPairing.unit_evaluation] at h
  rw [drinfeldIso_hom_comp_evaluation, comp_whiskerRight, Category.assoc,
    rightMate_comp_evaluation, ← whisker_exchange_assoc,
    rightDualIso_inv_whiskerRight_evaluation, ExactPairing.unit_evaluation, ← h,
    braiding_tensorUnit_left]
  monoidal

/-- The double braiding `β_{X,Y} ≫ β_{Y,X}` of `X ⊗ Y` followed by the Drinfeld isomorphism of
`X ⊗ Y` is the tensor product of the Drinfeld isomorphisms of `X` and `Y`, followed by the tensor
comparison of the double right dual functor. -/
theorem braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom (X Y : C) :
    (β_ X Y).hom ≫ (β_ Y X).hom ≫ (drinfeldIso (X ⊗ Y)).hom =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ μ (doubleRightDualFunctor C) X Y := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (doubleRightDualFunctor_μ C X Y).symm)
  refine rightHom_ext (X := (X ⊗ Y)ᘁ) ?_
  -- Evaluate both sides against `(X ⊗ Y)ᘁ`, and move the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` to the
  -- front, so that the right side becomes an evaluation of the tensor product pairing of
  -- `(Yᘁ, Yᘁᘁ)` and `(Xᘁ, Xᘁᘁ)`.
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    drinfeldIso_hom_comp_evaluation, comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightDualTensorIso_inv_whiskerRight_evaluation,
    tensor_evaluation]
  -- After the Drinfeld isomorphisms, that evaluation is the braided evaluation of the tensor
  -- product pairing of `(X, Xᘁ)` and `(Y, Yᘁ)`, after the double braiding.
  have key : ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ▷ (Yᘁ ⊗ Xᘁ) ≫
      𝟙 _ ⊗≫ ((Xᘁ : C)ᘁ : C) ◁ ε_ Yᘁ Yᘁᘁ ▷ (Xᘁ : C) ⊗≫ ε_ Xᘁ Xᘁᘁ =
        ((β_ X Y).hom ≫ (β_ Y X).hom) ▷ (Yᘁ ⊗ Xᘁ) ≫ (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫
          ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := by
    rw [braiding_comp_braiding_whiskerRight_comp_braiding_comp_tensor_evaluation]
    calc
      _ = 𝟙 _ ⊗≫ ((drinfeldIso X).hom ▷ ((Y ⊗ (Yᘁ : C)) ⊗ (Xᘁ : C)) ≫
            ((Xᘁ : C)ᘁ : C) ◁ (((drinfeldIso Y).hom ▷ (Yᘁ : C) ≫ ε_ Yᘁ Yᘁᘁ) ▷ (Xᘁ : C))) ⊗≫
              ε_ Xᘁ Xᘁᘁ := by
        rw [tensorHom_def]; monoidal
      _ = 𝟙 _ ⊗≫ (X ◁ (((drinfeldIso Y).hom ▷ (Yᘁ : C) ≫ ε_ Yᘁ Yᘁᘁ) ▷ (Xᘁ : C)) ≫
            (drinfeldIso X).hom ▷ (𝟙_ C ⊗ (Xᘁ : C))) ⊗≫ ε_ Xᘁ Xᘁᘁ := by
        rw [whisker_exchange]
      _ = _ := by
        rw [drinfeldIso_hom_comp_evaluation, ← drinfeldIso_hom_comp_evaluation X]; monoidal
  rw [key, whisker_exchange_assoc, braiding_naturality_right_assoc,
    rightDualTensorIso_hom_whiskerRight_evaluation, comp_whiskerRight, Category.assoc]

end Braided

section Symmetric

variable [SymmetricCategory C] [RightRigidCategory C]

/-- In a symmetric right rigid category, the Drinfeld isomorphisms form a monoidal natural
isomorphism from the identity functor to the double right dual functor. -/
instance drinfeldNatIso_isMonoidal : NatTrans.IsMonoidal (drinfeldNatIso (C := C)).hom where
  -- The unit and tensor comparisons of the identity functor are identities.
  unit := (Category.id_comp _).trans drinfeldIso_unit_hom
  -- In a symmetric category the double braiding in
  -- `braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom` is the identity.
  tensor X Y := (Category.id_comp _).trans <|
    (SymmetricCategory.symmetry_assoc X Y _).symm.trans
      (braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom X Y)

end Symmetric

end TauCeti
