/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace
public import TauCeti.CategoryTheory.Monoidal.Rigid.Drinfeld

/-!
# The canonical pivotal structure on a symmetric rigid category

In a braided right rigid category the Drinfeld isomorphisms `drinfeldIso X : X ≅ Xᘁᘁ` form a
natural isomorphism `drinfeldNatIso : 𝟭 C ≅ doubleRightDualFunctor C`. It is always compatible
with the unit comparison of the double right dual functor. When the braiding is symmetric it is
also compatible with the tensor comparison, so it is a monoidal natural isomorphism: this rests
on the fact that in a symmetric category the swapped pairing of a tensor product is the tensor
product of the swapped pairings (`TauCeti.braiding_comp_tensor_evaluation`). Hence every
symmetric rigid category carries a canonical pivotal structure, registered as the instance
`TauCeti.symmetricPivotalCategory`.

Through the Drinfeld isomorphism, the pivotal pairing of `X` becomes the braided swap of the
pairing `(X, Xᘁ)`, so both traces are computed by the braiding:
`rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ` and
`leftTrace f = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. Naturality of the braiding then
shows that the left and right traces of every endomorphism agree: the canonical pivotal
structure satisfies the sphericity condition.

## Main declarations

* `TauCeti.drinfeldNatIso`: the Drinfeld isomorphisms as a natural isomorphism
  `𝟭 C ≅ doubleRightDualFunctor C` in a braided right rigid category, with
  `TauCeti.drinfeldNatIso_hom_app_unit` its compatibility with the unit comparison;
* `TauCeti.drinfeldIso_tensor_hom`: in a symmetric category, the Drinfeld isomorphism of
  `X ⊗ Y` is the tensor product of those of `X` and `Y`, followed by the tensor comparison of the
  double right dual functor;
* `TauCeti.drinfeldNatIso_isMonoidal`: in a symmetric category, `drinfeldNatIso` is monoidal;
* `TauCeti.symmetricPivotalCategory`: the canonical pivotal structure on a symmetric rigid
  category, whose components are the Drinfeld isomorphisms (`TauCeti.pivotalIsoApp_eq_drinfeldIso`);
* `TauCeti.rightTrace_eq_braiding` and `TauCeti.leftTrace_eq_braiding`: the traces as braided
  loops, and `TauCeti.leftTrace_eq_rightTrace_of_symmetric`: the two traces agree.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§8.9–8.10
* [leanprover-community/mathlib4#42192](https://github.com/leanprover-community/mathlib4/pull/42192),
  for the name `symmetricPivotalCategory` and the construction of the pivotal structure from the
  Drinfeld isomorphism
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing Functor.LaxMonoidal

universe v u

namespace TauCeti

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
functor. This holds for any braiding. -/
theorem drinfeldNatIso_hom_app_unit :
    (drinfeldNatIso (C := C)).hom.app (𝟙_ C) = ε (doubleRightDualFunctor C) := by
  refine Eq.trans ?_ (doubleRightDualFunctor_ε C).symm
  rw [drinfeldNatIso_hom_app]
  -- The dual of `𝟙_ C` here is the one chosen by the rigid structure, not `hasRightDualUnit`.
  refine rightHom_ext (X := (RightRigidCategory.rightDual (𝟙_ C)).rightDual) ?_
  -- The evaluation of `(𝟙_ C, (𝟙_ C)ᘁ)` through the identification `(𝟙_ C)ᘁ ≅ 𝟙_ C`.
  have h := rightMate_comp_evaluation exactPairingUnit (RightRigidCategory.rightDual (𝟙_ C)).exact
    (𝟙 _)
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, ← rightDualIso_hom,
    ExactPairing.unit_evaluation] at h
  rw [drinfeldIso_hom_comp_evaluation, comp_whiskerRight, Category.assoc,
    rightMate_comp_evaluation, ← whisker_exchange_assoc, rightDualIso_inv,
    rightMate_comp_evaluation, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ExactPairing.unit_evaluation, ← h, braiding_tensorUnit_left]
  monoidal

end Braided

section Symmetric

variable [SymmetricCategory C] [RightRigidCategory C]

/-- In a symmetric right rigid category, the Drinfeld isomorphism of `X ⊗ Y` is the tensor product
of the Drinfeld isomorphisms of `X` and `Y`, followed by the tensor comparison of the double
right dual functor. -/
theorem drinfeldIso_tensor_hom (X Y : C) :
    (drinfeldIso (X ⊗ Y)).hom =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ μ (doubleRightDualFunctor C) X Y := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (doubleRightDualFunctor_μ C X Y).symm)
  refine rightHom_ext (X := (X ⊗ Y)ᘁ) ?_
  -- Evaluate both sides against `(X ⊗ Y)ᘁ`, and move the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` to the
  -- front, so that the right side becomes an evaluation of the tensor product pairing of
  -- `(Yᘁ, Yᘁᘁ)` and `(Xᘁ, Xᘁᘁ)`.
  rw [drinfeldIso_hom_comp_evaluation, comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightDualTensorIso.eq_1 Yᘁ Xᘁ, rightDualIso_inv,
    rightMate_comp_evaluation, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    tensor_evaluation]
  -- After the Drinfeld isomorphisms, that evaluation is the braided evaluation of the tensor
  -- product pairing of `(X, Xᘁ)` and `(Y, Yᘁ)`.
  have key : ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ▷ (Yᘁ ⊗ Xᘁ) ≫
      𝟙 _ ⊗≫ ((Xᘁ : C)ᘁ : C) ◁ ε_ Yᘁ Yᘁᘁ ▷ (Xᘁ : C) ⊗≫ ε_ Xᘁ Xᘁᘁ =
        (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := by
    rw [braiding_comp_tensor_evaluation]
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
  rw [key, braiding_naturality_right_assoc, rightDualTensorIso, rightDualIso_hom,
    rightMate_comp_evaluation, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- In a symmetric right rigid category, the Drinfeld isomorphisms form a monoidal natural
isomorphism from the identity functor to the double right dual functor. -/
instance drinfeldNatIso_isMonoidal : NatTrans.IsMonoidal (drinfeldNatIso (C := C)).hom where
  -- The unit and tensor comparisons of the identity functor are identities.
  unit := (Category.id_comp _).trans drinfeldNatIso_hom_app_unit
  tensor X Y := (Category.id_comp _).trans (drinfeldIso_tensor_hom X Y)

end Symmetric

section Pivotal

variable [SymmetricCategory C] [RigidCategory C]

/-- The canonical pivotal structure on a symmetric rigid category, given by the Drinfeld
isomorphisms. -/
noncomputable instance symmetricPivotalCategory : PivotalCategory C where
  pivotalIso := drinfeldNatIso

/-- The components of the canonical pivotal structure on a symmetric rigid category are the
Drinfeld isomorphisms. -/
@[simp]
theorem pivotalIsoApp_eq_drinfeldIso (X : C) : pivotalIsoApp X = drinfeldIso X :=
  Iso.ext ((pivotalIso_hom_app X).symm.trans (drinfeldNatIso_hom_app X))

/-- In a symmetric rigid category with its canonical pivotal structure, the right trace of `f`
closes up `f` with the coevaluation of `(X, Xᘁ)` and the braided evaluation. -/
theorem rightTrace_eq_braiding {X : C} (f : X ⟶ X) :
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [rightTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_drinfeldIso, drinfeldIso_hom_comp_evaluation]

/-- In a symmetric rigid category with its canonical pivotal structure, the left trace of `f`
closes up `f` with the braided coevaluation and the evaluation of `(X, Xᘁ)`. -/
theorem leftTrace_eq_braiding {X : C} (f : X ⟶ X) :
    leftTrace f = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  rw [leftTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_drinfeldIso,
    coevaluation_comp_drinfeldIso_inv_assoc, ← SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- In a symmetric rigid category with its canonical pivotal structure, the left and right traces
of every endomorphism agree. -/
theorem leftTrace_eq_rightTrace_of_symmetric {X : C} (f : X ⟶ X) :
    leftTrace f = rightTrace f := by
  rw [leftTrace_eq_braiding, rightTrace_eq_braiding, braiding_naturality_left_assoc]

end Pivotal

end TauCeti
