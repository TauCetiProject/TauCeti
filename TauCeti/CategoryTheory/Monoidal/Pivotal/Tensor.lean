/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace

/-!
# Pivotal traces and dimensions of tensor products

In a pivotal category, the pivotal pairing `pivotalExactPairing (X ⊗ Y)` is the tensor product of
the pivotal pairings of `Y` and of `X`, transported along the comparison
`rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. This is where the monoidality of the pivotal
structure enters. Consequently the trace of a tensor product `f ⊗ₘ g` is computed by two nested
loops.

For the left trace the loop of `f` lies inside the loop of `g`, so the scalar `leftTrace f` acts
on `Y` from the left:
`leftTrace (f ⊗ₘ g) = leftTrace ((λ_ Y).inv ≫ leftTrace f ▷ Y ≫ (λ_ Y).hom ≫ g)`. A scalar acting
on `Y` from the right can be moved out of the left trace, so whenever the left and right actions
of `leftTrace f` on `Y` agree, the left trace is multiplicative:
`leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g`. Symmetrically, the right trace is
multiplicative whenever `rightTrace g` acts on `X` in the same way from both sides.

The two actions of a scalar need not agree in a general monoidal category, so the hypothesis
cannot be dropped in general. The actions do agree in a braided category, where the left and right
traces and dimensions are therefore multiplicative without further hypotheses.

## Main declarations

* `TauCeti.pivotalExactPairing_tensor_evaluation` and
  `TauCeti.pivotalExactPairing_tensor_coevaluation`: the pivotal pairing of `X ⊗ Y` is the tensor
  product of the pivotal pairings, up to `rightDualTensorIso X Y`, which is therefore also a
  comparison of left duals (`TauCeti.rightDualTensorIso_hom_eq_leftMate`);
* `TauCeti.leftTrace_tensorHom` and `TauCeti.rightTrace_tensorHom`: the traces of `f ⊗ₘ g` as
  nested loops;
* `TauCeti.leftTrace_tensorHom_eq_comp`, `TauCeti.rightTrace_tensorHom_eq_comp`,
  `TauCeti.leftDim_tensor_eq_comp` and `TauCeti.rightDim_tensor_eq_comp`: multiplicativity of the
  traces and dimensions when the relevant scalar acts in the same way from both sides;
* `TauCeti.leftTrace_tensorHom_eq_comp_of_braided` and its companions: multiplicativity in a
  braided pivotal category.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- The evaluation of the pivotal pairing of `X ⊗ Y` is that of the tensor product of the pivotal
pairings of `Y` and of `X`, after the comparison `rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
theorem pivotalExactPairing_tensor_evaluation (X Y : C) :
    @evaluation C _ _ (X ⊗ Y)ᘁ (X ⊗ Y) (pivotalExactPairing (X ⊗ Y)) =
      (X ⊗ Y) ◁ (rightDualTensorIso X Y).hom ≫
        @evaluation C _ _ (Yᘁ ⊗ Xᘁ) (X ⊗ Y)
          (@tensor C _ _ Yᘁ Xᘁ Y X (pivotalExactPairing Y) (pivotalExactPairing X)) := by
  -- Monoidality of the pivotal structure, with the tensor comparison of the double right dual
  -- functor unfolded. The two sides differ only in how the target `(X ⊗ Y)ᘁᘁ` is written.
  have hφ : (pivotalIsoApp (X ⊗ Y)).hom = ((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫
      (rightDualTensorIso Yᘁ Xᘁ).inv ≫ ((rightDualTensorIso X Y).hom)ᘁ := by
    rw [pivotalIsoApp_tensor_hom, doubleRightDualFunctor_μ]
    rfl
  -- The evaluation of the tensor product of the pivotal pairings, written with the canonical
  -- pairing of `Yᘁ ⊗ Xᘁ`: transporting along `rightDualTensorIso Yᘁ Xᘁ` gives the tensor product
  -- of the canonical pairings, and the rest is coherence plus one interchange.
  have hε : (((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫
        (rightDualTensorIso Yᘁ Xᘁ).inv) ▷ ((Yᘁ : C) ⊗ (Xᘁ : C)) ≫
        ε_ ((Yᘁ : C) ⊗ (Xᘁ : C)) (((Yᘁ : C) ⊗ (Xᘁ : C))ᘁ : C) =
      @evaluation C _ _ (Yᘁ ⊗ Xᘁ) (X ⊗ Y)
        (@tensor C _ _ Yᘁ Xᘁ Y X (pivotalExactPairing Y) (pivotalExactPairing X)) := by
    rw [comp_whiskerRight, Category.assoc, rightDualTensorIso_inv_whiskerRight_evaluation,
      tensor_evaluation,
      @tensor_evaluation C _ _ _ _ _ _ (pivotalExactPairing Y) (pivotalExactPairing X),
      pivotalExactPairing_evaluation, pivotalExactPairing_evaluation, tensorHom_def']
    calc _ = 𝟙 _ ⊗≫ X ◁ (pivotalIsoApp Y).hom ▷ (Yᘁ : C) ▷ (Xᘁ : C) ⊗≫
          ((pivotalIsoApp X).hom ▷ (((Yᘁ : C)ᘁ : C) ⊗ (Yᘁ : C)) ≫
            ((Xᘁ : C)ᘁ : C) ◁ ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C)) ▷ (Xᘁ : C) ⊗≫
          ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (pivotalIsoApp Y).hom ▷ (Yᘁ : C) ▷ (Xᘁ : C) ⊗≫
          (X ◁ ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C) ≫ (pivotalIsoApp X).hom ▷ 𝟙_ C) ▷ (Xᘁ : C) ⊗≫
          ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by rw [whisker_exchange]
      _ = _ := by monoidal
  calc _ = (pivotalIsoApp (X ⊗ Y)).hom ▷ ((X ⊗ Y)ᘁ : C) ≫
        ε_ ((X ⊗ Y)ᘁ : C) (((X ⊗ Y)ᘁ : C)ᘁ : C) := pivotalExactPairing_evaluation _
    _ = (((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫
          (rightDualTensorIso Yᘁ Xᘁ).inv) ▷ ((X ⊗ Y)ᘁ : C) ≫
        ((rightDualTensorIso X Y).hom)ᘁ ▷ ((X ⊗ Y)ᘁ : C) ≫
        ε_ ((X ⊗ Y)ᘁ : C) (((X ⊗ Y)ᘁ : C)ᘁ : C) := by
      rw [hφ, ← Category.assoc, comp_whiskerRight, Category.assoc]
    _ = (((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫
          (rightDualTensorIso Yᘁ Xᘁ).inv) ▷ ((X ⊗ Y)ᘁ : C) ≫
        _ ◁ (rightDualTensorIso X Y).hom ≫
        ε_ ((Yᘁ : C) ⊗ (Xᘁ : C)) (((Yᘁ : C) ⊗ (Xᘁ : C))ᘁ : C) := by
      rw [rightAdjointMate_comp_evaluation]
    _ = (X ⊗ Y) ◁ (rightDualTensorIso X Y).hom ≫
        (((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫
          (rightDualTensorIso Yᘁ Xᘁ).inv) ▷ ((Yᘁ : C) ⊗ (Xᘁ : C)) ≫
        ε_ ((Yᘁ : C) ⊗ (Xᘁ : C)) (((Yᘁ : C) ⊗ (Xᘁ : C))ᘁ : C) :=
      (whisker_exchange_assoc _ _ _).symm
    _ = _ := by rw [hε]

/-- The comparison `rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` of right duals is also the
comparison of left duals of `X ⊗ Y`, for the pivotal pairing of `X ⊗ Y` and the tensor product of
the pivotal pairings of `Y` and of `X`. -/
theorem rightDualTensorIso_hom_eq_leftMate (X Y : C) :
    (rightDualTensorIso X Y).hom =
      leftMate (@tensor C _ _ Yᘁ Xᘁ Y X (pivotalExactPairing Y) (pivotalExactPairing X))
        (pivotalExactPairing (X ⊗ Y)) (𝟙 (X ⊗ Y)) :=
  @leftDualHom_ext C _ _ _ _ _
    (@tensor C _ _ Yᘁ Xᘁ Y X (pivotalExactPairing Y) (pivotalExactPairing X)) _ _ (by
      rw [leftMate_comp_evaluation, id_whiskerRight, Category.id_comp,
        pivotalExactPairing_tensor_evaluation])

/-- The coevaluation of the pivotal pairing of `X ⊗ Y`, followed by the comparison
`rightDualTensorIso X Y : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`, is the coevaluation of the tensor product of the
pivotal pairings of `Y` and of `X`. -/
@[reassoc]
theorem pivotalExactPairing_tensor_coevaluation (X Y : C) :
    @coevaluation C _ _ (X ⊗ Y)ᘁ (X ⊗ Y) (pivotalExactPairing (X ⊗ Y)) ≫
        (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) =
      @coevaluation C _ _ (Yᘁ ⊗ Xᘁ) (X ⊗ Y)
        (@tensor C _ _ Yᘁ Xᘁ Y X (pivotalExactPairing Y) (pivotalExactPairing X)) := by
  -- `rightDualTensorIso X Y` is the comparison of the two pairings as left duals of `X ⊗ Y`,
  -- which carries one coevaluation to the other.
  rw [rightDualTensorIso_hom_eq_leftMate, coevaluation_comp_leftMate,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- **The left trace of a tensor product** is a nested loop: the left trace of `f` acts on `Y`
from the left, inside the left trace of `g`. -/
theorem leftTrace_tensorHom {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace ((λ_ Y).inv ≫ leftTrace f ▷ Y ≫ (λ_ Y).hom ≫ g) := by
  -- Replace the dual `(X ⊗ Y)ᘁ` by `Yᘁ ⊗ Xᘁ` with the tensor product pairings.
  rw [leftTrace_def, ← rightDualTensorIso_hom_whiskerRight_evaluation, whisker_exchange_assoc,
    pivotalExactPairing_tensor_coevaluation_assoc]
  refine (@ExactPairing.coevaluation_whiskerLeft_tensorHom_evaluation C _ _ _ _ _ _
    (pivotalExactPairing X) _ (pivotalExactPairing Y) _ f g).trans ?_
  rw [leftTrace_def, leftTrace_def]

/-- **The right trace of a tensor product** is a nested loop: the right trace of `g` acts on `X`
from the right, inside the right trace of `f`. -/
theorem rightTrace_tensorHom {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace (f ≫ (ρ_ X).inv ≫ X ◁ rightTrace g ≫ (ρ_ X).hom) := by
  -- Replace the dual `(X ⊗ Y)ᘁ` by `Yᘁ ⊗ Xᘁ` with the tensor product pairings.
  rw [rightTrace_def, pivotalExactPairing_tensor_evaluation, ← whisker_exchange_assoc,
    coevaluation_comp_whiskerLeft_rightDualTensorIso_hom_assoc]
  refine (@ExactPairing.coevaluation_tensorHom_whiskerRight_evaluation C _ _ _ _ _ _
    (pivotalExactPairing X) _ (pivotalExactPairing Y) _ f g).trans ?_
  rw [rightTrace_def, rightTrace_def]

/-- **Multiplicativity of the left trace**: if the left trace of `f` acts on `Y` in the same way
from the left and from the right, then `leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g`. -/
theorem leftTrace_tensorHom_eq_comp {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y)
    (h : (λ_ Y).inv ≫ leftTrace f ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ leftTrace f ≫ (ρ_ Y).hom) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g := by
  rw [leftTrace_tensorHom, ← Category.assoc, ← Category.assoc, Category.assoc (λ_ Y).inv, h,
    leftTrace_comm, leftTrace_comp_whiskerLeft_scalar, scalar_comm]

/-- **Multiplicativity of the right trace**: if the right trace of `g` acts on `X` in the same way
from the left and from the right, then `rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g`. -/
theorem rightTrace_tensorHom_eq_comp {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y)
    (h : (λ_ X).inv ≫ rightTrace g ▷ X ≫ (λ_ X).hom = (ρ_ X).inv ≫ X ◁ rightTrace g ≫ (ρ_ X).hom) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g := by
  rw [rightTrace_tensorHom, ← h, rightTrace_comm, Category.assoc, Category.assoc,
    rightTrace_scalar_whiskerRight_comp, scalar_comm]

/-- **Multiplicativity of the left dimension**: if the left dimension of `X` acts on `Y` in the
same way from the left and from the right, then `leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y`. -/
theorem leftDim_tensor_eq_comp (X Y : C)
    (h : (λ_ Y).inv ≫ leftDim X ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ leftDim X ≫ (ρ_ Y).hom) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y := by
  rw [← leftTrace_id, ← leftTrace_id, ← leftTrace_id, ← id_tensorHom_id,
    leftTrace_tensorHom_eq_comp _ _ (by rwa [leftTrace_id])]

/-- **Multiplicativity of the right dimension**: if the right dimension of `Y` acts on `X` in the
same way from the left and from the right, then `rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y`. -/
theorem rightDim_tensor_eq_comp (X Y : C)
    (h : (λ_ X).inv ≫ rightDim Y ▷ X ≫ (λ_ X).hom = (ρ_ X).inv ≫ X ◁ rightDim Y ≫ (ρ_ X).hom) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y := by
  rw [← rightTrace_id, ← rightTrace_id, ← rightTrace_id, ← id_tensorHom_id,
    rightTrace_tensorHom_eq_comp _ _ (by rwa [rightTrace_id])]

section Braided

variable [BraidedCategory C]

/-- In a braided pivotal category, the left trace is multiplicative. -/
@[simp]
theorem leftTrace_tensorHom_eq_comp_of_braided {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g :=
  leftTrace_tensorHom_eq_comp f g (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom _ Y)

/-- In a braided pivotal category, the right trace is multiplicative. -/
@[simp]
theorem rightTrace_tensorHom_eq_comp_of_braided {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g :=
  rightTrace_tensorHom_eq_comp f g (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom _ X)

/-- In a braided pivotal category, the left dimension is multiplicative. -/
@[simp]
theorem leftDim_tensor_eq_comp_of_braided (X Y : C) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y :=
  leftDim_tensor_eq_comp X Y (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom _ Y)

/-- In a braided pivotal category, the right dimension is multiplicative. -/
@[simp]
theorem rightDim_tensor_eq_comp_of_braided (X Y : C) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y :=
  rightDim_tensor_eq_comp X Y (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom _ X)

end Braided

end TauCeti
