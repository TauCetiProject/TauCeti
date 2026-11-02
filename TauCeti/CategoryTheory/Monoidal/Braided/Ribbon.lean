/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Balanced
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Ribbon categories

A ribbon category is a balanced rigid category whose twist commutes with right duality.
The compatibility is a property of the chosen balanced structure, not additional twist data.
It lets a twist slide through an evaluation or a coevaluation, and is the condition that
makes the associated pivotal structure spherical.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
  and Appendix A.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory ExactPairing

universe v u

namespace TauCeti

/-- A balanced rigid category is *ribbon* when the twist of the right dual is the right
adjoint mate of the twist. This property refers to the specified balanced structure. -/
class RibbonCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [BalancedCategory C] : Prop where
  /-- The twist commutes with right duality. -/
  twist_rightDual (X : C) : BalancedCategory.twist.hom.app (Xᘁ : C) =
    (BalancedCategory.twist.hom.app X)ᘁ

namespace RibbonCategory

attribute [simp] twist_rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [BalancedCategory C] [RibbonCategory C]

/-- The inverse twist also commutes with right duality. -/
@[simp]
theorem twist_inv_rightDual (X : C) : BalancedCategory.twist.inv.app (Xᘁ : C) =
    (BalancedCategory.twist.inv.app X)ᘁ := by
  have h : BalancedCategory.twist.app (Xᘁ : C) =
      (BalancedCategory.twist.app X).rightAdjointMate :=
    Iso.ext (by
      rw [Iso.rightAdjointMate_hom]
      exact twist_rightDual X)
  simpa only [Iso.rightAdjointMate_inv, Iso.app_inv, Functor.id_obj] using congrArg Iso.inv h

/-- A twist slides across evaluation from an object to its right dual. -/
@[reassoc]
theorem twist_comp_evaluation (X : C) :
    BalancedCategory.twist.hom.app (Xᘁ : C) ▷ X ≫ ε_ X Xᘁ =
      Xᘁ ◁ BalancedCategory.twist.hom.app X ≫ ε_ X Xᘁ := by
  rw [twist_rightDual]
  simpa only [Functor.id_obj] using
    rightAdjointMate_comp_evaluation (BalancedCategory.twist.hom.app X)

/-- A twist slides across coevaluation from the right dual to the object. -/
@[reassoc]
theorem coevaluation_comp_twist (X : C) :
    η_ X Xᘁ ≫ X ◁ BalancedCategory.twist.hom.app (Xᘁ : C) =
      η_ X Xᘁ ≫ BalancedCategory.twist.hom.app X ▷ Xᘁ := by
  rw [twist_rightDual]
  simpa only [Functor.id_obj] using
    coevaluation_comp_rightAdjointMate (BalancedCategory.twist.hom.app X)

end RibbonCategory

end TauCeti
