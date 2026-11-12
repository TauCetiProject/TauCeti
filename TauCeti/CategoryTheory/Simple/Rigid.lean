/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Duality on simple classes

In a rigid monoidal abelian category with additive tensor product the right dual of a simple
object is simple (`TauCeti.simple_rightDual`), so duality acts on the simple isomorphism classes:
`TauCeti.SimpleClasses.dual` sends the class of `X` to the class of `Xᘁ`. In a finite semisimple
rigid category with simple tensor unit this action is an involution
(`TauCeti.SimpleClasses.dual_dual`, in `TauCeti/CategoryTheory/Semisimple/Rigid.lean`).

## Main declarations

* `TauCeti.SimpleClasses.dual`: the dual simple class;
* `TauCeti.SimpleClasses.dualReprIso`: its representative is isomorphic to the right dual of the
  representative;
* `TauCeti.SimpleClasses.dual_classOf` and `TauCeti.SimpleClasses.eq_dual_iff`: characterizations
  of the dual class;
* `TauCeti.SimpleClasses.classOfUnitReprRightDualIso`: the right dual of the representative of
  a simple tensor unit is isomorphic to the tensor unit, compatibly with evaluation and
  coevaluation.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.8
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C]

namespace SimpleClasses

/-- The **dual** of a simple class: the class of the right dual of its representative. -/
def dual (S : SimpleClasses C) : SimpleClasses C :=
  classOf S.reprᘁ

/-- The representative of the dual class is isomorphic to the right dual of the representative. -/
def dualReprIso (S : SimpleClasses C) : S.dual.repr ≅ S.reprᘁ :=
  classOfReprIso _

/-- The dual of the class of a simple object is the class of its right dual. -/
@[simp]
theorem dual_classOf (X : C) [Simple X] : (classOf X).dual = classOf Xᘁ :=
  (classOf_eq_iff_nonempty_iso _ _).2 ⟨(classOfReprIso X).rightAdjointMate.symm⟩

/-- A simple class is the dual of `S` exactly when its representative is isomorphic to the right
dual of the representative of `S`. -/
theorem eq_dual_iff (S T : SimpleClasses C) : T = S.dual ↔ Nonempty (T.repr ≅ S.reprᘁ) := by
  rw [eq_iff_nonempty_iso]
  exact ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ dualReprIso S⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ (dualReprIso S).symm⟩⟩

section Unit

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
  [RightRigidCategory C] [Simple (𝟙_ C)]

/-- The right dual of the representative of the unit class is isomorphic to the tensor unit,
using `classOfReprIso (𝟙_ C)` and uniqueness of right duals. -/
def classOfUnitReprRightDualIso : (classOf (𝟙_ C)).reprᘁ ≅ 𝟙_ C :=
  rightDualIso (RightRigidCategory.rightDual _).exact
    (exactPairingCongrLeft (Y := 𝟙_ C) (classOfReprIso (𝟙_ C)))

/-- The forward unit-dual comparison is evaluation after inserting the unit representative. -/
theorem classOfUnitReprRightDualIso_hom :
    (classOfUnitReprRightDualIso (C := C)).hom =
      (ρ_ _).inv ≫ _ ◁ (classOfReprIso (𝟙_ C)).inv ≫
        ε_ (classOf (𝟙_ C)).repr (classOf (𝟙_ C)).reprᘁ := by
  simp only [classOfUnitReprRightDualIso, rightDualIso, rightAdjointMate,
    exactPairingCongrLeft_coevaluation, ExactPairing.unit_coevaluation]
  monoidal

/-- The inverse unit-dual comparison is coevaluation followed by the unit identification. -/
theorem classOfUnitReprRightDualIso_inv :
    (classOfUnitReprRightDualIso (C := C)).inv =
      η_ (classOf (𝟙_ C)).repr (classOf (𝟙_ C)).reprᘁ ≫
        (classOfReprIso (𝟙_ C)).hom ▷ _ ≫ (λ_ _).hom := by
  simp only [classOfUnitReprRightDualIso, rightDualIso, rightAdjointMate,
    exactPairingCongrLeft_evaluation, ExactPairing.unit_evaluation]
  monoidal

/-- The inverse comparison carries evaluation to the unit evaluation. -/
@[reassoc (attr := simp)]
theorem classOfUnitReprRightDualIso_inv_evaluation :
    (classOfUnitReprRightDualIso (C := C)).inv ▷ _ ≫
        ε_ (classOf (𝟙_ C)).repr (classOf (𝟙_ C)).reprᘁ =
      (λ_ _).hom ≫ (classOfReprIso (𝟙_ C)).hom := by
  rw [classOfUnitReprRightDualIso, ExactPairing.rightDualIso_inv_whiskerRight_evaluation,
    exactPairingCongrLeft_evaluation, ExactPairing.unit_evaluation]
  monoidal

/-- The forward comparison carries coevaluation to the unit coevaluation. -/
@[reassoc (attr := simp)]
theorem coevaluation_classOfUnitReprRightDualIso_hom :
    η_ (classOf (𝟙_ C)).repr (classOf (𝟙_ C)).reprᘁ ≫
        _ ◁ (classOfUnitReprRightDualIso (C := C)).hom =
      (classOfReprIso (𝟙_ C)).inv ≫ (ρ_ _).inv := by
  rw [classOfUnitReprRightDualIso, ExactPairing.rightDualIso_hom,
    ExactPairing.coevaluation_comp_rightMate, exactPairingCongrLeft_coevaluation,
    ExactPairing.unit_coevaluation]
  monoidal

end Unit

end SimpleClasses

end TauCeti
