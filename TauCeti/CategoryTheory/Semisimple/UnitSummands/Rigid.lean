/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.UnitSummands.Basic
public import TauCeti.CategoryTheory.Simple.Rigid

/-!
# Exact pairings and duality for Peircian unit supports

In a finite semisimple monoidal category `C` with `MonoidalPreadditive C`, an exact pairing
`ExactPairing X Y` between simple objects swaps left and right unit supports
(`leftUnitClass_of_exactPairing`, `rightUnitClass_of_exactPairing`). When `Y` has a right dual
`Y'`, `X ⊗ Y` is nonzero iff `rightUnitClass X = leftUnitClass Y`
(`not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass`), yielding `@[simp]` laws
`leftUnitClass_rightDual`, `rightUnitClass_rightDual`, `leftUnitClass_dual_repr`, and
`rightUnitClass_dual_repr`.

## Main declarations

* `TauCeti.not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass`: `X ⊗ Y` is nonzero iff
  `rightUnitClass X = leftUnitClass Y` when `Y` has a right dual.
* `TauCeti.leftUnitClass_of_exactPairing`, `TauCeti.rightUnitClass_of_exactPairing`: exact
  pairings of simple objects swap left and right unit supports.
* `TauCeti.leftUnitClass_rightDual`, `TauCeti.rightUnitClass_rightDual`,
  `TauCeti.leftUnitClass_dual_repr`, `TauCeti.rightUnitClass_dual_repr`: simp laws for right duals
  and dual simple classes.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §§2.1, 3.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple monoidal category, if `Y` admits a right dual `Y'`, then the tensor
product of simple objects `X` and `Y` is nonzero if and only if
`rightUnitClass X = leftUnitClass Y`. -/
theorem not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass (X Y : C) {Y' : C}
    [ExactPairing Y Y'] [Simple X] [Simple Y] :
    ¬ IsZero (X ⊗ Y) ↔ rightUnitClass X = leftUnitClass Y := by
  refine ⟨rightUnitClass_eq_leftUnitClass_of_not_isZero, fun h hz ↦ ?_⟩
  obtain ⟨I, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y') (Simple.not_isZero Y))
  have hI : I = rightUnitClass X :=
    (by simpa using leftUnitClass_eq_of_hom_ne_zero hf : I = leftUnitClass Y).trans h.symm
  have := isSplitMono_of_nonzero_from_simple hf
  have h0 : X ◁ (UnitSimpleClasses.ι I ≫ η_ Y Y') = 0 :=
    (((tensorRight Y').map_isZero hz).of_iso (α_ X Y Y').symm).eq_of_tgt _ _
  subst hI
  exact not_isZero_tensorObj_rightUnitClass X <| (IsZero.iff_id_eq_zero _).2 <| by
    rw [← whiskerLeft_id, ← IsSplitMono.id (UnitSimpleClasses.ι (rightUnitClass X) ≫ η_ Y Y'),
      whiskerLeft_comp, h0, zero_comp]

/-- In an exact pairing of simple objects, the left unit class of the right member equals the right
unit class of the left member. -/
theorem leftUnitClass_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    leftUnitClass Y = rightUnitClass X := by
  obtain ⟨_, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))
  exact (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf).symm

/-- In an exact pairing of simple objects, the right unit class of the right member equals the left
unit class of the left member. -/
theorem rightUnitClass_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    rightUnitClass Y = leftUnitClass X := by
  obtain ⟨_, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))
  have hR := rightUnitClass_eq_of_hom_ne_zero hf; have hL := leftUnitClass_eq_of_hom_ne_zero hf
  simp only [rightUnitClass_unitRepr, leftUnitClass_unitRepr] at hR hL
  exact hR.symm.trans hL

/-- Right duality interchanges left and right unit classes: the left unit class of `Xᘁ` is the
right unit class of `X`. -/
@[simp] theorem leftUnitClass_rightDual (X : C) [HasRightDual X] [Simple X] [Simple Xᘁ] :
    leftUnitClass Xᘁ = rightUnitClass X := leftUnitClass_of_exactPairing
/-- Right duality interchanges left and right unit classes: the right unit class of `Xᘁ` is the
left unit class of `X`. -/
@[simp] theorem rightUnitClass_rightDual (X : C) [HasRightDual X] [Simple X] [Simple Xᘁ] :
    rightUnitClass Xᘁ = leftUnitClass X := rightUnitClass_of_exactPairing

@[simp] theorem leftUnitClass_dual_repr [RigidCategory C] (S : SimpleClasses C) :
    leftUnitClass S.dual.repr = rightUnitClass S.repr := by
  rw [leftUnitClass_congr (SimpleClasses.dualReprIso S), leftUnitClass_rightDual]
@[simp] theorem rightUnitClass_dual_repr [RigidCategory C] (S : SimpleClasses C) :
    rightUnitClass S.dual.repr = leftUnitClass S.repr := by
  rw [rightUnitClass_congr (SimpleClasses.dualReprIso S), rightUnitClass_rightDual]

end TauCeti
