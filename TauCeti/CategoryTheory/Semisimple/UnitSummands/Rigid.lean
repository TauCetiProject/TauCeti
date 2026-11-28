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
(`leftUnitClass_eq_rightUnitClass_of_exactPairing`,
`rightUnitClass_eq_leftUnitClass_of_exactPairing`). When `Y` has a right dual
`Y'`, `X ⊗ Y` is nonzero iff `rightUnitClass X = leftUnitClass Y`
(`not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass`), yielding `@[simp]` laws
`leftUnitClass_rightDual`, `rightUnitClass_rightDual`, `leftUnitClass_dual_repr`, and
`rightUnitClass_dual_repr`.

## Main declarations

* `TauCeti.exists_unitSimpleClasses_ι_comp_coevaluation_ne_zero`: a nonzero object in an exact
  pairing has nonzero coevaluation composite with some canonical unit inclusion `ι I`.
* `TauCeti.simple_right_of_exactPairing`: the right member of an exact pairing with a simple
  object is simple.
* `TauCeti.not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass`: `X ⊗ Y` is nonzero iff
  `rightUnitClass X = leftUnitClass Y` when `Y` has a right dual.
* `TauCeti.leftUnitClass_eq_rightUnitClass_of_exactPairing`,
  `TauCeti.rightUnitClass_eq_leftUnitClass_of_exactPairing`: exact pairings with a simple left
  member swap left and right unit supports.
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

/-- For any exact pairing `(X, Y)` with `X` nonzero, some canonical unit-summand inclusion `ι I`
has nonzero composite with the coevaluation `η_ X Y`. -/
theorem exists_unitSimpleClasses_ι_comp_coevaluation_ne_zero {C : Type u} [Category.{v} C]
    [Abelian C] [MonoidalCategory C] [IsFiniteSemisimpleCategory C] (X Y : C) [ExactPairing X Y]
    (hX : ¬ IsZero X) : ∃ I : UnitSimpleClasses C, UnitSimpleClasses.ι I ≫ η_ X Y ≠ 0 :=
  (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1 (coevaluation_ne_zero hX)

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple monoidal category with `MonoidalPreadditive C`, the right member of an
exact pairing with a simple object is also simple. -/
theorem simple_right_of_exactPairing {X Y : C} (p : ExactPairing X Y) [Simple X] : Simple Y := by
  refine Simple.mk fun {Z} f _ ↦ ⟨fun _ h0 ↦ ?_, fun hf ↦ ?_⟩
  · have hY : IsZero Y := (IsZero.of_mono_eq_zero f h0).of_iso (asIso f).symm
    exact coevaluation_ne_zero (Y := Y) (Simple.not_isZero X)
      (((tensorLeft X).map_isZero hY).eq_of_tgt _ _)
  · have := isSplitMono_of_mono f
    let g : Y ⟶ Z := retraction f
    let e : Y ⟶ Y := g ≫ f
    let m : X ⟶ X := ExactPairing.leftMate p p e
    have hee : e ≫ e = e := by
      dsimp only [e, g]
      simp only [Category.assoc, IsSplitMono.id_assoc]
    have hmm : m ≫ m = m := by
      dsimp only [m]
      rw [← ExactPairing.comp_leftMate p p p e e, hee]
    have hm : m ≠ 0 := fun hm0 ↦ hf <| by
      have he0 : e = 0 := ExactPairing.rightDualHom_ext (X := X) (Y := Y) <| by
        simpa [hm0, m] using (ExactPairing.coevaluation_comp_leftMate p p e).symm
      calc f = (f ≫ g) ≫ f := by rw [IsSplitMono.id, Category.id_comp]
        _ = f ≫ e := Category.assoc _ _ _
        _ = 0 := by rw [he0, comp_zero]
    have : IsIso m := isIso_of_hom_simple hm
    have hm1 : m = 𝟙 X := (cancel_epi m).1 (by rw [Category.comp_id]; exact hmm)
    have he1 : e = 𝟙 Y := ExactPairing.rightDualHom_ext (X := X) (Y := Y) <| by
      simpa [hm1, m] using (ExactPairing.coevaluation_comp_leftMate p p e).symm
    exact ⟨⟨g, IsSplitMono.id f, he1⟩⟩

/-- In a finite semisimple monoidal category, if `Y` admits a right dual `Y'`, then the tensor
product of simple objects `X` and `Y` is nonzero if and only if
`rightUnitClass X = leftUnitClass Y`. -/
theorem not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass (X Y : C) {Y' : C}
    [ExactPairing Y Y'] [Simple X] [Simple Y] :
    ¬ IsZero (X ⊗ Y) ↔ rightUnitClass X = leftUnitClass Y := by
  refine ⟨rightUnitClass_eq_leftUnitClass_of_not_isZero, fun h hz ↦ ?_⟩
  obtain ⟨I, hf⟩ := exists_unitSimpleClasses_ι_comp_coevaluation_ne_zero Y Y' (Simple.not_isZero Y)
  have hI : I = rightUnitClass X :=
    (by simpa using leftUnitClass_eq_of_hom_ne_zero hf : I = leftUnitClass Y).trans h.symm
  subst hI
  exact not_isZero_obj_of_hom_ne_zero (tensorLeft X) hf (not_isZero_tensorObj_rightUnitClass X)
    (((tensorRight Y').map_isZero hz).of_iso (α_ X Y Y').symm)

/-- In an exact pairing with a simple left member, the left unit class of the right member equals
the right unit class of the left member. -/
theorem leftUnitClass_eq_rightUnitClass_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] :
    @leftUnitClass C _ _ _ _ _ Y (simple_right_of_exactPairing (X := X) ‹_›) =
      rightUnitClass X := by
  let _ := simple_right_of_exactPairing (X := X) ‹ExactPairing X Y›
  obtain ⟨_, hf⟩ := exists_unitSimpleClasses_ι_comp_coevaluation_ne_zero X Y (Simple.not_isZero X)
  exact (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf).symm

/-- In an exact pairing with a simple left member, the right unit class of the right member equals
the left unit class of the left member. -/
theorem rightUnitClass_eq_leftUnitClass_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] :
    @rightUnitClass C _ _ _ _ _ Y (simple_right_of_exactPairing (X := X) ‹_›) =
      leftUnitClass X := by
  let _ := simple_right_of_exactPairing (X := X) ‹ExactPairing X Y›
  obtain ⟨_, hf⟩ := exists_unitSimpleClasses_ι_comp_coevaluation_ne_zero X Y (Simple.not_isZero X)
  have hR := rightUnitClass_eq_of_hom_ne_zero hf; have hL := leftUnitClass_eq_of_hom_ne_zero hf
  simp only [rightUnitClass_unitRepr, leftUnitClass_unitRepr] at hR hL
  exact hR.symm.trans hL

/-- Right duality interchanges left and right unit classes: the left unit class of `Xᘁ` is the
right unit class of `X`. -/
@[simp] theorem leftUnitClass_rightDual (X : C) [HasRightDual X] [Simple X] :
    @leftUnitClass C _ _ _ _ _ Xᘁ (simple_right_of_exactPairing (X := X) HasRightDual.exact) =
      rightUnitClass X :=
  leftUnitClass_eq_rightUnitClass_of_exactPairing

/-- Right duality interchanges left and right unit classes: the right unit class of `Xᘁ` is the
left unit class of `X`. -/
@[simp] theorem rightUnitClass_rightDual (X : C) [HasRightDual X] [Simple X] :
    @rightUnitClass C _ _ _ _ _ Xᘁ (simple_right_of_exactPairing (X := X) HasRightDual.exact) =
      leftUnitClass X :=
  rightUnitClass_eq_leftUnitClass_of_exactPairing

@[simp] theorem leftUnitClass_dual_repr [RigidCategory C] (S : SimpleClasses C) :
    leftUnitClass S.dual.repr = rightUnitClass S.repr := by
  let _ := simple_right_of_exactPairing (HasRightDual.exact (X := S.repr))
  rw [leftUnitClass_congr (SimpleClasses.dualReprIso S), leftUnitClass_rightDual]
@[simp] theorem rightUnitClass_dual_repr [RigidCategory C] (S : SimpleClasses C) :
    rightUnitClass S.dual.repr = leftUnitClass S.repr := by
  let _ := simple_right_of_exactPairing (HasRightDual.exact (X := S.repr))
  rw [rightUnitClass_congr (SimpleClasses.dualReprIso S), rightUnitClass_rightDual]

end TauCeti
