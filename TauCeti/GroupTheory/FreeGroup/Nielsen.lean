/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# A Nielsen automorphism of a free group

The automorphism `FreeGroup.mulGeneratorEquiv` sends one generator `of a` to
`of a * of b`, for distinct `a` and `b`, and fixes all other generators.
Its inverse sends `of a` to `of a * (of b)⁻¹`.
-/

public section

namespace FreeGroup

private def mulGeneratorForward {α : Type u} [DecidableEq α] (a b : α) :
    FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun c => if c = a then of a * of b else of c

private def mulGeneratorBackward {α : Type u} [DecidableEq α] (a b : α) :
    FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun c => if c = a then of a * (of b)⁻¹ else of c

private theorem mulGeneratorForward_apply_of {α : Type u} [DecidableEq α] (a b : α) :
    mulGeneratorForward a b (of a) = of a * of b := by
  simp [mulGeneratorForward]

private theorem mulGeneratorForward_apply_of_ne {α : Type u} [DecidableEq α]
    (a b c : α) (hc : c ≠ a) : mulGeneratorForward a b (of c) = of c := by
  simp [mulGeneratorForward, hc]

private theorem mulGeneratorBackward_apply_of {α : Type u} [DecidableEq α] (a b : α) :
    mulGeneratorBackward a b (of a) = of a * (of b)⁻¹ := by
  simp [mulGeneratorBackward]

private theorem mulGeneratorBackward_apply_of_ne {α : Type u} [DecidableEq α]
    (a b c : α) (hc : c ≠ a) : mulGeneratorBackward a b (of c) = of c := by
  simp [mulGeneratorBackward, hc]

private theorem mulGeneratorHom_inverse {α : Type u} [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    (mulGeneratorForward a b).comp (mulGeneratorBackward a b) = MonoidHom.id _ ∧
      (mulGeneratorBackward a b).comp (mulGeneratorForward a b) = MonoidHom.id _ := by
  constructor <;> apply FreeGroup.ext_hom <;> intro c
  all_goals by_cases hc : c = a <;> simp [mulGeneratorForward, mulGeneratorBackward, hc, hab.symm]

/-- Replacing one generator `a` by `a * b` is a Nielsen transformation when `a ≠ b`. -/
def mulGeneratorEquiv {α : Type u} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    _root_.FreeGroup α ≃* _root_.FreeGroup α :=
  MonoidHom.toMulEquiv (mulGeneratorForward a b) (mulGeneratorBackward a b)
    (mulGeneratorHom_inverse a b hab).2 (mulGeneratorHom_inverse a b hab).1

/-- The Nielsen automorphism sends its selected generator to its product with `b`. -/
@[simp]
theorem mulGeneratorEquiv_apply_of {α : Type u} [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    mulGeneratorEquiv a b hab (of a) = of a * of b := by
  simp only [mulGeneratorEquiv, MonoidHom.toMulEquiv_apply,
    mulGeneratorForward_apply_of]

/-- The Nielsen automorphism fixes every other generator. -/
@[simp]
theorem mulGeneratorEquiv_apply_of_ne {α : Type u} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hc : c ≠ a) :
    mulGeneratorEquiv a b hab (of c) = of c := by
  simp only [mulGeneratorEquiv, MonoidHom.toMulEquiv_apply,
    mulGeneratorForward_apply_of_ne a b c hc]

/-- The inverse Nielsen automorphism multiplies the selected generator by `b⁻¹`. -/
@[simp]
theorem mulGeneratorEquiv_symm_apply_of {α : Type u} [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    (mulGeneratorEquiv a b hab).symm (of a) = of a * (of b)⁻¹ := by
  simp only [mulGeneratorEquiv, MonoidHom.toMulEquiv_symm_apply,
    mulGeneratorBackward_apply_of]

/-- The inverse Nielsen automorphism fixes every other generator. -/
@[simp]
theorem mulGeneratorEquiv_symm_apply_of_ne {α : Type u} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hc : c ≠ a) :
    (mulGeneratorEquiv a b hab).symm (of c) = of c := by
  simp only [mulGeneratorEquiv, MonoidHom.toMulEquiv_symm_apply,
    mulGeneratorBackward_apply_of_ne a b c hc]

end FreeGroup
