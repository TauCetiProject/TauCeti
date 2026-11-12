/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Elementary automorphisms of free groups

Inverting every generator and multiplying one generator by an integral power of another both give
automorphisms of a free group. These transformations supply bases used to construct primitive
elements.
-/

public section

namespace TauCeti.FreeGroup

universe u

/-- The automorphism that inverts every free generator. -/
noncomputable def generatorInversion {α : Type u} : FreeGroup α ≃* FreeGroup α := by
  let f : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i => (FreeGroup.of i)⁻¹)
  have hf : f.comp f = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    intro i
    simp [f]
  exact MonoidHom.toMulEquiv f f hf hf

/-- Generator inversion sends each generator to its inverse. -/
@[simp] theorem generatorInversion_of {α : Type u} (a : α) :
    generatorInversion (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [generatorInversion]

/-- The inverse automorphism also inverts every generator. -/
@[simp] theorem generatorInversion_symm_of {α : Type u} (a : α) :
    generatorInversion.symm (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [generatorInversion]

/-- The Nielsen automorphism sending `a` to `a b ^ n` and fixing the other free generators. -/
noncomputable def nielsenMul {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    FreeGroup α ≃* FreeGroup α := by
  classical
  refine MonoidHom.toMulEquiv
    (FreeGroup.lift fun c => if c = a then FreeGroup.of a * FreeGroup.of b ^ n else FreeGroup.of c)
    (FreeGroup.lift fun c =>
      if c = a then FreeGroup.of a * FreeGroup.of b ^ (-n) else FreeGroup.of c)
    ?_ ?_
  all_goals
    apply FreeGroup.ext_hom
    intro c
    by_cases hca : c = a
    · subst c
      simp [hab.symm, mul_assoc]
    · simp [hca]

/-- The Nielsen transformation multiplies the selected generator by a power of the other. -/
@[simp] theorem nielsenMul_of_left {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    nielsenMul a b hab n (FreeGroup.of a) = FreeGroup.of a * FreeGroup.of b ^ n := by
  classical
  simp [nielsenMul]

/-- The Nielsen transformation fixes every other generator. -/
@[simp] theorem nielsenMul_of_ne {α : Type u} (a b i : α) (hab : a ≠ b) (n : ℤ)
    (hi : i ≠ a) :
    nielsenMul a b hab n (FreeGroup.of i) = FreeGroup.of i := by
  classical
  simp [nielsenMul, hi]

/-- The inverse Nielsen transformation uses the opposite exponent. -/
theorem nielsenMul_symm_of_left {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    (nielsenMul a b hab n).symm (FreeGroup.of a) =
      FreeGroup.of a * FreeGroup.of b ^ (-n) := by
  classical
  simp [nielsenMul]

/-- The inverse Nielsen transformation fixes every other generator. -/
theorem nielsenMul_symm_of_ne {α : Type u} (a b i : α) (hab : a ≠ b) (n : ℤ)
    (hi : i ≠ a) :
    (nielsenMul a b hab n).symm (FreeGroup.of i) = FreeGroup.of i := by
  classical
  simp [nielsenMul, hi]

/-- The inverse Nielsen transformation is the move with the opposite exponent. -/
@[simp] theorem nielsenMul_symm {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    (nielsenMul a b hab n).symm = nielsenMul a b hab (-n) := by
  apply MulEquiv.ext
  intro x
  induction x using FreeGroup.induction_on with
  | one => simp
  | of c =>
    by_cases hca : c = a
    · subst c
      simp [nielsenMul_symm_of_left, zpow_neg]
    · simp [hca, nielsenMul_symm_of_ne]
  | inv_of c hc => simp [hc]
  | mul x y hx hy => simp [hx, hy]

end TauCeti.FreeGroup
