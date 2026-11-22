/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Restriction and extension of functionals on self-adjoint elements

For a topological complex star module `A`, taking the real part restricts a complex-linear
functional `φ : WeakDual ℂ A` to a real-linear functional on `selfAdjoint A`
(`WeakDual.restrictToSelfAdjoint`), defined by restricting scalars, postcomposing with
`Complex.reCLM`, and pulling back along `(selfAdjoint.submodule ℝ A).subtypeL`. Conversely, any
real-linear functional `ψ : WeakDual ℝ (selfAdjoint A)` extends uniquely to a complex-linear
functional on `A` whose value at each self-adjoint `a` is `(ψ a : ℂ)`, given by
`a ↦ ψ (ℜ a) + I * ψ (ℑ a)` (`WeakDual.extendFromSelfAdjoint`). Restricting the extension recovers
`ψ` (`WeakDual.restrictToSelfAdjoint_extendFromSelfAdjoint`), and any complex-linear functional
that is real-valued on `selfAdjoint A` is the extension of its restriction
(`WeakDual.extendFromSelfAdjoint_restrictToSelfAdjoint`).

## Main definitions and results

* `WeakDual.restrictToSelfAdjoint`: weak-star continuous real-linear restriction
  `WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A)`.
* `WeakDual.extendFromSelfAdjoint`: weak-star continuous real-linear extension
  `WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A`.
* `WeakDual.restrictToSelfAdjoint_apply`, `WeakDual.extendFromSelfAdjoint_apply`,
  `WeakDual.extendFromSelfAdjoint_apply_coe`,
  `WeakDual.eq_extendFromSelfAdjoint_of_forall_apply_coe`,
  `WeakDual.existsUnique_forall_apply_coe_eq`,
  `WeakDual.restrictToSelfAdjoint_extendFromSelfAdjoint`,
  `WeakDual.extendFromSelfAdjoint_restrictToSelfAdjoint`: evaluation, uniqueness, and
  restriction-extension identities.
-/

public section

open scoped ComplexStarModule

namespace WeakDual

section Restrict

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [TopologicalSpace A]

/-- Restriction of a complex-linear functional on `A` to a real-linear functional on
`selfAdjoint A`, taking the real part, as a weak-star continuous real-linear map. -/
noncomputable def restrictToSelfAdjoint : WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A) :=
  let toReal : WeakDual ℂ A →L[ℝ] WeakDual ℝ A :=
    { toFun := fun φ =>
        StrongDual.toWeakDual (Complex.reCLM.comp ((toStrongDual φ).restrictScalars ℝ))
      map_add' := fun _ _ => DFunLike.ext _ _ fun _ => by simp
      map_smul' := fun _ _ => DFunLike.ext _ _ fun _ => by simp
      cont := WeakDual.continuous_of_continuous_eval fun a =>
        Complex.continuous_re.comp (WeakDual.eval_continuous a) }
  (selfAdjoint.submodule ℝ A).subtypeL.pullbackFunctional.comp toReal

/-- Evaluating `restrictToSelfAdjoint φ` at a self-adjoint element `a` yields `(φ a).re`. -/
@[simp]
theorem restrictToSelfAdjoint_apply (φ : WeakDual ℂ A) (a : selfAdjoint A) :
    restrictToSelfAdjoint φ a = (φ (a : A)).re := by
  change ((selfAdjoint.submodule ℝ A).subtypeL.pullbackFunctional
    (StrongDual.toWeakDual (Complex.reCLM.comp ((toStrongDual φ).restrictScalars ℝ))))
    ⟨(a : A), a.property⟩ = (φ (a : A)).re
  simp [ContinuousLinearMap.pullbackFunctional_apply]

end Restrict

section Extend

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul ℂ A]

/-- The unique complex-linear extension of `ψ : WeakDual ℝ (selfAdjoint A)` to `A` whose value at
every self-adjoint element `a : selfAdjoint A` is `(ψ a : ℂ)`, defined by
`a ↦ ψ (ℜ a) + I * ψ (ℑ a)` as a weak-star continuous real-linear map. -/
noncomputable def extendFromSelfAdjoint : WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A :=
  have : ContinuousConstSMul ℝ A :=
    ⟨fun r => by simpa only [← Complex.coe_smul] using continuous_const_smul (r : ℂ)⟩
  (WeakDual.extendRCLikeL (𝕜 := ℂ) (F := A)).toContinuousLinearMap.comp
    (selfAdjointPartL ℝ A).pullbackFunctional

/-- Evaluating `extendFromSelfAdjoint ψ` at `a` gives `ψ (ℜ a) + I * ψ (ℑ a)`. -/
@[simp]
theorem extendFromSelfAdjoint_apply (ψ : WeakDual ℝ (selfAdjoint A)) (a : A) :
    extendFromSelfAdjoint ψ a = (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ) := by
  have : ContinuousConstSMul ℝ A :=
    ⟨fun r => by simpa only [← Complex.coe_smul] using continuous_const_smul (r : ℂ)⟩
  rw [extendFromSelfAdjoint, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WeakDual.extendRCLikeL_apply_apply, ContinuousLinearMap.pullbackFunctional_apply,
    ContinuousLinearMap.pullbackFunctional_apply]
  change (ψ (ℜ a) : ℂ) - Complex.I * (ψ (ℜ (Complex.I • a)) : ℂ) =
    (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ)
  rw [realPart_I_smul, map_neg, Complex.ofReal_neg, mul_neg, sub_neg_eq_add]

/-- On a self-adjoint element `a`, `extendFromSelfAdjoint ψ` evaluates to `(ψ a : ℂ)`. -/
theorem extendFromSelfAdjoint_apply_coe (ψ : WeakDual ℝ (selfAdjoint A)) (a : selfAdjoint A) :
    extendFromSelfAdjoint ψ (a : A) = (ψ a : ℂ) := by
  rw [extendFromSelfAdjoint_apply, selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe,
    map_zero, Complex.ofReal_zero, mul_zero, add_zero]

/-- Any complex-linear functional on `A` that agrees with `(ψ · : ℂ)` on `selfAdjoint A` equals
`extendFromSelfAdjoint ψ`. -/
theorem eq_extendFromSelfAdjoint_of_forall_apply_coe {φ : WeakDual ℂ A}
    {ψ : WeakDual ℝ (selfAdjoint A)} (h : ∀ a : selfAdjoint A, φ (a : A) = (ψ a : ℂ)) :
    φ = extendFromSelfAdjoint ψ := by
  refine DFunLike.ext _ _ fun a => ?_
  calc
    φ a = φ ((ℜ a : A) + Complex.I • (ℑ a : A)) := by rw [realPart_add_I_smul_imaginaryPart]
    _ = φ (ℜ a : A) + Complex.I * φ (ℑ a : A) := by rw [map_add, map_smul, smul_eq_mul]
    _ = (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ) := by rw [h (ℜ a), h (ℑ a)]
    _ = extendFromSelfAdjoint ψ a := (extendFromSelfAdjoint_apply ψ a).symm

/-- `extendFromSelfAdjoint ψ` is the unique complex-linear functional on `A` whose value at each
self-adjoint element `a` is `(ψ a : ℂ)`. -/
theorem existsUnique_forall_apply_coe_eq (ψ : WeakDual ℝ (selfAdjoint A)) :
    ∃! φ : WeakDual ℂ A, ∀ a : selfAdjoint A, φ (a : A) = (ψ a : ℂ) :=
  ⟨extendFromSelfAdjoint ψ, extendFromSelfAdjoint_apply_coe ψ,
    fun _ h => eq_extendFromSelfAdjoint_of_forall_apply_coe h⟩

/-- Restricting the complex-linear extension of `ψ` recovers `ψ`. -/
@[simp]
theorem restrictToSelfAdjoint_extendFromSelfAdjoint (ψ : WeakDual ℝ (selfAdjoint A)) :
    restrictToSelfAdjoint (extendFromSelfAdjoint ψ) = ψ :=
  DFunLike.ext _ _ fun a => by simp

/-- Any complex-linear functional that is real-valued on `selfAdjoint A` is recovered by extending
its restriction `restrictToSelfAdjoint φ`. -/
theorem extendFromSelfAdjoint_restrictToSelfAdjoint {φ : WeakDual ℂ A}
    (hre : ∀ a : selfAdjoint A, (φ (a : A)).im = 0) :
    extendFromSelfAdjoint (restrictToSelfAdjoint φ) = φ := by
  refine (eq_extendFromSelfAdjoint_of_forall_apply_coe fun a => ?_).symm
  rw [restrictToSelfAdjoint_apply]
  exact Complex.ext rfl (by simp [hre a])

end Extend

end WeakDual
