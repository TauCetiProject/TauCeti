/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import TauCeti.Topology.Algebra.Module.Star

/-!
# Restriction and extension of functionals on self-adjoint elements

For a topological complex star module `A`, taking the real part restricts a complex-linear
functional `φ : WeakDual ℂ A` to a real-linear functional on `selfAdjoint A`
(`WeakDual.restrictToSelfAdjoint`), defined by composing
`(WeakDual.extendRCLikeL (𝕜 := ℂ) (F := A)).symm` with pullback along `selfAdjoint.subtypeL ℝ A`.
Conversely, any
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
  [TopologicalSpace A] [ContinuousConstSMul ℂ A]

/-- Restriction of a complex-linear functional on `A` to a real-linear functional on
`selfAdjoint A`, taking the real part, as a weak-star continuous real-linear map. -/
noncomputable def restrictToSelfAdjoint : WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A) :=
  (selfAdjoint.subtypeL ℝ A).pullbackFunctional.comp
    (WeakDual.extendRCLikeL (𝕜 := ℂ) (F := A)).symm.toContinuousLinearMap

/-- Evaluating `restrictToSelfAdjoint φ` at a self-adjoint element `a` yields `(φ a).re`. -/
@[simp]
theorem restrictToSelfAdjoint_apply (φ : WeakDual ℂ A) (a : selfAdjoint A) :
    restrictToSelfAdjoint φ a = (φ (a : A)).re := by
  simp [restrictToSelfAdjoint, WeakDual.extendRCLikeL_symm_apply_apply]

end Restrict

section Extend

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul ℂ A]

/-- The unique complex-linear extension of `ψ : WeakDual ℝ (selfAdjoint A)` to `A` whose value at
every self-adjoint element `a : selfAdjoint A` is `(ψ a : ℂ)`, defined by
`a ↦ ψ (ℜ a) + I * ψ (ℑ a)` as a weak-star continuous real-linear map. -/
noncomputable def extendFromSelfAdjoint : WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A :=
  have := IsScalarTower.continuousConstSMul ℝ ℂ A
  (WeakDual.extendRCLikeL (𝕜 := ℂ) (F := A)).toContinuousLinearMap.comp
    (selfAdjointPartL ℝ A).pullbackFunctional

/-- Evaluating `extendFromSelfAdjoint ψ` at `a` gives `ψ (ℜ a) + I * ψ (ℑ a)`. -/
@[simp]
theorem extendFromSelfAdjoint_apply (ψ : WeakDual ℝ (selfAdjoint A)) (a : A) :
    extendFromSelfAdjoint ψ a = (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ) := by
  have := IsScalarTower.continuousConstSMul ℝ ℂ A
  simp [extendFromSelfAdjoint, WeakDual.extendRCLikeL_apply_apply, realPart_I_smul, sub_neg_eq_add]

/-- On a self-adjoint element `a`, `extendFromSelfAdjoint ψ` evaluates to `(ψ a : ℂ)`. -/
theorem extendFromSelfAdjoint_apply_coe (ψ : WeakDual ℝ (selfAdjoint A)) (a : selfAdjoint A) :
    extendFromSelfAdjoint ψ (a : A) = (ψ a : ℂ) := by
  simp [selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe]

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
