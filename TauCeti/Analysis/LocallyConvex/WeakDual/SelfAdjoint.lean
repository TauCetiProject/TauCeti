/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Restriction and extension of functionals on self-adjoint elements

For a topological complex star module `A`, taking the real part restricts a complex-linear
functional `φ : WeakDual ℂ A` to a real-linear functional on `selfAdjoint A`
(`WeakDual.restrictToSelfAdjoint`), defined by composing `WeakDual.extendRCLikeL.symm` with
pullback along the inclusion `selfAdjoint A →L[ℝ] A`. Conversely, any real-linear functional
`ψ : WeakDual ℝ (selfAdjoint A)` extends uniquely to a complex-linear functional on `A` via
`a ↦ ψ (ℜ a) + I * ψ (ℑ a)` (`WeakDual.extendFromSelfAdjoint`), defined by composing pullback
along `selfAdjointPartL ℝ A` with `WeakDual.extendRCLikeL`, and restricting the extension
recovers `ψ` (`WeakDual.restrictToSelfAdjoint_extendFromSelfAdjoint`).

## Main definitions and results

* `WeakDual.restrictToSelfAdjoint`: weak-star continuous real-linear restriction
  `WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A)`.
* `WeakDual.extendFromSelfAdjoint`: weak-star continuous real-linear extension
  `WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A`.
* `WeakDual.restrictToSelfAdjoint_apply`, `WeakDual.extendFromSelfAdjoint_apply`,
  `WeakDual.restrictToSelfAdjoint_extendFromSelfAdjoint`: evaluation and left-inverse identities.
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
  let incl : selfAdjoint A →L[ℝ] A :=
    { toLinearMap := (selfAdjoint.submodule ℝ A).subtype
      cont := continuous_subtype_val }
  incl.pullbackFunctional.comp
    (WeakDual.extendRCLikeL (𝕜 := ℂ) (F := A)).symm.toContinuousLinearMap

/-- Evaluating `restrictToSelfAdjoint φ` at a self-adjoint element `a` yields `(φ a).re`. -/
@[simp]
theorem restrictToSelfAdjoint_apply (φ : WeakDual ℂ A) (a : selfAdjoint A) :
    restrictToSelfAdjoint φ a = (φ (a : A)).re := by
  simp [restrictToSelfAdjoint, WeakDual.extendRCLikeL_symm_apply_apply]
  rfl

end Restrict

section Extend

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul ℂ A]

/-- Unique complex-linear extension of a real-linear functional on `selfAdjoint A` to `A`,
given by `a ↦ ψ (ℜ a) + I * ψ (ℑ a)`, as a weak-star continuous real-linear map. -/
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

/-- Restricting the complex-linear extension of `ψ` recovers `ψ`. -/
@[simp]
theorem restrictToSelfAdjoint_extendFromSelfAdjoint (ψ : WeakDual ℝ (selfAdjoint A)) :
    restrictToSelfAdjoint (extendFromSelfAdjoint ψ) = ψ :=
  DFunLike.ext _ _ fun a => by simp

end Extend

end WeakDual
