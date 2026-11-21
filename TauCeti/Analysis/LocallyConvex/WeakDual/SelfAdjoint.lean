/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
public import TauCeti.Topology.Algebra.Module.Star

/-!
# Restriction and extension of functionals on self-adjoint elements

For a topological complex star module `A`, taking the real part restricts a complex-linear
functional `φ : WeakDual ℂ A` to a real-linear functional on `selfAdjoint A`
(`WeakDual.restrictToSelfAdjoint`). Conversely, any real-linear functional
`ψ : WeakDual ℝ (selfAdjoint A)` extends uniquely to a complex-linear functional on `A` via
`a ↦ ψ (ℜ a) + I * ψ (ℑ a)` (`WeakDual.extendFromSelfAdjoint`), and restricting the extension
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
  [TopologicalSpace A]

/-- Restriction of a complex-linear functional on `A` to a real-linear functional on
`selfAdjoint A`, taking the real part, as a weak-star continuous real-linear map. -/
noncomputable def restrictToSelfAdjoint : WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A) where
  toFun φ := StrongDual.toWeakDual
    { toFun := fun a => (φ (a : A)).re
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        -- Coerce the real scalar action on `selfAdjoint A` to complex scalar multiplication in `A`.
        change (φ ((r : ℂ) • (a : A))).re = r * (φ (a : A)).re
        rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]
      cont := Complex.continuous_re.comp ((toStrongDual φ).continuous.comp continuous_subtype_val) }
  map_add' _ _ := DFunLike.ext _ _ fun _ => by simp
  map_smul' r φ := DFunLike.ext _ _ fun a => by
    -- Unfold pointwise real scaling in `WeakDual ℂ A`.
    change ((r • φ) (a : A)).re = r * (φ (a : A)).re
    simp
  cont := continuous_of_continuous_eval fun a =>
    Complex.continuous_re.comp (eval_continuous (a : A))

/-- Evaluating `restrictToSelfAdjoint φ` at a self-adjoint element `a` yields `(φ a).re`. -/
@[simp]
theorem restrictToSelfAdjoint_apply (φ : WeakDual ℂ A) (a : selfAdjoint A) :
    restrictToSelfAdjoint φ a = (φ (a : A)).re :=
  (rfl)

end Restrict

section Extend

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousSub A] [ContinuousStar A]
  [ContinuousConstSMul ℂ A]

/-- Unique complex-linear extension of a real-linear functional on `selfAdjoint A` to `A`,
given by `a ↦ ψ (ℜ a) + I * ψ (ℑ a)`, as a weak-star continuous real-linear map. -/
noncomputable def extendFromSelfAdjoint : WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A where
  toFun ψ := StrongDual.toWeakDual
    { toFun := fun a => (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ)
      map_add' := fun a b => by simp [mul_add]; ring
      map_smul' := fun z a => by
        rw [realPart_smul, imaginaryPart_smul]
        simp only [map_sub, map_add, map_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_add,
          Complex.ofReal_mul]
        apply Complex.ext <;> simp
      cont := by
        have : ContinuousConstSMul ℝ A :=
          ⟨fun r => by simpa only [← Complex.coe_smul] using continuous_const_smul (r : ℂ)⟩
        exact (Complex.continuous_ofReal.comp
            ((toStrongDual ψ).continuous.comp continuous_realPart)).add
          (continuous_const.mul
            (Complex.continuous_ofReal.comp
              ((toStrongDual ψ).continuous.comp continuous_imaginaryPart))) }
  map_add' ψ₁ ψ₂ := DFunLike.ext _ _ fun a => by
    -- Unfold pointwise addition of functionals in `WeakDual ℂ A`.
    change (((ψ₁ + ψ₂) (ℜ a) : ℂ) + Complex.I * ((ψ₁ + ψ₂) (ℑ a) : ℂ)) =
      ((ψ₁ (ℜ a) : ℂ) + Complex.I * (ψ₁ (ℑ a) : ℂ)) +
        ((ψ₂ (ℜ a) : ℂ) + Complex.I * (ψ₂ (ℑ a) : ℂ))
    simp only [add_apply, Complex.ofReal_add]
    ring
  map_smul' r ψ := DFunLike.ext _ _ fun a => by
    -- Unfold real scalar multiplication on `WeakDual ℝ (selfAdjoint A)` and `WeakDual ℂ A`.
    change (((r • ψ) (ℜ a) : ℂ) + Complex.I * ((r • ψ) (ℑ a) : ℂ)) =
      (r • (StrongDual.toWeakDual _)) a
    rw [WeakDual.real_smul_apply]
    simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
    change (r : ℂ) * (ψ (ℜ a) : ℂ) + Complex.I * ((r : ℂ) * (ψ (ℑ a) : ℂ)) =
      (r : ℂ) * ((ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ))
    ring
  cont := continuous_of_continuous_eval fun a =>
    (Complex.continuous_ofReal.comp (eval_continuous (ℜ a))).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (eval_continuous (ℑ a))))

/-- Evaluating `extendFromSelfAdjoint ψ` at `a` gives `ψ (ℜ a) + I * ψ (ℑ a)`. -/
@[simp]
theorem extendFromSelfAdjoint_apply (ψ : WeakDual ℝ (selfAdjoint A)) (a : A) :
    extendFromSelfAdjoint ψ a = (ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ) :=
  (rfl)

/-- Restricting the complex-linear extension of `ψ` recovers `ψ`. -/
@[simp]
theorem restrictToSelfAdjoint_extendFromSelfAdjoint (ψ : WeakDual ℝ (selfAdjoint A)) :
    restrictToSelfAdjoint (extendFromSelfAdjoint ψ) = ψ :=
  DFunLike.ext _ _ fun a => by simp

end Extend

end WeakDual
