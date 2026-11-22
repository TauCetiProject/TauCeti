/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Quadratic-algebra presentations of rings of integers

Any algebraic integer `g : 𝓞 K` satisfying a monic quadratic relation `g * g = a • 1 + b • g`
(`a, b : ℤ`) that generates `𝓞 K` over `ℤ` and does not lie in `ℚ` presents `𝓞 K` as the
integral quadratic algebra `QuadraticAlgebra ℤ a b`.

## Main results

* `TauCeti.NumberField.ringOfIntegersAlgEquivOfAdjoin`: `𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b`
  from a non-rational integral generator `g` of `𝓞 K`.
* `TauCeti.NumberField.ringOfIntegersAlgEquivOfAdjoin_symm_apply`: inverse evaluation
  `z ↦ z.re • 1 + z.im • g`.
* `TauCeti.NumberField.ringOfIntegersAlgEquivOfAdjoin_apply_gen`: sends `g` to
  `QuadraticAlgebra.omega`.
-/

public section

open NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

private theorem bijective_lift_of_adjoin {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) :
    Function.Bijective (QuadraticAlgebra.lift ⟨g, hg_sq⟩) := by
  refine ⟨?_, (QuadraticAlgebra.lift_surjective_iff _).mpr hg_top⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro z hz
  have hzK : (z.re : K) + (z.im : K) * (g : K) = 0 := by
    simpa [zsmul_eq_mul] using congrArg (algebraMap (𝓞 K) K) hz
  have him : z.im = 0 := by
    by_contra hne
    refine hg_notMem ⟨-(z.re : ℚ) / (z.im : ℚ), ?_⟩
    rw [show algebraMap ℚ K (-(z.re : ℚ) / (z.im : ℚ)) = -(z.re : K) / (z.im : K) by simp,
      div_eq_iff (by exact_mod_cast hne)]
    linear_combination -hzK
  exact QuadraticAlgebra.ext (by simpa [him] using hzK) him

/-- An algebraic integer generating `𝓞 K` over `ℤ` and not lying in `ℚ` presents `𝓞 K` as an
integral quadratic algebra. -/
noncomputable def ringOfIntegersAlgEquivOfAdjoin {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) :
    𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b :=
  (AlgEquiv.ofBijective (QuadraticAlgebra.lift ⟨g, hg_sq⟩)
    (bijective_lift_of_adjoin hg_sq hg_top hg_notMem)).symm

/-- The inverse of `ringOfIntegersAlgEquivOfAdjoin` sends `z` to `z.re • 1 + z.im • g`. -/
@[simp]
theorem ringOfIntegersAlgEquivOfAdjoin_symm_apply {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) (z : QuadraticAlgebra ℤ a b) :
    (ringOfIntegersAlgEquivOfAdjoin hg_sq hg_top hg_notMem).symm z = z.re • 1 + z.im • g := by
  rw [ringOfIntegersAlgEquivOfAdjoin, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply,
    QuadraticAlgebra.lift_apply_apply]

/-- `ringOfIntegersAlgEquivOfAdjoin` sends the generator `g` to `QuadraticAlgebra.omega`
(`⟨0, 1⟩`). -/
@[simp]
theorem ringOfIntegersAlgEquivOfAdjoin_apply_gen {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) :
    ringOfIntegersAlgEquivOfAdjoin hg_sq hg_top hg_notMem g = QuadraticAlgebra.omega :=
  (ringOfIntegersAlgEquivOfAdjoin hg_sq hg_top hg_notMem).symm.injective (by simp)

end TauCeti.NumberField
