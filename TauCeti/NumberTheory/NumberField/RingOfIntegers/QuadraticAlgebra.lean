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

/-- An algebraic integer generating `𝓞 K` over `ℤ` and not lying in `ℚ` presents `𝓞 K` as an
integral quadratic algebra. -/
noncomputable def ringOfIntegersAlgEquivOfAdjoin {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) :
    𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b :=
  (AlgEquiv.ofBijective (QuadraticAlgebra.lift ⟨g, hg_sq⟩)
    (show Function.Bijective (QuadraticAlgebra.lift ⟨g, hg_sq⟩) from by
      refine ⟨(QuadraticAlgebra.lift_injective_iff hg_sq).mpr ?_,
        (QuadraticAlgebra.lift_surjective_iff hg_sq).mpr hg_top⟩
      rw [LinearIndependent.pair_iff]
      intro s t h
      have hK : (s : K) + (t : K) * (g : K) = 0 := by
        simpa [zsmul_eq_mul] using congrArg (algebraMap (𝓞 K) K) h
      have ht : t = 0 := by
        by_contra hne
        refine hg_notMem ⟨-(s : ℚ) / (t : ℚ), ?_⟩
        rw [show algebraMap ℚ K (-(s : ℚ) / (t : ℚ)) = -(s : K) / (t : K) by simp,
          div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hK
      exact ⟨by exact_mod_cast (by simpa [ht] using hK : (s : K) = 0), ht⟩)).symm

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
