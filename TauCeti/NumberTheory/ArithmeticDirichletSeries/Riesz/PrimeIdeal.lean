/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Ideal

/-!
# First Riesz sums of the ideal von Mangoldt function

The smoothed prime-ideal count is the difference of two ordinary prime-power sums. This
separates the harmonic sum that produces the logarithmic main term from the Chebyshev sum.
-/

public section

open scoped NumberField nonZeroDivisors

namespace TauCeti

/-- The first Riesz sum of the ideal von Mangoldt coefficients is `y` times their harmonic
sum, minus the inclusive Chebyshev count. In particular, this Riesz sum is real. -/
theorem rieszSum_normCoeff_vonMangoldt_eq (K : Type*) [Field K] [NumberField K] (y : ℝ) :
    rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y =
      ((y * primePowerSummatory K
        (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) y -
          primePsi K Set.univ y : ℝ) : ℂ) := by
  rw [← sum_idealsLE_mul_div_absNorm_sub_one_eq_rieszSum_normCoeff,
    ← idealSummatory_apply K]
  rw [idealSummatory_eq_primePowerSummatory K _
    (fun A ↦ (primePowerWeight A : ℂ) * ((y : ℂ) / Ideal.absNorm (A : Ideal (𝓞 K)) - 1))
    (fun A ↦ by rw [vonMangoldt_eq_primePowerWeight])
    (fun I hI ↦ by rw [IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI,
      zero_mul])]
  simp only [primePsi_apply, Set.mem_univ, Set.ofPred_true, Set.indicator_univ,
    primePowerSummatory_apply, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_div, Complex.ofReal_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun A _ ↦ by ring

end TauCeti
