/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.PrimeIdeal
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.EulerKronecker
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
import TauCeti.NumberTheory.LFunctions.Mertens

/-!
# Linear growth of the first Dedekind zeta Riesz remainder

Mertens' first theorem over a number field gives a uniform linear bound for the first
Riesz sum of its ideal von Mangoldt coefficients after subtraction of the Dedekind zeta
main term. The bound does not require an explicit formula over zeros.

For the normalization over `ℚ`, see L. Alpöge, *The Riemann hypothesis*, `Deduction.Gchi`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Asymptotics Filter NumberField Set

namespace TauCeti.LFunctions

/-- The first Riesz remainder for `ζ_K`, obtained by subtracting `y log y` and adding
`(1 + EK(K)) y`, is bounded in norm by `C y` uniformly for `y ≥ 1`. -/
theorem exists_norm_rieszSum_normCoeff_vonMangoldt_sub_mul_log_add_le (K : Type*)
    [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y -
        (y * Real.log y : ℝ) + ((1 + eulerKroneckerConstant K) * y : ℝ)‖ ≤ C * y := by
  let R : ℝ → ℂ := fun y ↦ rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y -
    (y * Real.log y : ℝ) + ((1 + eulerKroneckerConstant K) * y : ℝ)
  have hR (y : ℝ) : R y = ((y * (primePowerSummatory K
        (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) y - Real.log y) -
        primePsi K univ y + (1 + eulerKroneckerConstant K) * y : ℝ) : ℂ) := by
    dsimp only [R]
    rw [rieszSum_normCoeff_vonMangoldt_eq]
    push_cast
    ring
  have hM := (isBigO_refl (fun y : ℝ ↦ y) atTop).mul
    (isBigO_primePowerSummatory_div_sub_log K)
  have hE := isBigO_const_mul_self (1 + eulerKroneckerConstant K) (fun y : ℝ ↦ y) atTop
  have hO : R =O[atTop] (fun y : ℝ ↦ y) := by
    have h := (hM.congr_right (fun _ ↦ mul_one _)).sub (primeIdealTheorem K).1.isBigO
    exact (Complex.isBigO_ofReal_left.mpr (h.add hE)).congr_left (fun y ↦ (hR y).symm)
  have hcont : Continuous R :=
    ((continuous_rieszSum _).sub (Complex.continuous_ofReal.comp Real.continuous_mul_log)).add
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
  have hO' := hO.isBigO_principal_Ici_of_continuousOn (a := 1)
    hcont.continuousOn continuous_id.continuousOn fun y hy ↦
      norm_ne_zero_iff.mpr (zero_lt_one.trans_le (mem_Ici.mp hy)).ne'
  obtain ⟨C, hC₀, hC⟩ := hO'.exists_nonneg
  exact ⟨C, hC₀, fun y hy ↦ by
    simpa only [Real.norm_of_nonneg (zero_le_one.trans hy)] using
      isBigOWith_principal.mp hC y hy⟩

end TauCeti.LFunctions
