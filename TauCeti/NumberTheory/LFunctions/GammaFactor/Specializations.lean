/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.GammaFactor.Vertical
public import TauCeti.NumberTheory.LFunctions.Data.Normalization
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
import TauCeti.NumberTheory.LFunctions.GammaFactor.Order

/-!
# Normalization and Riemann zeta specializations for archimedean gamma asymptotics

Translating an arithmetic L-function record of weight `w` to the analytic normalization shifts the
evaluation point of `AnalyticLFunctionData.gammaLogExponent` by `+w / 2`, matching
`NormalizationTranslation.analytic_analyticConductorAt`. For `riemannZetaData` (`gammaR = {0}`,
`gammaC = 0`), the logarithmic height exponent is `(σ - 1) / 2`.
-/

public section

open Complex Filter Set Asymptotics

namespace TauCeti.LFunctions

/-- Translating an arithmetic record of weight `w` to the analytic normalization shifts
`gammaLogExponent`'s evaluation point by `+w / 2`, matching
`NormalizationTranslation.analytic_analyticConductorAt`. -/
@[simp]
theorem NormalizationTranslation.analytic_gammaLogExponent (T : NormalizationTranslation)
    (σ : ℝ) :
    T.analytic.gammaLogExponent σ =
      T.arithmetic.toAnalyticLFunctionData.gammaLogExponent (σ + (T.weight : ℝ) / 2) := by
  simp only [AnalyticLFunctionData.gammaLogExponent_def, T.gammaR_eq, T.gammaC_eq,
    Multiset.map_map, Function.comp_def]
  congr 1 <;> congr 1 <;> refine Multiset.map_congr rfl fun z _ ↦ ?_ <;> simp <;> ring

/-- For the Riemann zeta record (`gammaR = {0}`, `gammaC = 0`), the logarithmic height exponent is
`(σ - 1) / 2`. -/
@[simp]
theorem riemannZetaData_gammaLogExponent (σ : ℝ) :
    riemannZetaData.gammaLogExponent σ = (σ - 1) / 2 := by
  simp [AnalyticLFunctionData.gammaLogExponent_def]

-- Vertical-strip asymptotic check for `riemannZetaData.gammaFactor`:
-- `log ‖Gammaℝ (σ + i t)‖ = -(π / 4) |t| + ((σ - 1) / 2) log |t| + O(1)` uniformly on `[a, b]`.
example (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Gammaℝ (p.1 + p.2 * I)‖ -
        (-(Real.pi / 4) * |p.2| + (p.1 - 1) / 2 * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  simpa using riemannZetaData.isBigO_log_norm_gammaFactor_vertical_sub a b

-- Dual gamma-quotient asymptotic check for `riemannZetaData` on `Re s = -δ`:
-- `log ‖Gammaℝ (1 - (-δ + i t)) / Gammaℝ (-δ + i t)‖ = ((1 + 2 δ) / 2) log |t| + O(1)`.
example (δ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Gammaℝ (1 - ((-δ : ℝ) + t * I)) / Gammaℝ ((-δ : ℝ) + t * I)‖ -
        (1 + 2 * δ) / 2 * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  have heq : (fun t : ℝ ↦ Real.log ‖Gammaℝ (1 - ((-δ : ℝ) + t * I)) / Gammaℝ ((-δ : ℝ) + t * I)‖ -
      (1 + 2 * δ) / 2 * Real.log |t|) =
      (fun t : ℝ ↦
        Real.log ‖riemannZetaData.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
            riemannZetaData.gammaFactor ((-δ : ℝ) + t * I)‖ -
          (riemannZetaData.degree : ℝ) / 2 * (1 + 2 * δ) * Real.log |t|) := by
    funext t
    simp only [riemannZetaData_dual, riemannZetaData_gammaFactor, riemannZetaData_degree,
      Nat.cast_one]
    ring
  rw [heq]
  exact riemannZetaData.isBigO_log_norm_dual_gammaFactor_div_neg_line_sub δ

-- Duplication check: two real gamma factors with shifts `{0, 1}` interleave into one `Gammaℂ`
-- factor, giving degree `2` (exponential rate `-π |t| / 2`), logarithmic exponent `σ - 1 / 2`,
-- and divisor `-1` at every nonpositive integer.
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 1}) (hC : d.gammaC = 0) :
    d.degree = 2 ∧
    (∀ σ : ℝ, d.gammaLogExponent σ = σ - 1 / 2) ∧
    (∀ s : ℂ, d.gammaFactor s = Gammaℂ s) ∧
    (∀ m : ℕ, MeromorphicOn.divisor d.gammaFactor Set.univ (-(m : ℂ)) = -1) := by
  refine ⟨by simp [AnalyticLFunctionData.degree_def, hR, hC], fun σ ↦ ?_, fun s ↦ ?_, fun m ↦ ?_⟩
  · simp [AnalyticLFunctionData.gammaLogExponent_def, hR, hC]
    ring
  · simp [AnalyticLFunctionData.gammaFactor_def, hR, hC, Gammaℝ_mul_Gammaℝ_add_one]
  · have hfg : d.gammaFactor = Gammaℂ := funext fun s ↦ by
      simp [AnalyticLFunctionData.gammaFactor_def, hR, hC, Gammaℝ_mul_Gammaℝ_add_one]
    rw [hfg, meromorphicOn_Gammaℂ.divisor_apply (Set.mem_univ _),
      (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff _).2 ⟨m, rfl⟩]
    simp

end TauCeti.LFunctions
