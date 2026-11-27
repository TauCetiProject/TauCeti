/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.Lipschitz

/-!
# Approximation by normalized Laplace coefficients

A normalized Taylor coefficient of a Laplace transform at a positive real rate `a` is a
Gamma average of the original function. The average at degree `k` is concentrated about
`(k + 1) / a`: for a function that is Lipschitz on the positive ray, the approximation error
is bounded by the Lipschitz constant times `√(k + 1) / a`.

This is the Gamma averaging step in Post–Widder inversion (D. V. Widder,
*The Laplace Transform*, Chapter VII), used in the Tauberian estimate
`New.norm_taylorCoeff_transform_sub_le_of_lipschitz` in
`Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped Nat NNReal Topology

namespace TauCeti

/-- At a positive real rate `a`, a normalized Laplace Taylor coefficient is the average
against the Gamma law of shape `k + 1` and rate `a`. At rate zero both sides vanish by
normalization and by the zero density, respectively. -/
theorem integral_gammaMeasure_eq_smul_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {F : ℂ → E} {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ᶠ z in 𝓝 (a : ℂ), HasLaplace f z (F z)) (k : ℕ) :
    (∫ x, f x ∂gammaMeasure (k + 1 : ℕ) a) =
      (((a : ℂ) ^ (k + 1) * (-1) ^ k / k !) • iteratedDeriv k F a) := by
  rcases ha.eq_or_lt with rfl | ha
  · have hz : gammaPDF (k + 1 : ℕ) 0 = 0 := by
      ext x
      by_cases hx : 0 ≤ x
      · rw [Pi.zero_apply, gammaPDF_of_nonneg hx, Real.rpow_natCast]
        simp
      · simp [gammaPDF_of_neg (not_le.mp hx)]
    rw [gammaMeasure, hz]
    simp
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hcoeff := (hasLaplace_pow_div_factorial_smul_iteratedDeriv hF k).const_smul
    ((a : ℂ) ^ (k + 1))
  rw [Probability.integral_gammaMeasure_eq_integral_Ioi hk ha f,
    mul_div_assoc, ← smul_smul, ← hcoeff.integral_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [Pi.smul_apply, smul_smul]
  rw [Real.rpow_natCast, Nat.cast_succ, add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial]
  rw [← IsScalarTower.algebraMap_smul ℂ, RCLike.algebraMap_eq_ofReal,
    RCLike.ofReal_eq_complex_ofReal]
  push_cast [Complex.ofReal_exp]
  congr 1
  rw [neg_mul]
  ring

/-- The Post–Widder coefficient of degree `k` at a positive rate `a` approximates the original
function at `(k + 1) / a` with error at most `K * √(k + 1) / a`, where `K` is a Lipschitz
constant on the positive ray. -/
theorem norm_smul_iteratedDeriv_sub_le_of_hasLaplace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ → E} {F : ℂ → E} {a : ℝ} (ha : 0 < a)
    (hF : ∀ᶠ z in 𝓝 (a : ℂ), HasLaplace f z (F z)) {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Ioi 0)) (k : ℕ) :
    ‖(((a : ℂ) ^ (k + 1) * (-1) ^ k / k !) • iteratedDeriv k F a) -
      f ((k + 1 : ℕ) / a)‖ ≤ (K : ℝ) * √(k + 1 : ℕ) / a := by
  rw [← integral_gammaMeasure_eq_smul_iteratedDeriv ha.le hF]
  exact Probability.norm_integral_gammaMeasure_sub_le (by positivity) ha hf

end TauCeti
