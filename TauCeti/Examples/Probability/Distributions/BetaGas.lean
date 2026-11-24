/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Probability.Distributions.BetaGas.Normalizability
import TauCeti.Probability.Distributions.BetaGas.PartitionFunction
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Beta-gas normalizability tests

Smoke tests for the general-potential logarithmic-growth API.
-/

namespace TauCeti.Probability

open _root_.MeasureTheory Real

variable {n : ℕ} {β β' : ℝ} {V : ℝ → ℝ}
variable (hβ : 0 < β) (hβ' : 1 < β') (hββ' : β ≤ β') (hV : Continuous V)
variable (hliminf :
  ((2 * β' / β : ℝ) : EReal) <
    Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
      (Filter.comap (fun x : ℝ => |x|) Filter.atTop))

example : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
    (-1 : ℝ) < (x ^ 2 / 2) / log |x| :=
  TauCeti.eventually_quadratic_div_log_abs_gt (-1)

example (hint : Integrable (betaGasWeight n β V)
    (volume : Measure (Fin n → ℝ))) :
    0 < betaGasPartitionFunction n β V :=
  betaGasPartitionFunction_pos_of_integrable n β V hint

example (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : ¬ Integrable (betaGasWeight n β V) (volume : Measure (Fin n → ℝ)))
    (x : Fin n → ℝ) : betaGasPDFReal n β V x = 0 := by
  simp [betaGasPDFReal_eq_zero_of_not_integrable n β V hint]

example (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : ¬ Integrable (betaGasWeight n β V) (volume : Measure (Fin n → ℝ))) :
    betaGasMeasure n β V = 0 := by
  ext s
  rw [betaGasMeasure_apply]
  simp [betaGasPDFReal_eq_zero_of_not_integrable n β V hint]

example (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    IsFiniteMeasure (betaGasMeasure n β V) := inferInstance

example (n : ℕ) (β : ℝ) : Measurable (gaussianBetaGasPDFReal n β) := by
  fun_prop

example (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gaussianBetaGasPDFReal n β) := by
  fun_prop

example : Integrable (betaGasWeight n β V)
    (volume : Measure (Fin n → ℝ)) :=
  integrable_betaGasWeight_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf

example : 0 < betaGasPartitionFunction n β V :=
  betaGasPartitionFunction_pos_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf

example : IsProbabilityMeasure (betaGasMeasure n β V) :=
  isProbabilityMeasure_betaGasMeasure_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf

example : (∫ x, betaGasPDFReal n β V x
    ∂(volume : Measure (Fin n → ℝ))) = 1 :=
  integral_betaGasPDFReal_eq_one n β V
    (betaGasPartitionFunction_pos_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf)

example : IsProbabilityMeasure (gaussianBetaGasMeasure 0 β) :=
  isProbabilityMeasure_gaussianBetaGasMeasure 0 hβ

example : ¬ Integrable (fun x : ℝ => |x| ^ (-1 : ℝ) * exp (-1 * x ^ 2)) := by
  intro h
  have hparams := TauCeti.integrable_abs_rpow_mul_exp_neg_mul_sq_iff.mp h
  norm_num at hparams

example : ¬ Integrable (fun x : ℝ => |x| ^ (0 : ℝ) * exp (-0 * x ^ 2)) := by
  intro h
  have hparams := TauCeti.integrable_abs_rpow_mul_exp_neg_mul_sq_iff.mp h
  norm_num at hparams

example : gaussianBetaGasPartitionFunction 2 1 = 4 * sqrt π := by
  rw [gaussianBetaGasPartitionFunction_two_eq (by norm_num : (0 : ℝ) < 1)]
  norm_num [Real.Gamma_one, Real.rpow_natCast]

example : gaussianBetaGasPartitionFunction 2 2 = π := by
  have hGamma : Gamma (3 / 2 : ℝ) = sqrt π / 2 := by
    have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    rw [Real.Gamma_one_half_eq] at h
    convert h using 1 <;> norm_num
    ring
  rw [gaussianBetaGasPartitionFunction_two_eq (by norm_num : (0 : ℝ) < 2)]
  norm_num [Real.rpow_natCast, Real.rpow_neg, hGamma]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

end TauCeti.Probability
