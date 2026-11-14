/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Probability.Distributions.BetaGas.Normalizability

/-!
# Beta-gas normalizability tests

Smoke tests for the general-potential logarithmic-growth API.
-/

namespace TauCeti.Probability

open MeasureTheory Real

variable {n : ℕ} {β β' : ℝ} {V : ℝ → ℝ}
variable (hβ : 0 < β) (hβ' : 1 < β') (hββ' : β ≤ β') (hV : Continuous V)
variable (hliminf :
  ((2 * β' / β : ℝ) : EReal) <
    Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
      (Filter.comap (fun x : ℝ => |x|) Filter.atTop))

example (hint : Integrable (betaGasWeight n β V)
    (volume : Measure (Fin n → ℝ))) :
    0 < betaGasPartitionFunction n β V :=
  betaGasPartitionFunction_pos_of_integrable n β V hint

example (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : ¬ Integrable (betaGasWeight n β V) (volume : Measure (Fin n → ℝ)))
    (x : Fin n → ℝ) : betaGasPDFReal n β V x = 0 := by
  rw [betaGasPDFReal_def, betaGasPartitionFunction_def, integral_undef hint, div_zero]

example (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : ¬ Integrable (betaGasWeight n β V) (volume : Measure (Fin n → ℝ))) :
    betaGasMeasure n β V = 0 := by
  ext s
  rw [betaGasMeasure_apply]
  have hdensity : betaGasPDFReal n β V = 0 := by
    funext x
    simp only [Pi.zero_apply, betaGasPDFReal_def, betaGasPartitionFunction_def,
      integral_undef hint, div_zero]
  simp [hdensity]

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

end TauCeti.Probability
