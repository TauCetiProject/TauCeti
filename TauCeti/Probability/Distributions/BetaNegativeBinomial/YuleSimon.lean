/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Basic
public import TauCeti.Probability.Distributions.YuleSimon.Basic
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Yule–Simon as a beta-negative-binomial law

Adding one to a beta-negative-binomial count with parameters `(1, ρ, 1)` gives the
Yule–Simon law of positive shape `ρ`. The shift reconciles the natural-number carrier
starting at zero with Yule–Simon's positive-integer support.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.10.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The successor of a beta-negative-binomial count with parameters `(1, ρ, 1)` has
Yule–Simon law of shape `ρ`. -/
theorem map_succ_betaNegativeBinomialMeasure {ρ : ℝ} (hρ : 0 < ρ) :
    (betaNegativeBinomialMeasure 1 ρ 1).map Nat.succ = yuleSimonMeasure ρ := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton n)]
  cases n with
  | zero =>
    have hpre : Nat.succ ⁻¹' {0} = ∅ := by ext k; simp
    simp [hpre]
  | succ k =>
    have hpre : Nat.succ ⁻¹' {k + 1} = {k} := by ext j; simp
    rw [hpre, betaNegativeBinomialMeasure_singleton (by norm_num) hρ (by norm_num),
      yuleSimonMeasure_singleton hρ, betaNegativeBinomialWeight_def, yuleSimonWeight_def]
    congr 1
    rw [betaNegativeBinomialWeightReal_of_ne_zero one_ne_zero, Real.Gamma_one, one_mul,
      add_comm (1 : ℝ) (k : ℝ), Real.Gamma_nat_eq_factorial,
      div_self (by positivity : (k.factorial : ℝ) ≠ 0), one_mul, beta_one_right hρ,
      yuleSimonWeightReal_def, Nat.cast_succ, beta_comm (ρ + 1) (k + 1)]
    simp [mul_comm]

/-- The successor of a natural-valued beta-negative-binomial variable with parameters
`(1, ρ, 1)` has Yule–Simon law. -/
theorem _root_.ProbabilityTheory.HasLaw.succ_yuleSimonMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ} {ρ : ℝ}
    (hX : HasLaw X (betaNegativeBinomialMeasure 1 ρ 1) P) (hρ : 0 < ρ) :
    HasLaw (fun ω ↦ Nat.succ (X ω)) (yuleSimonMeasure ρ) P := by
  rw [← map_succ_betaNegativeBinomialMeasure hρ]
  exact (hasLaw_map (by fun_prop : Measurable Nat.succ).aemeasurable).comp hX

end TauCeti.Probability
