/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Basic
public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Recurrence
public import TauCeti.Probability.MarkovChain.NullRecurrence
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Analysis.SpecificLimits.CentralBinomial
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Infinite mean return time and null recurrence of nearest-neighbor integer walks

Every nearest-neighbor integer walk `integerWalk p` (`p : unitInterval`) has infinite
extended mean first positive return time, with no symmetry assumption on `p`. For the
symmetric walk (`p = 1 / 2`), central binomial return probabilities tend to zero, so their
Cesàro averages vanish whereas the occupation strong law identifies their limit with the
reciprocal extended mean return time; a finite mean would give a positive reciprocal. For
every biased walk (`p ≠ 1 / 2`), including the deterministic endpoints `0` and `1`, the
walk is transient and therefore also has infinite mean return time.

Combining this unconditional infinite-mean formula with the return-series recurrence
criterion classifies every integer walk across the recurrence trichotomy:

* no state of `integerWalk p` is positive recurrent for any `p : unitInterval`;
* `integerWalk p` is null recurrent if and only if `(p : ℝ) = 1 / 2`;
* every finite `(integerWalk p)`-invariant measure is zero, so no integer walk admits an
  invariant probability measure.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.6, 1.7, and 1.10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace TauCeti.Probability

/-- Return probabilities of the symmetric integer walk tend to zero, including along
odd times, when they vanish identically. -/
theorem tendsto_integerWalk_pow_real_self (p : unitInterval) (hp : (p : ℝ) = 1 / 2)
    (x : ℤ) :
    Tendsto (fun n : ℕ => ((integerWalk p ^ n) x).real {x}) atTop (𝓝 0) := by
  have heven (n : ℕ) : ((integerWalk p ^ (2 * n)) x).real {x} =
      (n.centralBinom : ℝ) / 4 ^ n := by
    rw [measureReal_def, integerWalk_pow_even_apply_self]
    have hpow : ((2 * n).choose n : ℝ) * (p : ℝ) ^ n * (1 - (p : ℝ)) ^ n =
        (n.centralBinom : ℝ) / 4 ^ n := by
      rw [hp, mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 by norm_num,
        div_pow, one_pow, mul_one_div, Nat.centralBinom_eq_two_mul_choose]
    rw [hpow, ENNReal.toReal_ofReal (by positivity)]
  have hbound (n : ℕ) : ((integerWalk p ^ n) x).real {x} ≤
      ((n / 2).centralBinom : ℝ) / 4 ^ (n / 2) := by
    have hm := Nat.mod_lt n (by omega : 0 < 2)
    rcases (by omega : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1) with h | h
    · conv_lhs => rw [h]
      rw [heven]
    · conv_lhs => rw [h]
      simp only [measureReal_def, integerWalk_pow_odd_apply_self, ENNReal.toReal_zero]
      positivity
  exact squeeze_zero (fun _ => measureReal_nonneg) hbound
    (TauCeti.tendsto_centralBinom_div_four_pow.comp (Nat.tendsto_div_const_atTop (by omega)))

private theorem tendsto_integerWalk_integral_visitCount_div (p : unitInterval)
    (hp : (p : ℝ) = 1 / 2) (x : ℤ) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) x n : ℝ) / n
      ∂markovChainLaw (Measure.dirac x) (integerWalk p)) atTop (𝓝 0) := by
  simp_rw [integral_div, (integerWalk p).integral_visitCount_succ_markovChainLaw_dirac]
  simpa only [div_eq_inv_mul, Function.comp_apply] using
    ((tendsto_integerWalk_pow_real_self p hp x).comp (tendsto_add_atTop_nat 1)).cesaro

/-- The extended mean first positive return time of every nearest-neighbor integer walk is
infinite, for both symmetric and biased parameters (including the deterministic endpoints). -/
-- Simplify before the endpoint rules replace `integerWalk` by a deterministic kernel.
@[simp↓]
theorem integerWalk_meanReturnTime_eq_top (p : unitInterval) (x : ℤ) :
    (integerWalk p).meanReturnTime x = ∞ := by
  by_cases hp : (p : ℝ) = 1 / 2
  · refine (Kernel.IsNullRecurrent.meanReturnTime_eq_top ?_)
    exact (integerWalk p).isNullRecurrent_iff_isRecurrent_and_tendsto_integral_visitCount_div_zero.2
      ⟨(integerWalk_isRecurrent_iff p x).mpr hp, tendsto_integerWalk_integral_visitCount_div p hp x⟩
  · exact ((integerWalk_isTransient_iff p x).mpr hp).meanReturnTime_eq_top

/-- No nearest-neighbor integer walk has a positive recurrent state. -/
@[simp↓]
theorem not_integerWalk_isPositiveRecurrent (p : unitInterval) (x : ℤ) :
    ¬ (integerWalk p).IsPositiveRecurrent x := by
  simp [Kernel.isPositiveRecurrent_iff, integerWalk_meanReturnTime_eq_top]

/-- **Null recurrence of the symmetric integer walk.** A nearest-neighbor integer walk is null
recurrent at `x` if and only if `(p : ℝ) = 1 / 2`. -/
@[simp↓]
theorem integerWalk_isNullRecurrent_iff (p : unitInterval) (x : ℤ) :
    (integerWalk p).IsNullRecurrent x ↔ (p : ℝ) = 1 / 2 := by
  simp [Kernel.isNullRecurrent_iff, integerWalk_isRecurrent_iff, integerWalk_meanReturnTime_eq_top]

/-- Every finite invariant measure of any nearest-neighbor integer walk is zero. -/
theorem integerWalk_invariant_eq_zero {p : unitInterval} {μ : Measure ℤ} [IsFiniteMeasure μ]
    (hμ : (integerWalk p).Invariant μ) :
    μ = 0 :=
  Measure.ext_of_singleton fun x =>
    hμ.apply_singleton_eq_zero_of_not_isPositiveRecurrent (not_integerWalk_isPositiveRecurrent p x)

/-- No nearest-neighbor integer walk admits an invariant probability measure. -/
theorem not_integerWalk_invariant_of_isProbabilityMeasure (p : unitInterval) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] :
    ¬ (integerWalk p).Invariant μ :=
  fun hμ => IsProbabilityMeasure.ne_zero μ (integerWalk_invariant_eq_zero hμ)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Every realization of any nearest-neighbor integer walk has infinite extended mean first
positive return. No symmetry assumption on `p` or topology on the sample space is required. -/
theorem lintegral_integerWalk_hittingAfter_eq_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ → ℤ}
    {p : unitInterval} {x : ℤ}
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (integerWalk p)) P) :
    (∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω => X ω n) {x} 1 ω) ∂P) = ∞ := by
  have hτ : Measurable (hittingAfter (fun n (ω : ℕ → ℤ) => ω n) {x} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => ℤ)) (measurableSet_singleton x)).measurable'
  have hm := (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp hτ
  -- Entrance times depend only on the coordinate path; evaluation after composition
  -- therefore identifies the integrand with the canonical path functional.
  convert (hX.lintegral_comp hm.aemeasurable).trans
    (by simpa only [Kernel.meanReturnTime_def, Function.comp_def] using
      integerWalk_meanReturnTime_eq_top p x) using 1
  apply lintegral_congr
  intro ω
  simp only [Function.comp_apply, hittingAfter_def]

end ProbabilityTheory.HasLaw
