/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Mixed.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Small-rate estimates for Poisson counts

Factorial moments bound the probability of at least `k` occurrences by `r ^ k / k!`.
In particular, two or more occurrences have probability at most `r² / 2`, whereas the
one-occurrence probability differs from `r` by at most `r²`. Both errors are therefore
of smaller order than the rate at zero, including the zero-rate boundary.

For a finite collection of counts the multiple-occurrence bound needs no independence.
Applied to `n` counts of rate `a / n`, it shows that the probability of any cell containing
multiple occurrences tends to zero. This is the subdivision estimate used in microscopic
characterizations of Poisson processes; no process construction is assumed here.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 6.
-/

public section

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology NNReal Nat

namespace TauCeti.Probability

/-- The factorial-moment bound for the upper tail of a Poisson count. It also holds at `k = 0`
and at rate zero. -/
theorem poissonMeasure_real_Ici_le (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real (Set.Ici k) ≤ (r : ℝ) ^ k / k ! := by
  have hint : Integrable (fun n : ℕ => (n.descFactorial k : ℝ)) (poissonMeasure r) := by
    simpa only [mixedPoissonMeasure_dirac] using
      (integrable_descFactorial_mixedPoissonMeasure_iff
        (ρ := Measure.dirac r) k).2 (integrable_dirac (by simp))
  have hmoment : ∫ n : ℕ, (n.descFactorial k : ℝ) ∂poissonMeasure r = (r : ℝ) ^ k := by
    simpa only [mixedPoissonMeasure_dirac, integral_dirac] using
      integral_descFactorial_mixedPoissonMeasure (Measure.dirac r) k
  have hle := integral_mono ((integrable_const (k ! : ℝ)).indicator
    (measurableSet_Ici (a := k))) hint (fun n => ?_)
  · rw [integral_indicator_const _ measurableSet_Ici, hmoment, smul_eq_mul] at hle
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < k !)).2 hle
  · by_cases hn : n ∈ Set.Ici k
    · simp only [Set.indicator_of_mem hn]
      exact_mod_cast (Nat.descFactorial_self k ▸ Nat.descFactorial_le k hn)
    · simp only [Set.indicator_of_notMem hn]
      positivity

/-- Two or more occurrences have probability at most half the squared rate. -/
theorem poissonMeasure_real_Ici_two_le (r : ℝ≥0) :
    (poissonMeasure r).real (Set.Ici 2) ≤ (r : ℝ) ^ 2 / 2 := by
  simpa using poissonMeasure_real_Ici_le r 2

/-- The error in replacing the one-occurrence probability by the rate is at most the
squared rate, uniformly for all nonnegative rates. -/
theorem abs_poissonMeasure_real_singleton_one_sub_le (r : ℝ≥0) :
    |(poissonMeasure r).real {1} - r| ≤ (r : ℝ) ^ 2 := by
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr r.coe_nonneg)
  have hl := Real.one_sub_le_exp_neg (r : ℝ)
  rw [poissonMeasure_real_singleton]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [abs_of_nonpos (by nlinarith [r.coe_nonneg])]
  nlinarith [mul_le_mul_of_nonneg_left hl r.coe_nonneg]

/-- The one-occurrence probability is `r + o(r)` as the nonnegative rate tends to zero. -/
theorem isLittleO_poissonMeasure_real_singleton_one_sub :
    (fun r : ℝ≥0 => (poissonMeasure r).real {1} - r) =o[𝓝 0] fun r => (r : ℝ) := by
  refine (isBigO_of_le (𝓝 0) (g := fun r : ℝ≥0 => (r : ℝ) ^ 2) fun r => ?_).trans_isLittleO
    ((isLittleO_pow_id one_lt_two).comp_tendsto
      (NNReal.continuous_coe.tendsto' 0 0 rfl))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (r : ℝ))] using
    abs_poissonMeasure_real_singleton_one_sub_le r

/-- The multiple-occurrence probability is `o(r)` as the nonnegative rate tends to zero. -/
theorem isLittleO_poissonMeasure_real_Ici_two :
    (fun r : ℝ≥0 => (poissonMeasure r).real (Set.Ici 2)) =o[𝓝 0] fun r => (r : ℝ) := by
  refine (isBigO_of_le' (𝓝 0) (c := (1 / 2 : ℝ))
    (g := fun r : ℝ≥0 => (r : ℝ) ^ 2) fun r => ?_).trans_isLittleO
    ((isLittleO_pow_id one_lt_two).comp_tendsto
      (NNReal.continuous_coe.tendsto' 0 0 rfl))
  simpa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    abs_of_nonneg (sq_nonneg (r : ℝ)), div_eq_mul_inv, mul_comm] using
    poissonMeasure_real_Ici_two_le r

/-- A union bound for multiple occurrences in finitely many Poisson counts. Neither
independence nor equal rates are required. -/
theorem measureReal_exists_two_le_of_hasLaw {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) :
    P.real {ω | ∃ i, 2 ≤ X i ω} ≤ ∑ i, (r i : ℝ) ^ 2 / 2 := by
  have hevent : {ω | ∃ i, 2 ≤ X i ω} = ⋃ i, {ω | 2 ≤ X i ω} := by ext; simp
  rw [hevent]
  refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [(hX i).measureReal_eq (p := fun n => 2 ≤ n) .of_discrete]
  exact poissonMeasure_real_Ici_two_le (r i)

/-- With rate `a / n` in each of `n` cells, the probability of any multiple occurrence
vanishes as the subdivision is refined. The counts need not be independent. -/
theorem tendsto_measureReal_exists_two_div_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (a : ℝ≥0) {X : (n : ℕ) → Fin n → Ω → ℕ}
    (hX : ∀ n i, HasLaw (X n i) (poissonMeasure (a / n)) P) :
    Tendsto (fun n => P.real {ω | ∃ i, 2 ≤ X n i ω}) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat ((a : ℝ) ^ 2 / 2))
  refine (measureReal_exists_two_le_of_hasLaw (hX n)).trans ?_
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NNReal.coe_div, NNReal.coe_natCast]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact le_of_eq (by field_simp)

end TauCeti.Probability
