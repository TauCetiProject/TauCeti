/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.Probability.Distributions.Beta.Measurability
public import TauCeti.Probability.Distributions.Binomial.Measurability

/-!
# The beta-binomial distribution

This file defines the beta-binomial law by mixing a binomial success probability against a Beta
law.  It proves normalization, the classical Beta-function mass formula, finite support, and
parameter measurability.  The binomial kernel is extended measurably to all real mixing values by
projection onto the unit interval; this choice is immaterial because Beta laws are concentrated on
the open unit interval.

## Main results

* `TauCeti.Probability.betaBinomialMeasure` is the Beta mixture of binomial laws;
* `TauCeti.Probability.betaBinomialMeasure_real_singleton` gives its mass function;
* `TauCeti.Probability.betaBinomialMeasure_eq_sum_dirac` gives its finite Dirac-sum form;
* `TauCeti.Probability.betaBinomialMeasure_singleton_ne_zero_iff` identifies its support;
* `TauCeti.Probability.measurable_betaBinomialMeasure` gives joint parameter measurability.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace TauCeti.Probability

private theorem measurable_binomialExtension (n : ℕ) :
    Measurable fun p : ℝ => binomial n (Set.projIcc 0 1 zero_le_one p) := by
  fun_prop

/-- The beta-binomial law with trial count `n` and positive Beta shapes `a` and `b`.

It is the mixture of `Binomial(n, p)` against `Beta(a, b)`. Invalid shape parameters give the zero
measure. -/
def betaBinomialMeasure (n : ℕ) (a b : ℝ) : Measure ℕ :=
  if 0 < a ∧ 0 < b then
    (betaMeasure a b).bind fun p => binomial n (Set.projIcc 0 1 zero_le_one p)
  else 0

/-- The defining mixture formula for a beta-binomial law at positive shape parameters. -/
theorem betaBinomialMeasure_eq_bind {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    betaBinomialMeasure n a b =
      (betaMeasure a b).bind fun p => binomial n (Set.projIcc 0 1 zero_le_one p) := by
  simp [betaBinomialMeasure, ha, hb]

/-- A beta-binomial law is zero outside the positive shape-parameter range. -/
@[simp]
theorem betaBinomialMeasure_eq_zero_of_invalid {a b : ℝ} (h : ¬ (0 < a ∧ 0 < b)) (n : ℕ) :
    betaBinomialMeasure n a b = 0 := by
  simp [betaBinomialMeasure, h]

/-- A beta-binomial law with positive shapes is a probability measure. -/
theorem isProbabilityMeasure_betaBinomialMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    IsProbabilityMeasure (betaBinomialMeasure n a b) := by
  rw [betaBinomialMeasure_eq_bind ha hb]
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_binomialExtension n).aemeasurable]
  simp

/-- The real mass of a beta-binomial law is the binomial coefficient times a quotient of Beta
functions. -/
@[simp]
theorem betaBinomialMeasure_real_singleton {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n k : ℕ) :
    (betaBinomialMeasure n a b).real {k} =
      n.choose k * beta (a + k) (b + (n - k)) / beta a b := by
  rw [betaBinomialMeasure_eq_bind ha hb, measureReal_def,
    Measure.bind_apply (measurableSet_singleton k) (measurable_binomialExtension n).aemeasurable]
  have hmass : AEMeasurable
      (fun p : ℝ => binomial n (Set.projIcc 0 1 zero_le_one p) {k})
      (betaMeasure a b) :=
    ((Measure.measurable_coe (measurableSet_singleton k)).comp
      (measurable_binomialExtension n)).aemeasurable
  rw [← integral_toReal hmass (ae_of_all _ fun p =>
    (lt_top_iff_ne_top.mpr <| measure_ne_top
      (binomial n (Set.projIcc 0 1 zero_le_one p)) {k}))]
  simp_rw [← measureReal_def, binomial_real_singleton]
  by_cases hkn : k ≤ n
  · have hproj :
        (fun p : ℝ =>
          (n.choose k : ℝ) * (Set.projIcc 0 1 zero_le_one p : ℝ) ^ k *
            (1 - Set.projIcc 0 1 zero_le_one p) ^ (n - k)) =ᵐ[betaMeasure a b]
          fun p => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
      simp only [Set.projIcc_of_mem zero_le_one ⟨hp.1.le, hp.2.le⟩]
    rw [integral_congr_ae hproj]
    have hak : 0 < a + (k : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
    have hbnk : 0 < b + ((n - k : ℕ) : ℝ) :=
      add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg (n - k))
    calc
      ∫ p : ℝ, ↑(n.choose k) * p ^ k * (1 - p) ^ (n - k) ∂betaMeasure a b =
          (n.choose k : ℝ) *
            (beta (a + k) (b + (n - k)) / beta a b) := by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        congr 1
        calc
          ∫ p : ℝ, p ^ k * (1 - p) ^ (n - k) ∂betaMeasure a b =
              beta (a + k) (b + ((n - k : ℕ) : ℝ)) / beta a b := by
            simpa only [Real.rpow_natCast] using
              integral_rpow_mul_one_sub_rpow_betaMeasure ha hb hak hbnk
          _ = beta (a + k) (b + ((n : ℝ) - k)) / beta a b := by
            rw [Nat.cast_sub hkn]
      _ = (n.choose k : ℝ) * beta (a + k) (b + (n - k)) / beta a b := by ring
  · have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)
    simp [hchoose]

/-- The `ENNReal` mass of a beta-binomial law. -/
@[simp]
theorem betaBinomialMeasure_singleton {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n k : ℕ) :
    betaBinomialMeasure n a b {k} =
      ENNReal.ofReal (n.choose k * beta (a + k) (b + (n - k)) / beta a b) := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  rw [← ofReal_measureReal (s := {k}), betaBinomialMeasure_real_singleton ha hb]

/-- A beta-binomial law is the finite weighted sum of its classical masses. -/
theorem betaBinomialMeasure_eq_sum_dirac {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    betaBinomialMeasure n a b =
      ∑ k ∈ Finset.Iic n,
        ENNReal.ofReal (n.choose k * beta (a + k) (b + (n - k)) / beta a b) •
          Measure.dirac k := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  apply Measure.ext_of_singleton
  intro k
  rw [betaBinomialMeasure_singleton ha hb, Measure.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · simp_all
    · simp_all
  · have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    rw [hchoose]
    simp only [Nat.cast_zero, zero_mul, zero_div, ENNReal.ofReal_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≠ k := by
      intro hik
      apply hk
      simpa [hik] using hi
    simp [hik]

/-- A natural number has positive beta-binomial mass exactly when it does not exceed the trial
count. -/
theorem betaBinomialMeasure_singleton_ne_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n k : ℕ) : betaBinomialMeasure n a b {k} ≠ 0 ↔ k ≤ n := by
  rw [betaBinomialMeasure_singleton ha hb]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro hpos
    by_contra hkn
    have hzero :
        (n.choose k : ℝ) * beta (a + k) (b + (n - k)) / beta a b = 0 := by
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)]
    linarith
  · intro hkn
    have hchoose : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn
    have hbetaNum : 0 < beta (a + (k : ℝ)) (b + ((n - k : ℕ) : ℝ)) :=
      beta_pos (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k))
        (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg (n - k)))
    simpa only [Nat.cast_sub hkn] using
      div_pos (mul_pos hchoose hbetaNum) (beta_pos ha hb)

/-- With zero trials, every valid beta-binomial law is concentrated at zero. -/
@[simp]
theorem betaBinomialMeasure_zero_trials {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaBinomialMeasure 0 a b = Measure.dirac 0 := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb 0
  apply Measure.ext_of_singleton
  intro k
  rw [betaBinomialMeasure_singleton ha hb]
  by_cases hk : k = 0
  · subst k
    simp [(beta_pos ha hb).ne']
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    simp [Measure.dirac_apply' _ (measurableSet_singleton k), hk,
      Nat.choose_eq_zero_of_lt hkpos]

/-- The beta-binomial family is jointly measurable in the trial count and both shape
parameters. -/
@[fun_prop]
theorem measurable_betaBinomialMeasure :
    Measurable fun q : ℕ × ℝ × ℝ => betaBinomialMeasure q.1 q.2.1 q.2.2 := by
  refine measurable_from_prod_countable_right fun n => ?_
  simp only [betaBinomialMeasure]
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact (Measure.measurable_bind' (measurable_binomialExtension n)).comp
      measurable_betaMeasure
  · exact measurable_const

end TauCeti.Probability
