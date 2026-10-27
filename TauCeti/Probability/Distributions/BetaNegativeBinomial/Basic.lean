/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.NegativeBinomial.Measurability
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.Probability.Distributions.Beta.Measurability
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The beta-negative-binomial distribution

The beta-negative-binomial law mixes the success probability of a negative-binomial law against
a Beta distribution.  Its parameters are a nonnegative negative-binomial shape `r` and positive
Beta shapes `a` and `b`.  At `r = 0` it is the Dirac law at zero; invalid parameters give the zero
measure.

This file establishes the measure-level foundation of the family: the defining mixture,
normalization, singleton masses, native support, and joint parameter measurability.  These results
make later moment, transform, cumulative-distribution, and quantile calculations possible without
unfolding the mixture.

## Main results

* `TauCeti.Probability.betaNegativeBinomialMeasure` is the Beta mixture of negative-binomial laws;
* `TauCeti.Probability.betaNegativeBinomialMeasure_real_singleton` gives its classical mass;
* `TauCeti.Probability.betaNegativeBinomialMeasure_eq_sum_dirac` is its weighted Dirac-sum form;
* `TauCeti.Probability.betaNegativeBinomialMeasure_singleton_ne_zero_iff` identifies its support;
* `TauCeti.Probability.measurable_betaNegativeBinomialMeasure` gives joint parameter measurability.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The real beta-negative-binomial mass at `k`.

At shape zero this is the mass of `dirac 0`; at positive shape it is the classical quotient of
Gamma and Beta functions. -/
def betaNegativeBinomialWeightReal (r a b : ℝ) (k : ℕ) : ℝ :=
  if r = 0 then if k = 0 then 1 else 0
  else Real.Gamma (r + k) / (Real.Gamma r * k.factorial) * beta (a + r) (b + k) / beta a b

/-- The `ℝ≥0∞`-valued beta-negative-binomial mass at `k`. -/
def betaNegativeBinomialWeight (r a b : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaNegativeBinomialWeightReal r a b k)

/-- The `ℝ≥0∞`-valued mass is the extended-real image of the real mass. -/
theorem betaNegativeBinomialWeight_def (r a b : ℝ) (k : ℕ) :
    betaNegativeBinomialWeight r a b k = ENNReal.ofReal (betaNegativeBinomialWeightReal r a b k) :=
  (rfl)

/-- Every beta-negative-binomial mass is finite. -/
@[simp]
theorem betaNegativeBinomialWeight_ne_top (r a b : ℝ) (k : ℕ) :
    betaNegativeBinomialWeight r a b k ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- At shape zero the real mass is one at zero and vanishes elsewhere. -/
@[simp]
theorem betaNegativeBinomialWeightReal_zero (a b : ℝ) (k : ℕ) :
    betaNegativeBinomialWeightReal 0 a b k = if k = 0 then 1 else 0 := by
  simp [betaNegativeBinomialWeightReal]

/-- At nonzero shape the real mass is the classical Gamma--Beta expression. -/
@[simp]
theorem betaNegativeBinomialWeightReal_of_ne_zero {r : ℝ} (hr : r ≠ 0) (a b : ℝ) (k : ℕ) :
    betaNegativeBinomialWeightReal r a b k =
      Real.Gamma (r + k) / (Real.Gamma r * k.factorial) * beta (a + r) (b + k) /
        beta a b := by
  rw [betaNegativeBinomialWeightReal, ite_eq_right hr]

/-- The beta-negative-binomial law with negative-binomial shape `r` and Beta shapes `a`, `b`.

For `0 ≤ r`, `0 < a`, and `0 < b`, this mixes `negativeBinomialMeasure r p` against
`betaMeasure a b`.  Every other parameter value gives the zero measure. -/
def betaNegativeBinomialMeasure (r a b : ℝ) : Measure ℕ :=
  if 0 ≤ r ∧ 0 < a ∧ 0 < b then
    (betaMeasure a b).bind fun p => negativeBinomialMeasure r p
  else 0

/-- The defining mixture formula on the valid parameter range. -/
theorem betaNegativeBinomialMeasure_eq_bind {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) :
    betaNegativeBinomialMeasure r a b =
      (betaMeasure a b).bind fun p => negativeBinomialMeasure r p := by
  simp [betaNegativeBinomialMeasure, hr, ha, hb]

/-- Invalid beta-negative-binomial parameters give the zero measure. -/
@[simp]
theorem betaNegativeBinomialMeasure_eq_zero_of_invalid {r a b : ℝ}
    (h : ¬ (0 ≤ r ∧ 0 < a ∧ 0 < b)) : betaNegativeBinomialMeasure r a b = 0 := by
  simp [betaNegativeBinomialMeasure, h]

/-- A beta-negative-binomial law with valid parameters is a probability measure. -/
theorem isProbabilityMeasure_betaNegativeBinomialMeasure {r a b : ℝ} (hr : 0 ≤ r)
    (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaNegativeBinomialMeasure r a b) := by
  rw [betaNegativeBinomialMeasure_eq_bind hr ha hb]
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  refine isProbabilityMeasure_bind
    (by fun_prop : Measurable fun p : ℝ => negativeBinomialMeasure r p).aemeasurable ?_
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
  exact isProbabilityMeasure_negativeBinomialMeasure hr hp.1 hp.2.le

/-- At negative-binomial shape zero, every valid beta-negative-binomial law is concentrated at
zero. -/
@[simp]
theorem betaNegativeBinomialMeasure_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaNegativeBinomialMeasure 0 a b = Measure.dirac 0 := by
  rw [betaNegativeBinomialMeasure_eq_bind le_rfl ha hb,
    Measure.bind_congr_right ((ae_mem_Ioo_betaMeasure a b).mono fun p hp =>
      negativeBinomialMeasure_zero hp.1 hp.2.le), Measure.bind_const]
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  simp

/-- At positive shape the real mass is positive at every natural number. -/
theorem betaNegativeBinomialWeightReal_pos_of_pos {r a b : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) : 0 < betaNegativeBinomialWeightReal r a b k := by
  rw [betaNegativeBinomialWeightReal_of_ne_zero hr.ne']
  exact div_pos
    (mul_pos
      (div_pos (Real.Gamma_pos_of_pos (by positivity))
        (mul_pos (Real.Gamma_pos_of_pos hr) (by positivity)))
      (beta_pos (add_pos ha hr) (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg k))))
    (beta_pos ha hb)

/-- The real mass is nonnegative throughout the valid parameter range. -/
theorem betaNegativeBinomialWeightReal_nonneg {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) : 0 ≤ betaNegativeBinomialWeightReal r a b k := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialWeightReal_zero]
    split_ifs <;> norm_num
  exact (betaNegativeBinomialWeightReal_pos_of_pos hr ha hb k).le

/-- The real-valued and extended beta-negative-binomial masses agree. -/
@[simp]
theorem betaNegativeBinomialWeight_toReal {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) :
    (betaNegativeBinomialWeight r a b k).toReal = betaNegativeBinomialWeightReal r a b k := by
  rw [betaNegativeBinomialWeight_def, ENNReal.toReal_ofReal]
  exact betaNegativeBinomialWeightReal_nonneg hr ha hb k

/-- The real singleton mass of a beta-negative-binomial law. -/
@[simp]
theorem betaNegativeBinomialMeasure_real_singleton {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) :
    (betaNegativeBinomialMeasure r a b).real {k} =
      betaNegativeBinomialWeightReal r a b k := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb]
    by_cases hk : k = 0
    · subst k
      simp [betaNegativeBinomialWeightReal]
    · simp [betaNegativeBinomialWeightReal, hk]
  rw [betaNegativeBinomialMeasure_eq_bind hr.le ha hb, measureReal_def,
    Measure.bind_apply (measurableSet_singleton k)
      (by fun_prop : Measurable fun p : ℝ => negativeBinomialMeasure r p).aemeasurable]
  have hmass : AEMeasurable (fun p : ℝ => negativeBinomialMeasure r p {k})
      (betaMeasure a b) :=
    ((Measure.measurable_coe (measurableSet_singleton k)).comp
      (by fun_prop : Measurable fun p : ℝ => negativeBinomialMeasure r p)).aemeasurable
  rw [← integral_toReal hmass]
  · simp_rw [← measureReal_def]
    have hpointwise : (fun p : ℝ => (negativeBinomialMeasure r p).real {k}) =ᵐ[betaMeasure a b]
        fun p => Real.Gamma (r + k) / (Real.Gamma r * k.factorial) * p ^ r * (1 - p) ^ k := by
      filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
      rw [negativeBinomialMeasure_real_singleton hr.le hp.1 hp.2.le,
        negativeBinomialWeightReal_eq_gamma hr.ne' k, Real.rpow_eq_pow, add_comm (k : ℝ) r,
        mul_comm (k.factorial : ℝ)]
    rw [integral_congr_ae hpointwise, betaNegativeBinomialWeightReal_of_ne_zero hr.ne']
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have har : 0 < a + r := add_pos ha hr
    have hbk : 0 < b + (k : ℝ) := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg k)
    have hint : ∫ p : ℝ, p ^ r * (1 - p) ^ k ∂betaMeasure a b =
        beta (a + r) (b + k) / beta a b := by
      simpa only [Real.rpow_natCast] using
        integral_rpow_mul_one_sub_rpow_betaMeasure ha hb har hbk
    rw [hint]
    ring
  · filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
    let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp.1 hp.2.le
    exact measure_lt_top _ _

/-- The `ℝ≥0∞` singleton mass of a beta-negative-binomial law. -/
@[simp]
theorem betaNegativeBinomialMeasure_singleton {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) :
    betaNegativeBinomialMeasure r a b {k} = betaNegativeBinomialWeight r a b k := by
  let _ := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  rw [← ofReal_measureReal (s := {k}), betaNegativeBinomialMeasure_real_singleton hr ha hb,
    betaNegativeBinomialWeight_def]

/-- The real beta-negative-binomial masses sum to one throughout the valid parameter range. -/
theorem hasSum_betaNegativeBinomialWeightReal {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) : HasSum (betaNegativeBinomialWeightReal r a b) 1 := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  have hsum : ∑' k, betaNegativeBinomialWeight r a b k = 1 := by
    simpa only [Set.indicator_univ, betaNegativeBinomialMeasure_singleton hr ha hb,
      measure_univ] using
        (Measure.tsum_indicator_apply_singleton (betaNegativeBinomialMeasure r a b)
          univ MeasurableSet.univ)
  have hsumReal : ∑' k, (betaNegativeBinomialWeight r a b k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (betaNegativeBinomialWeight_ne_top r a b), hsum,
      ENNReal.toReal_one]
  have h := ENNReal.hasSum_toReal (f := betaNegativeBinomialWeight r a b)
    (by rw [hsum]; exact ENNReal.one_ne_top)
  rw [hsumReal] at h
  simpa only [betaNegativeBinomialWeight_toReal hr ha hb] using h

/-- A valid beta-negative-binomial law is the weighted Dirac sum of its singleton masses. -/
theorem betaNegativeBinomialMeasure_eq_sum_dirac {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) :
    betaNegativeBinomialMeasure r a b =
      Measure.sum fun k => betaNegativeBinomialWeight r a b k • Measure.dirac k := by
  rw [← Measure.sum_smul_dirac (betaNegativeBinomialMeasure r a b)]
  congr 1
  funext k
  congr 1
  exact betaNegativeBinomialMeasure_singleton hr ha hb k

/-- Every natural number has positive mass at positive shape; at shape zero only zero does. -/
@[simp]
theorem betaNegativeBinomialWeightReal_pos_iff {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) :
    0 < betaNegativeBinomialWeightReal r a b k ↔ k = 0 ∨ 0 < r := by
  rcases hr.eq_or_lt with rfl | hr
  · by_cases hk : k = 0 <;> simp [hk]
  · exact ⟨fun _ => Or.inr hr, fun _ => betaNegativeBinomialWeightReal_pos_of_pos hr ha hb k⟩

/-- The `ℝ≥0∞` mass is nonzero at every natural number at positive shape; at shape zero only at
zero. -/
@[simp]
theorem betaNegativeBinomialWeight_ne_zero_iff {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) :
    betaNegativeBinomialWeight r a b k ≠ 0 ↔ k = 0 ∨ 0 < r := by
  rw [betaNegativeBinomialWeight_def, ENNReal.ofReal_ne_zero_iff,
    betaNegativeBinomialWeightReal_pos_iff hr ha hb]

/-- The native support of a valid beta-negative-binomial law is `{0}` at shape zero and all of
`ℕ` at positive shape. -/
theorem betaNegativeBinomialMeasure_singleton_ne_zero_iff {r a b : ℝ} (hr : 0 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    betaNegativeBinomialMeasure r a b {k} ≠ 0 ↔ k = 0 ∨ 0 < r := by
  rw [betaNegativeBinomialMeasure_singleton hr ha hb,
    betaNegativeBinomialWeight_ne_zero_iff hr ha hb]

/-- The beta-negative-binomial family is jointly measurable in all three real parameters. -/
@[fun_prop]
theorem measurable_betaNegativeBinomialMeasure :
    Measurable fun q : ℝ × ℝ × ℝ => betaNegativeBinomialMeasure q.1 q.2.1 q.2.2 := by
  have hweight (k : ℕ) : Measurable fun q : ℝ × ℝ × ℝ =>
      betaNegativeBinomialWeight q.1 q.2.1 q.2.2 k := by
    apply Measurable.ennreal_ofReal
    unfold betaNegativeBinomialWeightReal
    apply Measurable.ite
    · exact measurableSet_eq_fun measurable_fst measurable_const
    · exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
        measurable_const measurable_const
    · fun_prop
  have hvalid : MeasurableSet {q : ℝ × ℝ × ℝ | 0 ≤ q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2} := by
    measurability
  have heq : (fun q : ℝ × ℝ × ℝ => betaNegativeBinomialMeasure q.1 q.2.1 q.2.2) =
      fun q => if 0 ≤ q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2 then
        Measure.sum fun k => betaNegativeBinomialWeight q.1 q.2.1 q.2.2 k • Measure.dirac k
      else 0 := by
    funext q
    split_ifs with h
    · exact betaNegativeBinomialMeasure_eq_sum_dirac h.1 h.2.1 h.2.2
    · exact betaNegativeBinomialMeasure_eq_zero_of_invalid h
  rw [heq]
  exact Measurable.ite hvalid (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight)
    measurable_const

end TauCeti.Probability
