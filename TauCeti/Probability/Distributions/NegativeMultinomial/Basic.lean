/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Distributions.Poisson.Measurability
import TauCeti.Probability.Distributions.Gamma.Poisson
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Analysis.SpecialFunctions.Gamma

/-!
# Negative-multinomial distributions

The negative-multinomial family extends counts of several types of failures before a fixed
number of successes to a real shape parameter. It mixes independent Poisson counts of rates
`p i * Λ` against a Gamma law with shape `r` and rate `p₀`. The weights satisfy
`p₀ + ∑ i, p i = 1`, with `p₀ > 0` and nonnegative category weights.

This file supplies the probability law, exact Gamma-quotient singleton masses, their weighted
Dirac sum, native support, and joint parameter measurability. Shape zero gives the point mass
at the zero count vector. Invalid parameters give the zero measure. Zero category weights are
allowed and force the corresponding counts to vanish.

The mass calculation follows the scalar Gamma–Poisson calculation in
`TauCeti.Probability.Distributions.Gamma.Poisson`: the Poisson product shifts the Gamma shape by
the total count, while the weights' normalization makes the combined rate one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley (1997).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The real negative-multinomial mass. At shape zero it is the mass of the zero vector. -/
def negativeMultinomialWeightReal (r p₀ : ℝ) (p : ι → ℝ≥0) (k : ι → ℕ) : ℝ :=
  if r = 0 then if k = 0 then 1 else 0
  else Real.Gamma (r + ∑ i, (k i : ℝ)) / (Real.Gamma r * ∏ i, ((k i).factorial : ℝ)) *
    p₀ ^ r * ∏ i, (p i : ℝ) ^ k i

/-- The extended nonnegative negative-multinomial mass. -/
def negativeMultinomialWeight (r p₀ : ℝ) (p : ι → ℝ≥0) (k : ι → ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (negativeMultinomialWeightReal r p₀ p k)

/-- The extended mass is the nonnegative-real lift of the real mass. -/
theorem negativeMultinomialWeight_eq_ofReal (r p₀ : ℝ) (p : ι → ℝ≥0) (k : ι → ℕ) :
    negativeMultinomialWeight r p₀ p k = ENNReal.ofReal (negativeMultinomialWeightReal r p₀ p k) :=
  (rfl)

/-- At nonzero shape the mass has its Gamma-quotient form. -/
@[simp]
theorem negativeMultinomialWeightReal_of_ne_zero {r : ℝ} (hr : r ≠ 0)
    (p₀ : ℝ) (p : ι → ℝ≥0) (k : ι → ℕ) :
    negativeMultinomialWeightReal r p₀ p k =
      Real.Gamma (r + ∑ i, (k i : ℝ)) / (Real.Gamma r * ∏ i, ((k i).factorial : ℝ)) *
        p₀ ^ r * ∏ i, (p i : ℝ) ^ k i := by
  simp [negativeMultinomialWeightReal, hr]

/-- At shape zero the mass is one at the zero vector and zero elsewhere. -/
@[simp]
theorem negativeMultinomialWeightReal_zero (p₀ : ℝ) (p : ι → ℝ≥0) (k : ι → ℕ) :
    negativeMultinomialWeightReal 0 p₀ p k = if k = 0 then 1 else 0 := by
  simp [negativeMultinomialWeightReal]

/-- Negative-multinomial masses are nonnegative for nonnegative shape and success
weight. No normalization of the weights is needed for this pointwise fact. -/
theorem negativeMultinomialWeightReal_nonneg {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 ≤ p₀)
    (p : ι → ℝ≥0) (k : ι → ℕ) : 0 ≤ negativeMultinomialWeightReal r p₀ p k := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [negativeMultinomialWeightReal_zero]
    split_ifs <;> norm_num
  · rw [negativeMultinomialWeightReal_of_ne_zero hr.ne']
    exact mul_nonneg (mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
      (by positivity)) (Real.rpow_nonneg hp₀ _)) (Finset.prod_nonneg fun _ _ => by positivity)

/-- The real and extended nonnegative masses agree. -/
@[simp]
theorem negativeMultinomialWeight_toReal {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 ≤ p₀)
    (p : ι → ℝ≥0) (k : ι → ℕ) :
    (negativeMultinomialWeight r p₀ p k).toReal = negativeMultinomialWeightReal r p₀ p k :=
  ENNReal.toReal_ofReal (negativeMultinomialWeightReal_nonneg hr hp₀ p k)

/-- The negative-multinomial law, constructed as a Gamma mixture of independent Poisson counts.
Shape zero is Dirac at zero; negative shape or invalid weights give the zero measure. -/
def negativeMultinomialMeasure (r p₀ : ℝ) (p : ι → ℝ≥0) : Measure (ι → ℕ) :=
  if 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1 then
    if r = 0 then Measure.dirac 0
    else if 0 < r then
      (gammaMeasure r p₀).bind
        (fun lam => Measure.pi (fun i => poissonMeasure (p i * Real.toNNReal lam)))
    else 0
  else 0

/-- The positive-shape law is its defining Gamma–Poisson mixture. -/
theorem negativeMultinomialMeasure_of_pos {r p₀ : ℝ} (hr : 0 < r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    negativeMultinomialMeasure r p₀ p = (gammaMeasure r p₀).bind
      (fun lam => Measure.pi (fun i => poissonMeasure (p i * Real.toNNReal lam))) := by
  simp [negativeMultinomialMeasure, hr, hr.ne', hp₀, hp]

/-- Shape zero gives the point mass at the zero count vector for valid weights. -/
@[simp]
theorem negativeMultinomialMeasure_zero {p₀ : ℝ} (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    negativeMultinomialMeasure 0 p₀ p = Measure.dirac 0 := by
  simp [negativeMultinomialMeasure, hp₀, hp]

/-- Outside the probability parameter range the law is zero. -/
@[simp]
theorem negativeMultinomialMeasure_eq_zero_of_invalid {r p₀ : ℝ} {p : ι → ℝ≥0}
    (h : ¬ (0 ≤ r ∧ 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1)) :
    negativeMultinomialMeasure r p₀ p = 0 := by
  unfold negativeMultinomialMeasure
  split_ifs with hp hr hrpos
  · exact (h ⟨hr.ge, hp⟩).elim
  · exact (h ⟨hrpos.le, hp⟩).elim
  · rfl
  · rfl

/-- The negative-multinomial law is a probability measure for valid weights and nonnegative
shape, including zero category weights and shape zero. -/
theorem isProbabilityMeasure_negativeMultinomialMeasure {r p₀ : ℝ} (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    IsProbabilityMeasure (negativeMultinomialMeasure r p₀ p) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_zero hp₀ hp]
    infer_instance
  · rw [negativeMultinomialMeasure_of_pos hr hp₀ hp]
    have := isProbabilityMeasure_gammaMeasure hr hp₀
    exact isProbabilityMeasure_bind
      (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable
      (ae_of_all _ fun _ => inferInstance)

private lemma integral_prod_poissonMass_gammaMeasure {r p₀ : ℝ} (hr : 0 < r)
    (hp₀ : 0 < p₀) {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (k : ι → ℕ) :
    ∫ x, ∏ i, (Real.exp (-((p i : ℝ) * x)) * ((p i : ℝ) * x) ^ k i /
      (k i).factorial) ∂gammaMeasure r p₀ = negativeMultinomialWeightReal r p₀ p k := by
  classical
  have hshape : 0 < r + ∑ i, (k i : ℝ) := by positivity
  -- Transfer to the Gamma density on its positive support.
  rw [integral_gammaMeasure_eq_integral_Ioi hr hp₀]
  simp only [smul_eq_mul]
  -- Collect the Poisson factors; normalization of the weights makes the combined rate one.
  have hcollect := fun x (hx : x ∈ Ioi (0 : ℝ)) =>
    Real.gammaKernel_mul_prod_exp_mul_pow_div_factorial p₀ r (fun i => (p i : ℝ)) k hx.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi hcollect, integral_const_mul,
    hp]
  -- Euler's Gamma integral evaluates the shifted shape, leaving the mass constants.
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hshape zero_lt_one,
    negativeMultinomialWeightReal_of_ne_zero hr.ne']
  simp only [one_div_one, Real.one_rpow]
  ring

/-- The native singleton masses of the negative-multinomial law, including shape zero. -/
@[simp]
theorem negativeMultinomialMeasure_singleton {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (k : ι → ℕ) :
    negativeMultinomialMeasure r p₀ p {k} = negativeMultinomialWeight r p₀ p k := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_zero hp₀ hp]
    by_cases hk : k = 0
    · subst k
      simp [negativeMultinomialWeight]
    · simp [negativeMultinomialWeight, hk, eq_comm]
  have hkernel : Measurable fun x : ℝ =>
      Measure.pi (fun i => poissonMeasure (p i * Real.toNNReal x)) :=
    measurable_pi_poissonMeasure_mul_toNNReal p
  have := isProbabilityMeasure_gammaMeasure hr hp₀
  have := isProbabilityMeasure_negativeMultinomialMeasure hr.le hp₀ hp
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (by simp [negativeMultinomialWeight])).mp
  rw [negativeMultinomialWeight_toReal hr.le hp₀.le,
    negativeMultinomialMeasure_of_pos hr hp₀ hp,
    Measure.bind_apply (measurableSet_singleton k) hkernel.aemeasurable]
  have hmass : AEMeasurable
      (fun x : ℝ => (Measure.pi (fun i => poissonMeasure (p i * Real.toNNReal x))) {k})
      (gammaMeasure r p₀) :=
    ((Measure.measurable_coe (measurableSet_singleton k)).comp hkernel).aemeasurable
  rw [← integral_toReal hmass (ae_of_all _ fun _ => measure_lt_top _ _)]
  simp only [Measure.pi_singleton, ENNReal.toReal_prod, ← measureReal_def,
    poissonMeasure_real_singleton, NNReal.coe_mul]
  trans ∫ x, ∏ i, (Real.exp (-((p i : ℝ) * x)) * ((p i : ℝ) * x) ^ k i /
    (k i).factorial) ∂gammaMeasure r p₀
  · apply integral_congr_ae
    filter_upwards [ae_pos_gammaMeasure r p₀] with x hx
    simp only [Real.coe_toNNReal x hx.le]
  · exact integral_prod_poissonMass_gammaMeasure hr hp₀ hp k

/-- The real singleton masses are the stated Gamma-quotient weights. -/
theorem negativeMultinomialMeasure_real_singleton {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (k : ι → ℕ) :
    (negativeMultinomialMeasure r p₀ p).real {k} = negativeMultinomialWeightReal r p₀ p k := by
  rw [measureReal_def, negativeMultinomialMeasure_singleton hr hp₀ hp,
    negativeMultinomialWeight_toReal hr hp₀.le]

/-- The negative-multinomial law is the countable weighted sum of its Dirac masses. -/
theorem negativeMultinomialMeasure_eq_sum_dirac {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    negativeMultinomialMeasure r p₀ p =
      Measure.sum (fun k => negativeMultinomialWeight r p₀ p k • Measure.dirac k) := by
  rw [← Measure.sum_smul_dirac (negativeMultinomialMeasure r p₀ p)]
  simp only [negativeMultinomialMeasure_singleton hr hp₀ hp]

/-- At positive shape, a singleton has nonzero mass exactly when every zero-weight category
has count zero. At shape zero, only the zero count vector has nonzero mass. -/
theorem negativeMultinomialMeasure_singleton_ne_zero_iff {r p₀ : ℝ} (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (k : ι → ℕ) :
    negativeMultinomialMeasure r p₀ p {k} ≠ 0 ↔
      (r = 0 ∧ k = 0) ∨ (0 < r ∧ ∀ i, p i = 0 → k i = 0) := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_singleton (le_refl 0) hp₀ hp]
    by_cases hk : k = 0 <;> simp [negativeMultinomialWeight, hk]
  rw [negativeMultinomialMeasure_singleton hr.le hp₀ hp, negativeMultinomialWeight,
    ENNReal.ofReal_ne_zero_iff]
  have hnonneg := negativeMultinomialWeightReal_nonneg hr.le hp₀.le p k
  rw [lt_iff_le_and_ne, and_iff_right hnonneg,
    negativeMultinomialWeightReal_of_ne_zero hr.ne']
  have hGamma : Real.Gamma (r + ∑ i, (k i : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hGamma₀ : Real.Gamma r ≠ 0 := (Real.Gamma_pos_of_pos hr).ne'
  have hfac : (∏ i, ((k i).factorial : ℝ)) ≠ 0 := by positivity
  have hpow : p₀ ^ r ≠ 0 := (Real.rpow_pos_of_pos hp₀ r).ne'
  rw [ne_comm]
  simp [hGamma, hGamma₀, hfac, hpow, hr.ne', hr, Finset.prod_ne_zero_iff]

/-- At success weight one, all category weights vanish and the law is Dirac at zero. -/
@[simp]
theorem negativeMultinomialMeasure_eq_dirac_of_successWeight_eq_one {r : ℝ} (hr : 0 ≤ r) :
    negativeMultinomialMeasure r 1 (0 : ι → ℝ≥0) = Measure.dirac 0 := by
  classical
  apply Measure.ext_of_singleton
  intro k
  by_cases hk : k = 0
  · subst k
    rcases hr.eq_or_lt with rfl | hr
    · simp
    · rw [negativeMultinomialMeasure_singleton hr.le zero_lt_one (by simp)]
      simp [negativeMultinomialWeight, hr.ne', (Real.Gamma_pos_of_pos hr).ne']
  · have hzero : negativeMultinomialMeasure r 1 (0 : ι → ℝ≥0) {k} = 0 := by
      by_contra h
      have hsupport := (negativeMultinomialMeasure_singleton_ne_zero_iff hr zero_lt_one
        (p := (0 : ι → ℝ≥0)) (by simp) k).mp h
      rcases hsupport with ⟨_, h⟩ | ⟨_, h⟩
      · exact hk h
      · exact hk (funext fun i => h i rfl)
    simp [hzero, hk, eq_comm]

/-- The full totalized family is measurable jointly in shape, success weight, and category
weights, with the Giry measurable structure on measures. -/
@[fun_prop]
theorem measurable_negativeMultinomialMeasure :
    Measurable fun q : (ℝ × ℝ) × (ι → ℝ≥0) =>
      negativeMultinomialMeasure q.1.1 q.1.2 q.2 := by
  classical
  have hw : Measurable fun q : (ℝ × ℝ) × (ι → ℝ≥0) =>
      Measure.sum (fun k => negativeMultinomialWeight q.1.1 q.1.2 q.2 k • Measure.dirac k) := by
    apply TauCeti.MeasureTheory.measurable_sum_smul_dirac
    intro k
    unfold negativeMultinomialWeight negativeMultinomialWeightReal
    apply Measurable.ennreal_ofReal
    apply Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_const)
    · exact measurable_const
    · fun_prop
  have hv : MeasurableSet {q : (ℝ × ℝ) × (ι → ℝ≥0) |
      0 ≤ q.1.1 ∧ 0 < q.1.2 ∧ q.1.2 + ∑ i, (q.2 i : ℝ) = 1} := by
    have hsum : Measurable fun q : (ℝ × ℝ) × (ι → ℝ≥0) =>
        q.1.2 + ∑ i, (q.2 i : ℝ) := by fun_prop
    exact (measurableSet_le measurable_const measurable_fst.fst).inter
      ((measurableSet_lt measurable_const measurable_fst.snd).inter
        (measurableSet_eq_fun hsum measurable_const))
  have hm : Measurable fun q : (ℝ × ℝ) × (ι → ℝ≥0) =>
      if 0 ≤ q.1.1 ∧ 0 < q.1.2 ∧ q.1.2 + ∑ i, (q.2 i : ℝ) = 1 then
        Measure.sum (fun k => negativeMultinomialWeight q.1.1 q.1.2 q.2 k • Measure.dirac k)
      else 0 := hw.ite hv measurable_const
  convert hm using 1
  funext q
  split_ifs with h
  · exact negativeMultinomialMeasure_eq_sum_dirac h.1 h.2.1 h.2.2
  · exact negativeMultinomialMeasure_eq_zero_of_invalid h

end TauCeti.Probability
