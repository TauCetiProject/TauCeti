/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
import TauCeti.Probability.Distributions.Poisson.Transforms
import TauCeti.MeasureTheory.Integral.Bind

/-!
# Directional real transforms of negative-multinomial laws

For a negative-multinomial count vector with shape `r`, success weight `p₀` and category weights
`p`, the observable `∑ i, θ i * k i` has exponential-integrability domain
`{t | ∑ i, p i * exp (t * θ i) < 1}` at positive shape. Its moment generating function there is
`(p₀ / (1 - ∑ i, p i * exp (t * θ i))) ^ r`. Shape zero has full domain and constant transform
one, including at parameters on or outside the positive-shape domain.

The exact domain follows by integrating the nonnegative component exponentials in the defining
Gamma–Poisson mixture. The component Poisson transform reduces the outer integrability question
to the sharp Gamma exponential-integrability criterion. The results permit zero category
weights and empty coordinate types, and keep the observable on the native count carrier.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem negativeMultinomial_exponential_rate_eq {p₀ : ℝ} {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (θ : ι → ℝ) (t : ℝ) :
    (∑ i, (p i : ℝ) * (Real.exp (t * θ i) - 1)) =
      (∑ i, (p i : ℝ) * Real.exp (t * θ i)) - (1 - p₀) := by
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith

private theorem poisson_exponential_integral_eq_ae (r p₀ : ℝ) (p : ι → ℝ≥0)
    (θ : ι → ℝ) (t : ℝ) :
    (fun x : ℝ => ∫ k : ι → ℕ, Real.exp (t * ∑ i, θ i * (k i : ℝ))
      ∂(Measure.pi fun i => poissonMeasure (p i * Real.toNNReal x))) =ᵐ[gammaMeasure r p₀]
    (fun x => Real.exp ((∑ i, (p i : ℝ) * (Real.exp (t * θ i) - 1)) * x)) := by
  filter_upwards [ae_pos_gammaMeasure r p₀] with x hx
  have h := mgf_sum_mul_natCast_pi_poissonMeasure (fun i => p i * Real.toNNReal x) θ t
  simp only [mgf] at h
  rw [h]
  simp only [NNReal.coe_mul, Real.coe_toNNReal x hx.le]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A directional exponential is integrable exactly on the stated strict domain at positive
shape; at shape zero every parameter is allowed. The equivalence includes divergence at the
boundary of the positive-shape domain. -/
@[simp]
theorem integrable_exp_sum_mul_natCast_negativeMultinomialMeasure_iff {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (θ : ι → ℝ) (t : ℝ) :
    Integrable (fun k : ι → ℕ => Real.exp (t * ∑ i, θ i * (k i : ℝ)))
      (negativeMultinomialMeasure r p₀ p) ↔
        r = 0 ∨ ∑ i, (p i : ℝ) * Real.exp (t * θ i) < 1 := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · simp only [negativeMultinomialMeasure_zero hp₀ hp, true_or, iff_true]
    exact integrable_dirac' (.of_discrete) (by simp)
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp,
    Measure.integrable_bind_iff (measurable_pi_poissonMeasure_mul_toNNReal p)
      (.of_discrete)]
  have hcomponent : ∀ x : ℝ, Integrable
      (fun k : ι → ℕ => Real.exp (t * ∑ i, θ i * (k i : ℝ)))
      (Measure.pi fun i => poissonMeasure (p i * Real.toNNReal x)) :=
    fun x => integrable_exp_sum_mul_natCast_pi_poissonMeasure _ θ t
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le, ae_of_all _ hcomponent,
    true_and, hr.ne', false_or]
  rw [integrable_congr (poisson_exponential_integral_eq_ae r p₀ p θ t)]
  have hgamma := Set.ext_iff.mp (integrableExpSet_id_gammaMeasure hr hp₀)
    (∑ i, (p i : ℝ) * (Real.exp (t * θ i) - 1))
  -- Express exponential-domain membership as integrability of the exponential itself.
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_Iio, id_eq] at hgamma
  rw [hgamma, negativeMultinomial_exponential_rate_eq hp θ t]
  constructor <;> intro ht <;> linarith

/-- The exact directional exponential-integrability domain, with the full shape-zero domain. -/
@[simp]
theorem integrableExpSet_sum_mul_natCast_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (θ : ι → ℝ) :
    integrableExpSet (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (negativeMultinomialMeasure r p₀ p) =
        {t | r = 0 ∨ ∑ i, (p i : ℝ) * Real.exp (t * θ i) < 1} := by
  ext t
  exact integrable_exp_sum_mul_natCast_negativeMultinomialMeasure_iff hr hp₀ hp θ t

/-- The directional moment generating function on its exact domain. At shape zero the formula
is one even when the displayed denominator vanishes. -/
@[simp]
theorem mgf_sum_mul_natCast_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (θ : ι → ℝ) {t : ℝ}
    (ht : r = 0 ∨ ∑ i, (p i : ℝ) * Real.exp (t * θ i) < 1) :
    mgf (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (negativeMultinomialMeasure r p₀ p) t =
        (p₀ / (1 - ∑ i, (p i : ℝ) * Real.exp (t * θ i))) ^ r := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · simp [negativeMultinomialMeasure_zero hp₀ hp, mgf]
  have ht' := ht.resolve_left hr.ne'
  have hint := (integrable_exp_sum_mul_natCast_negativeMultinomialMeasure_iff
    hr.le hp₀ hp θ t).mpr ht
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp] at hint ⊢
  rw [mgf, Measure.integral_bind
    (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable hint,
    integral_congr_ae (poisson_exponential_integral_eq_ae r p₀ p θ t)]
  have hrate : (∑ i, (p i : ℝ) * (Real.exp (t * θ i) - 1)) < p₀ := by
    rw [negativeMultinomial_exponential_rate_eq hp θ t]
    linarith
  have hmgf := mgf_id_gammaMeasure hr hp₀ hrate
  simp only [mgf, id_eq] at hmgf
  rw [hmgf]
  have hbase : 1 - (∑ i, (p i : ℝ) * (Real.exp (t * θ i) - 1)) / p₀ =
      (1 - ∑ i, (p i : ℝ) * Real.exp (t * θ i)) / p₀ := by
    rw [negativeMultinomial_exponential_rate_eq hp θ t]
    field_simp
    ring
  rw [hbase, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  simp only [inv_div]

/-- The simplified directional cumulant generating function on the exact domain. -/
@[simp]
theorem cgf_sum_mul_natCast_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (θ : ι → ℝ) {t : ℝ}
    (ht : r = 0 ∨ ∑ i, (p i : ℝ) * Real.exp (t * θ i) < 1) :
    cgf (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (negativeMultinomialMeasure r p₀ p) t =
        r * Real.log (p₀ / (1 - ∑ i, (p i : ℝ) * Real.exp (t * θ i))) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [cgf, mgf_sum_mul_natCast_negativeMultinomialMeasure (le_refl 0) hp₀ hp θ ht]
  rw [cgf, mgf_sum_mul_natCast_negativeMultinomialMeasure hr.le hp₀ hp θ ht,
    Real.log_rpow (div_pos hp₀ (sub_pos.mpr (ht.resolve_left hr.ne')))]

end TauCeti.Probability
