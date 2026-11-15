/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
public import TauCeti.Probability.Distributions.Multinomial.Basic
import TauCeti.Probability.Distributions.Gamma.CharFun
import TauCeti.Probability.Distributions.Poisson.CharFun
import TauCeti.MeasureTheory.Integral.Bind

/-!
# Characteristic functions of negative-multinomial laws

The Euclidean cast of a negative-multinomial count vector has characteristic function
`(p₀ / (1 - ∑ i, p i * exp (I * t i))) ^ r`. The power is the principal complex power:
the denominator has real part at least `p₀ > 0`. The formula includes nonintegral shapes,
shape zero, zero category weights, and empty coordinate types.

The defining Gamma–Poisson mixture reduces the calculation to the independent-Poisson
characteristic function and `complexMGF_id_gammaMeasure` at a parameter with nonpositive real
part. No extra exponential-integrability hypothesis on the count vector is needed.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem poisson_characteristic_integral_eq_ae (r p₀ : ℝ) (p : ι → ℝ≥0)
    (t : EuclideanSpace ℝ ι) :
    (fun x : ℝ => ∫ k : ι → ℕ,
      Complex.exp ((inner ℝ (multinomialToEuclidean k) t : ℂ) * Complex.I)
      ∂(Measure.pi fun i => poissonMeasure (p i * Real.toNNReal x))) =ᵐ[gammaMeasure r p₀]
    (fun x => Complex.exp
      ((∑ i, (p i : ℂ) * (Complex.exp (Complex.I * (t i : ℂ)) - 1)) * x)) := by
  filter_upwards [ae_pos_gammaMeasure r p₀] with x hx
  have h := charFun_map_multinomialToEuclidean_pi_poissonMeasure
    (fun i => p i * Real.toNNReal x) t
  rw [charFun_apply, integral_map measurable_multinomialToEuclidean.aemeasurable
    (by fun_prop)] at h
  rw [h]
  simp only [NNReal.coe_mul, Real.coe_toNNReal x hx.le, Complex.ofReal_mul]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The joint characteristic function of a negative-multinomial count vector after real
casting. The denominator lies in the open right half-plane, fixing the principal-power branch.
At shape zero the transform is one. -/
@[simp]
theorem charFun_map_multinomialToEuclidean_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (t : EuclideanSpace ℝ ι) :
    charFun ((negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean) t =
      ((p₀ : ℂ) / (1 - ∑ i, (p i : ℂ) * Complex.exp (Complex.I * (t i : ℂ)))) ^
        (r : ℂ) := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · simp [negativeMultinomialMeasure_zero hp₀ hp, real_inner_comm,
      inner_multinomialToEuclidean]
  have := isProbabilityMeasure_negativeMultinomialMeasure hr.le hp₀ hp
  have hint : Integrable (fun k : ι → ℕ =>
      Complex.exp ((inner ℝ (multinomialToEuclidean k) t : ℂ) * Complex.I))
      (negativeMultinomialMeasure r p₀ p) :=
    (integrable_const (1 : ℂ)).mono (.of_discrete) (by simp)
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp] at hint ⊢
  rw [charFun_apply, integral_map measurable_multinomialToEuclidean.aemeasurable
    (by fun_prop), Measure.integral_bind
      (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable hint,
    integral_congr_ae (poisson_characteristic_integral_eq_ae r p₀ p t)]
  let z : ℂ := ∑ i, (p i : ℂ) * (Complex.exp (Complex.I * (t i : ℂ)) - 1)
  have hz : z.re ≤ 0 := by
    simp only [z, Complex.re_sum]
    apply Finset.sum_nonpos
    intro i _
    simpa [Complex.mul_re, Complex.exp_re] using
      mul_nonpos_of_nonneg_of_nonpos (p i).coe_nonneg
        (sub_nonpos.mpr (Real.cos_le_one (t i)))
  trans (1 - z / (p₀ : ℂ)) ^ (-(r : ℂ))
  · simpa only [complexMGF, id_eq, z] using
      complexMGF_id_gammaMeasure hr hp₀ (lt_of_le_of_lt hz hp₀)
  have hbase : 1 - z / (p₀ : ℂ) =
      (1 - ∑ i, (p i : ℂ) * Complex.exp (Complex.I * (t i : ℂ))) / p₀ := by
    have hp' : (p₀ : ℂ) + ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hp
    simp only [z, mul_sub, mul_one, Finset.sum_sub_distrib]
    field_simp [Complex.ofReal_ne_zero.mpr hp₀.ne']
    linear_combination hp'
  have hpos : 0 < (1 - z / (p₀ : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re]
    exact sub_pos.mpr (lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hz hp₀.le)
      zero_lt_one)
  have harg : (1 - z / (p₀ : ℂ)).arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  rw [Complex.cpow_neg, ← Complex.inv_cpow _ _ harg, hbase, inv_div]

end TauCeti.Probability
