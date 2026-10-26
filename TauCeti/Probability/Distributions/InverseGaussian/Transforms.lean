/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGaussian.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Probability.Distributions.Levy.Moments

/-!
# Exponential moments of inverse Gaussian laws

The inverse Gaussian law with positive mean `μ` and shape `lam` has exact
exponential-integrability domain `(-∞, lam / (2 * μ ^ 2)]`. Its moment-generating function is
`exp (lam / μ * (1 - √(1 - 2 * μ ^ 2 * t / lam)))`, including the finite right endpoint.

Below that endpoint, exponential reweighting changes the mean of the inverse Gaussian density.
At the endpoint, it instead gives a constant multiple of the Lévy density. The latter identity
also transfers the sharp divergence beyond the endpoint from the Lévy law.

## References

* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {μ lam t : ℝ}

private theorem inverseGaussianPDFReal_mul_exp_eq_levy
    (hμ : 0 < μ) (hlam : 0 < lam) (t x : ℝ) :
    inverseGaussianPDFReal μ lam x * exp (t * x) =
      exp (lam / μ) * (levyPDFReal 0 lam x *
        exp ((t - lam / (2 * μ ^ 2)) * x)) := by
  by_cases hx : 0 < x
  · rw [inverseGaussianPDFReal_of_pos hμ hlam hx, levyPDFReal_of_lt hlam hx,
      sub_zero]
    have hfactor : √(lam / (2 * π * x ^ 3)) =
        √(lam / (2 * π)) * x ^ (-(3 / 2 : ℝ)) := by
      have hthree : (3 / 2 : ℝ) = (3 : ℕ) * (1 / 2 : ℝ) := by norm_num
      rw [Real.rpow_neg hx.le, hthree, Real.rpow_natCast_mul hx.le, ← Real.sqrt_eq_rpow,
        ← div_eq_mul_inv, ← Real.sqrt_div (by positivity)]
      congr 1
      ring
    rw [hfactor]
    have he : -(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x) + t * x =
        lam / μ + (-lam / (2 * x) + (t - lam / (2 * μ ^ 2)) * x) := by
      field_simp
      ring
    simp only [mul_assoc, ← exp_add]
    simp only [mul_assoc] at he
    rw [he, exp_add]
    ring
  · simp [inverseGaussianPDFReal_of_nonpos (not_lt.mp hx),
      levyPDFReal_of_le (not_lt.mp hx)]

/-- The exact exponential-integrability domain of a valid inverse Gaussian law is a closed
half-line. In particular, its right endpoint is integrable. -/
@[simp]
theorem integrableExpSet_id_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    integrableExpSet id (inverseGaussianMeasure μ lam) = Iic (lam / (2 * μ ^ 2)) := by
  ext t
  have htransfer : Integrable (fun x : ℝ ↦ exp ((t - lam / (2 * μ ^ 2)) * x))
      (levyMeasure 0 lam) ↔ t - lam / (2 * μ ^ 2) ≤ 0 := by
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iic] using
      Set.ext_iff.mp (integrableExpSet_id_levyMeasure hlam 0) (t - lam / (2 * μ ^ 2))
  rw [levyMeasure_eq_withDensity, funext (levyPDF_eq_ofReal 0 lam)] at htransfer
  rw [integrable_withDensity_ofReal_iff (measurable_levyPDFReal 0 lam).aemeasurable
    (ae_of_all _ (levyPDFReal_nonneg 0 lam))] at htransfer
  simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iic]
  rw [integrable_inverseGaussianMeasure_iff]
  simp only [smul_eq_mul, inverseGaussianPDFReal_mul_exp_eq_levy hμ hlam]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_ne_zero _))]
  simpa only [smul_eq_mul, sub_nonpos] using htransfer

/-- Exponential moments of an inverse Gaussian law exist exactly up to and including the
critical parameter. -/
@[simp]
theorem integrable_exp_mul_inverseGaussianMeasure_iff (hμ : 0 < μ) (hlam : 0 < lam) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (inverseGaussianMeasure μ lam) ↔
      t ≤ lam / (2 * μ ^ 2) := by
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iic] using
    Set.ext_iff.mp (integrableExpSet_id_inverseGaussianMeasure hμ hlam) t

private theorem inverseGaussianPDFReal_mul_exp_eq
    (hμ : 0 < μ) (hlam : 0 < lam) {ν : ℝ} (hν : 0 < ν)
    (ht : t = lam / (2 * μ ^ 2) - lam / (2 * ν ^ 2)) (x : ℝ) :
    inverseGaussianPDFReal μ lam x * exp (t * x) =
      exp (lam / μ - lam / ν) * inverseGaussianPDFReal ν lam x := by
  by_cases hx : 0 < x
  · rw [inverseGaussianPDFReal_of_pos hμ hlam hx,
      inverseGaussianPDFReal_of_pos hν hlam hx]
    have he : -(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x) + t * x =
        lam / μ - lam / ν - (lam * (x - ν) ^ 2) / (2 * ν ^ 2 * x) := by
      rw [ht]
      field_simp
      ring
    rw [mul_assoc, ← exp_add, he, sub_eq_add_neg, exp_add]
    ring_nf
  · simp [inverseGaussianPDFReal_of_nonpos (not_lt.mp hx)]

/-- The inverse Gaussian moment-generating function, including its finite value at the
critical parameter `lam / (2 * μ ^ 2)`. -/
theorem mgf_id_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (ht : t ≤ lam / (2 * μ ^ 2)) :
    mgf id (inverseGaussianMeasure μ lam) t =
      exp (lam / μ * (1 - √(1 - 2 * μ ^ 2 * t / lam))) := by
  rcases ht.eq_or_lt with ht | ht
  · have hlevy : ∫ x, levyPDFReal 0 lam x = 1 := by
      have := isProbabilityMeasure_levyMeasure hlam 0
      have h : ∫ x, (1 : ℝ) ∂levyMeasure 0 lam = 1 := by simp
      rw [levyMeasure_eq_withDensity, funext (levyPDF_eq_ofReal 0 lam),
        integral_withDensity_ofReal (measurable_levyPDFReal 0 lam).aemeasurable
          (ae_of_all _ (levyPDFReal_nonneg 0 lam))] at h
      simpa using h
    rw [ht, mgf, integral_inverseGaussianMeasure_eq]
    simp only [id_eq, smul_eq_mul,
      inverseGaussianPDFReal_mul_exp_eq_levy hμ hlam, sub_self, zero_mul, exp_zero, mul_one,
      integral_const_mul, hlevy, mul_one]
    congr 1
    have : 1 - 2 * μ ^ 2 * (lam / (2 * μ ^ 2)) / lam = 0 := by
      field_simp
      ring
    rw [this, sqrt_zero, sub_zero, mul_one]
  · have hA : 0 < 1 - 2 * μ ^ 2 * t / lam := by
      have hden : 0 < 2 * μ ^ 2 := by positivity
      have hlt : 2 * μ ^ 2 * t < lam := by
        simpa only [mul_comm] using (lt_div_iff₀ hden).mp ht
      exact sub_pos.mpr ((div_lt_one hlam).mpr hlt)
    let ν := μ / √(1 - 2 * μ ^ 2 * t / lam)
    have hν : 0 < ν := div_pos hμ (sqrt_pos.mpr hA)
    have hνsq : ν ^ 2 = μ ^ 2 / (1 - 2 * μ ^ 2 * t / lam) := by
      dsimp [ν]
      rw [div_pow, sq_sqrt hA.le]
    have ht' : t = lam / (2 * μ ^ 2) - lam / (2 * ν ^ 2) := by
      rw [hνsq]
      field_simp [hA.ne']
      ring
    rw [mgf, integral_inverseGaussianMeasure_eq]
    simp only [id_eq, smul_eq_mul, inverseGaussianPDFReal_mul_exp_eq hμ hlam hν ht',
      integral_const_mul, integral_inverseGaussianPDFReal hν hlam, mul_one]
    congr 1
    dsimp [ν]
    field_simp

/-- The cumulant-generating function of a valid inverse Gaussian law on its exact domain,
including the finite right endpoint. -/
theorem cgf_id_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (ht : t ≤ lam / (2 * μ ^ 2)) :
    cgf id (inverseGaussianMeasure μ lam) t =
      lam / μ * (1 - √(1 - 2 * μ ^ 2 * t / lam)) := by
  rw [cgf, mgf_id_inverseGaussianMeasure hμ hlam ht, log_exp]

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The exact exponential-moment criterion for any variable with a valid inverse Gaussian
law. No separate probability assumption on the source measure is needed. -/
theorem integrable_exp_mul_of_hasLaw_inverseGaussianMeasure_iff
    (hμ : 0 < μ) (hlam : 0 < lam) (hX : HasLaw X (inverseGaussianMeasure μ lam) P) :
    Integrable (fun ω ↦ exp (t * X ω)) P ↔ t ≤ lam / (2 * μ ^ 2) := by
  rw [← integrable_exp_mul_inverseGaussianMeasure_iff hμ hlam, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- The moment-generating function of a variable with inverse Gaussian law, on its closed
exponential-integrability domain. -/
theorem mgf_of_hasLaw_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) (ht : t ≤ lam / (2 * μ ^ 2)) :
    mgf X P t = exp (lam / μ * (1 - √(1 - 2 * μ ^ 2 * t / lam))) := by
  have h := hX.integral_comp (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ ↦ exp (t * x)) (inverseGaussianMeasure μ lam))
  rw [← mgf_id_inverseGaussianMeasure hμ hlam ht]
  simpa only [mgf, Function.comp_def, id_eq] using h

/-- The cumulant-generating function of a variable with inverse Gaussian law, including the
finite critical endpoint. -/
theorem cgf_of_hasLaw_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) (ht : t ≤ lam / (2 * μ ^ 2)) :
    cgf X P t = lam / μ * (1 - √(1 - 2 * μ ^ 2 * t / lam)) := by
  rw [cgf, mgf_of_hasLaw_inverseGaussianMeasure hμ hlam hX ht, log_exp]

end RandomVariables

end TauCeti.Probability
