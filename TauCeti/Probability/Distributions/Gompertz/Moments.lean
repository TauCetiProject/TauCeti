/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gompertz.Basic

/-!
# Gompertz moments and exponential integrability

Every real exponential moment of a valid Gompertz law is finite: its defining logarithmic
transformation turns an exponential moment into a power of `1 + E / η`. All natural moments
are therefore finite as well. Their values, the mean and variance, and the moment-generating
function are expressed as convergent integrals against the rate-one exponential density.
No additional special function is needed.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {η b : ℝ}

private lemma exp_mul_gompertzTransform (hη : 0 < η) {e : ℝ} (he : 0 < e) (t b : ℝ) :
    exp (t * (log (1 + e / η) / b)) = (1 + e / η) ^ (t / b) := by
  rw [rpow_def_of_pos (by positivity : 0 < 1 + e / η)]
  congr 1
  ring

/-- Every real exponential moment of a valid Gompertz law is integrable. -/
theorem integrable_exp_mul_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (t : ℝ) :
    Integrable (fun x => exp (t * x)) (gompertzMeasure η b) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [gompertzMeasure_of_pos hη hb, integrable_map_measure (by fun_prop) (by fun_prop)]
  -- Dominate the shifted real power by a natural power with a finite source moment.
  obtain ⟨n, hn⟩ := exists_nat_gt (t / b)
  have hLp : MemLp id (n : ℝ≥0∞) (expMeasure 1) := by
    have hi : 0 ∈ interior (integrableExpSet id (expMeasure 1)) := by
      rw [integrableExpSet_id_expMeasure one_pos, isOpen_Iio.interior_eq]
      exact one_pos
    simpa using memLp_of_mem_interior_integrableExpSet hi (n : ℝ≥0)
  have hpoly : MemLp (fun e : ℝ => 1 + e / η) (n : ℝ≥0∞) (expMeasure 1) := by
    simpa only [id_eq, div_eq_mul_inv, Pi.add_def] using (memLp_const 1).add (hLp.mul_const η⁻¹)
  apply hpoly.integrable_norm_pow'.mono'
    ((by fun_prop : Measurable (fun e : ℝ => exp (t * (log (1 + e / η) / b)))).aestronglyMeasurable)
  filter_upwards [ae_pos_expMeasure 1] with e he
  have hbase : 1 ≤ 1 + e / η := by linarith [div_pos he hη]
  simp only [norm_of_nonneg (exp_nonneg _), Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans_le hbase)]
  rw [exp_mul_gompertzTransform hη he]
  simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hbase hn.le

/-- The exact exponential-integrability domain of a valid Gompertz law is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    integrableExpSet id (gompertzMeasure η b) = univ := by
  ext t
  exact iff_true_intro (integrable_exp_mul_id_gompertzMeasure hη hb t)

/-- Every natural raw moment of a Gompertz law is integrable. -/
theorem integrable_pow_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (n : ℕ) :
    Integrable (fun x => x ^ n) (gompertzMeasure η b) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) (n := n)
  rw [integrableExpSet_id_gompertzMeasure hη hb, interior_univ]
  trivial

/-- Gompertz raw moments as convergent logarithmic integrals against the exponential density.
This includes order zero. -/
theorem integral_pow_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂gompertzMeasure η b =
      b⁻¹ ^ n * ∫ e in Ioi 0, log (1 + e / η) ^ n * exp (-e) := by
  rw [gompertzMeasure_of_pos hη hb, integral_map (by fun_prop) (by fun_prop),
    integral_expMeasure_eq_integral_Ioi one_pos, ← integral_const_mul]
  congr 1
  funext e
  simp only [one_mul, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

/-- The Gompertz mean, expressed through its convergent first logarithmic integral. -/
theorem integral_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    ∫ x, x ∂gompertzMeasure η b =
      b⁻¹ * ∫ e in Ioi 0, log (1 + e / η) * exp (-e) := by
  simpa using integral_pow_gompertzMeasure hη hb 1

/-- The Gompertz variance, expressed through its first two logarithmic integrals. -/
theorem variance_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    Var[id; gompertzMeasure η b] = b⁻¹ ^ 2 *
      ((∫ e in Ioi 0, log (1 + e / η) ^ 2 * exp (-e)) -
        (∫ e in Ioi 0, log (1 + e / η) * exp (-e)) ^ 2) := by
  let _ := isProbabilityMeasure_gompertzMeasure hη hb
  have hLp : MemLp id 2 (gompertzMeasure η b) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_pow_gompertzMeasure hη hb 2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_pow_gompertzMeasure hη hb 2,
    integral_id_gompertzMeasure hη hb]
  ring

/-- The Gompertz mgf is a convergent shifted-power integral for every real argument. -/
theorem mgf_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (t : ℝ) :
    mgf id (gompertzMeasure η b) t =
      ∫ e in Ioi 0, (1 + e / η) ^ (t / b) * exp (-e) := by
  rw [mgf, gompertzMeasure_of_pos hη hb, integral_map (by fun_prop) (by fun_prop),
    integral_expMeasure_eq_integral_Ioi one_pos]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro e he
  simp only [one_mul, id_eq, smul_eq_mul]
  rw [exp_mul_gompertzTransform hη he, mul_comm]

/-- The Gompertz cgf is the logarithm of its convergent shifted-power integral. -/
theorem cgf_id_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (t : ℝ) :
    cgf id (gompertzMeasure η b) t =
      log (∫ e in Ioi 0, (1 + e / η) ^ (t / b) * exp (-e)) := by
  rw [cgf, mgf_id_gompertzMeasure hη hb]

end TauCeti.Probability
