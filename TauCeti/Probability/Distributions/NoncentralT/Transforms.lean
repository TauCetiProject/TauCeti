/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralT.Basic
import TauCeti.Probability.Distributions.InverseGamma.Moments

/-!
# Exponential integrability of noncentral t laws

Every valid noncentral t law has exponential-integrability domain `{0}`, independently of its
noncentrality. Thus neither tail admits a nonzero exponential moment, even when the law is
asymmetric. The same criterion is supplied for random variables with this law.

Integrating the Gaussian factor of the ratio construction gives an exponential with a positive
quadratic term in the reciprocal chi-squared square root. Completing the square bounds it below
by a positive-rate inverse-gamma exponential, whose integral diverges.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {ν δ t : ℝ}

/-- A noncentral t law has no nonzero exponential moment, for any real noncentrality. -/
theorem not_integrable_exp_mul_id_noncentralTMeasure (hν : 0 < ν) (ht : t ≠ 0) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralTMeasure ν δ) := by
  intro h
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [noncentralTMeasure_eq_map_gaussianReal hν,
    integrable_map_measure (by fun_prop) (by fun_prop)] at h
  -- Integrate out the Gaussian numerator before comparing the remaining positive integrand.
  have hinner (v : ℝ) :
      ∫ x, exp (t * (x / √(v / ν))) ∂gaussianReal δ 1 =
        exp (δ * (t / √(v / ν)) + (t / √(v / ν)) ^ 2 / 2) := by
    simpa only [mgf, id_eq, NNReal.coe_one, one_mul, div_mul_eq_mul_div, mul_div_assoc] using
      congrFun (mgf_id_gaussianReal (μ := δ) (v := 1)) (t / √(v / ν))
  have hg := h.integral_prod_right
  simp only [Function.comp_apply, hinner] at hg
  -- Completing the square absorbs the linear noncentrality term into a constant multiplier.
  have hi : Integrable (fun v : ℝ ↦ exp (t ^ 2 * ν / 4 * v⁻¹)) (chiSquaredMeasure ν) := by
    refine (hg.const_mul (exp (δ ^ 2))).mono' (by fun_prop) ?_
    filter_upwards [ae_pos_chiSquaredMeasure hν] with v hv
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
    apply exp_le_exp.mpr
    have heq : t ^ 2 * ν / 4 * v⁻¹ = (t / √(v / ν)) ^ 2 / 4 := by
      rw [div_pow, sq_sqrt (div_pos hv hν).le]
      field_simp
    rw [heq]
    nlinarith [sq_nonneg (δ + (t / √(v / ν)) / 2)]
  -- Inversion identifies this last exponential with a forbidden inverse-gamma moment.
  have hinv : Integrable (fun x : ℝ ↦ exp (t ^ 2 * ν / 4 * x))
      (inverseGammaMeasure (ν / 2) (1 / 2)) := by
    rw [inverseGammaMeasure_of_pos (by positivity) (by positivity),
      integrable_map_measure (by fun_prop) (by fun_prop)]
    rwa [chiSquaredMeasure_eq_gammaMeasure hν] at hi
  exact not_integrable_exp_mul_inverseGammaMeasure (by positivity) (by positivity)
    (by positivity : 0 < t ^ 2 * ν / 4) hinv

/-- The exponential integrand under a valid noncentral t law is integrable exactly at zero. -/
@[simp]
theorem integrable_exp_mul_id_noncentralTMeasure_iff (hν : 0 < ν) (δ t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralTMeasure ν δ) ↔ t = 0 := by
  refine ⟨fun h ↦ by_contra fun ht ↦ not_integrable_exp_mul_id_noncentralTMeasure hν ht h, ?_⟩
  rintro rfl
  simp

/-- The exact exponential-integrability domain of every valid noncentral t law is `{0}`. -/
@[simp]
theorem integrableExpSet_id_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    integrableExpSet id (noncentralTMeasure ν δ) = {0} := by
  ext t
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_singleton_iff] using
    integrable_exp_mul_id_noncentralTMeasure_iff hν δ t

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A noncentral t random variable has an integrable exponential exactly at rate zero. -/
theorem integrable_exp_mul_of_hasLaw_noncentralTMeasure_iff (hν : 0 < ν)
    (hX : HasLaw X (noncentralTMeasure ν δ) P) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) P ↔ t = 0 := by
  rw [← integrable_exp_mul_id_noncentralTMeasure_iff hν δ t, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

end TauCeti.Probability
