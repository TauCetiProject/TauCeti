/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Weibull.Transforms

/-!
# Random variables with a Weibull law

This file transfers the elementary moment and exponential-transform theory of the Weibull measure
to random variables carrying that law. The exponential moments retain the three regimes determined
by the shape: a full real domain above shape one, an endpoint at the reciprocal scale at shape one,
and the nonpositive half-line below shape one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {k lam q t : ℝ}

/-- A random variable with a Weibull law is almost surely positive. This remains true for invalid
parameters, where the totalized law is the zero measure. -/
theorem ae_pos_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P) :
    ∀ᵐ ω ∂P, 0 < X ω :=
  (hX.ae_iff measurableSet_Ioi.mem).2 (TauCeti.Probability.ae_pos_weibullMeasure k lam)

/-- A real power of a Weibull random variable is integrable exactly above the negative shape. -/
theorem integrable_rpow_weibullMeasure_iff (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) (q : ℝ) :
    Integrable (fun ω ↦ X ω ^ q) P ↔ -k < q := by
  rw [← TauCeti.Probability.integrable_rpow_weibullMeasure_iff hk hlam q, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- The real-power moment of a Weibull random variable on its exact integrability domain. -/
theorem integral_rpow_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) (hq : -k < q) :
    ∫ ω, X ω ^ q ∂P = lam ^ q * Real.Gamma (1 + q / k) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ q), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_rpow_weibullMeasure hk hlam hq]

/-- Every natural power of a Weibull random variable is integrable. This includes invalid
parameters, where the totalized Weibull measure is zero. -/
theorem integrable_pow_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P := by
  exact hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_weibullMeasure k lam n)

/-- The natural raw moments of a Weibull random variable. -/
theorem integral_pow_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = lam ^ n * Real.Gamma (1 + (n : ℝ) / k) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_weibullMeasure hk hlam]

/-- The expectation of a Weibull random variable. -/
theorem integral_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) :
    ∫ ω, X ω ∂P = lam * Real.Gamma (1 + 1 / k) := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_weibullMeasure hk hlam]

/-- The variance of a Weibull random variable. -/
theorem variance_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) :
    variance X P =
      lam ^ 2 * (Real.Gamma (1 + 2 / k) - Real.Gamma (1 + 1 / k) ^ 2) := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_weibullMeasure hk hlam]

/-- Every real exponential rate is integrable for a Weibull random variable of shape greater
than one. -/
theorem integrable_exp_mul_weibullMeasure_of_one_lt
    (hX : HasLaw X (weibullMeasure k lam) P) (hk : 1 < k) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  apply hX.integrable_fun_comp (f := fun x : ℝ ↦ Real.exp (t * x))
  exact TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_of_one_lt hk t

/-- For a Weibull random variable of shape below one, an exponential moment is finite exactly at
nonpositive rates. -/
theorem integrable_exp_mul_weibullMeasure_iff_of_lt_one
    (hX : HasLaw X (weibullMeasure k lam) P) (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔ t ≤ 0 := by
  rw [← TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_iff_of_lt_one hk hk' hlam t,
    ← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- For a shape-one Weibull random variable, an exponential moment is finite exactly below the
reciprocal scale. -/
theorem integrable_exp_mul_weibullMeasure_one_iff
    (hX : HasLaw X (weibullMeasure 1 lam) P) (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔ t < lam⁻¹ := by
  rw [← TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_one_iff hlam t,
    ← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- The exact exponential-integrability domain of a Weibull random variable. -/
theorem integrableExpSet_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 0 < k) (hlam : 0 < lam) :
    integrableExpSet X P =
      if k < 1 then Set.Iic 0 else if k = 1 then Set.Iio lam⁻¹ else Set.univ := by
  rw [← TauCeti.Probability.integrableExpSet_id_weibullMeasure hk hlam]
  ext t
  change Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (weibullMeasure k lam)
  rw [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- The moment-generating function of a superlinear Weibull random variable is its convergent
Gamma-coefficient series. -/
theorem mgf_weibullMeasure_of_one_lt (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 1 < k) (hlam : 0 < lam) (t : ℝ) :
    mgf X P t =
      ∑' n : ℕ, (t * lam) ^ n * Real.Gamma (1 + (n : ℝ) / k) / n.factorial := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_weibullMeasure_of_one_lt hk hlam]

/-- The cumulant-generating function of a superlinear Weibull random variable is the logarithm
of its Gamma-coefficient series. -/
theorem cgf_weibullMeasure_of_one_lt (hX : HasLaw X (weibullMeasure k lam) P)
    (hk : 1 < k) (hlam : 0 < lam) (t : ℝ) :
    cgf X P t = Real.log
      (∑' n : ℕ, (t * lam) ^ n * Real.Gamma (1 + (n : ℝ) / k) / n.factorial) := by
  rw [cgf, hX.mgf_weibullMeasure_of_one_lt hk hlam]

/-- The moment-generating function of a shape-one Weibull random variable below the reciprocal
scale. -/
theorem mgf_weibullMeasure_one (hX : HasLaw X (weibullMeasure 1 lam) P)
    (hlam : 0 < lam) (ht : t < lam⁻¹) :
    mgf X P t = (1 - lam * t)⁻¹ := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_weibullMeasure_one hlam ht]

/-- The cumulant-generating function of a shape-one Weibull random variable below the reciprocal
scale. -/
theorem cgf_weibullMeasure_one (hX : HasLaw X (weibullMeasure 1 lam) P)
    (hlam : 0 < lam) (ht : t < lam⁻¹) :
    cgf X P t = -Real.log (1 - lam * t) := by
  rw [cgf, hX.mgf_weibullMeasure_one hlam ht, Real.log_inv]

end ProbabilityTheory.HasLaw
