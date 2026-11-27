/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The arcsine distribution

The arcsine distribution on the unit interval is the beta distribution with both shape
parameters equal to one half. This file records the measure-level definition, its exact
topological support, natural moments, mean, variance, and exponential-integrability domain.
Defining the law as a beta measure makes these results direct specializations of the beta theory.
The corresponding `ProbabilityTheory.HasLaw` results expose the same support, moment, and
exponential-integrability facts for random variables carrying the arcsine law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The arcsine law on `[0, 1]`, realized as the beta law with shapes `(1 / 2, 1 / 2)`. -/
def arcsineMeasure : Measure ℝ :=
  betaMeasure (1 / 2) (1 / 2)

/-- The arcsine law is the symmetric beta law with both shape parameters one half. -/
theorem arcsineMeasure_eq_betaMeasure :
    arcsineMeasure = betaMeasure (1 / 2) (1 / 2) :=
  (rfl)

/-- The arcsine law is a probability measure. -/
noncomputable instance isProbabilityMeasure_arcsineMeasure :
    IsProbabilityMeasure arcsineMeasure :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

/-- The arcsine law has no atoms, including at the endpoints of its support. -/
instance : NullSingletonClass arcsineMeasure := by
  rw [arcsineMeasure_eq_betaMeasure, betaMeasure]
  infer_instance

/-- An arcsine variable lies almost everywhere in the open unit interval. -/
theorem ae_mem_Ioo_arcsineMeasure : ∀ᵐ x ∂arcsineMeasure, x ∈ Ioo (0 : ℝ) 1 := by
  simpa only [arcsineMeasure] using ae_mem_Ioo_betaMeasure (1 / 2) (1 / 2)

/-- The topological support of the arcsine law is the closed unit interval. -/
@[simp]
theorem support_arcsineMeasure : arcsineMeasure.support = Icc 0 1 := by
  simpa only [arcsineMeasure] using
    support_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)

/-- Every natural power is integrable against the arcsine law. -/
theorem integrable_pow_arcsineMeasure (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) arcsineMeasure := by
  simpa only [arcsineMeasure] using
    integrable_pow_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num) n

/-- The natural moments of the arcsine law, inherited from its beta realization. -/
@[simp]
theorem integral_pow_arcsineMeasure (n : ℕ) :
    ∫ x, x ^ n ∂arcsineMeasure =
      Real.Gamma (1 / 2 + n) * Real.Gamma (1 / 2 + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma (1 / 2 + 1 / 2 + n)) := by
  simpa only [arcsineMeasure] using
    integral_pow_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num) n

/-- The mean of the arcsine law is one half. -/
@[simp]
theorem integral_id_arcsineMeasure : ∫ x, x ∂arcsineMeasure = 1 / 2 := by
  rw [arcsineMeasure, integral_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)]
  norm_num

/-- The variance of the arcsine law is one eighth. -/
@[simp]
theorem variance_id_arcsineMeasure : variance id arcsineMeasure = 1 / 8 := by
  rw [arcsineMeasure, variance_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)]
  norm_num

/-- Every exponential moment of the arcsine law exists. -/
@[simp]
theorem integrableExpSet_id_arcsineMeasure : integrableExpSet id arcsineMeasure = univ := by
  simpa only [arcsineMeasure] using
    integrableExpSet_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open MeasureTheory TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with the arcsine law lies almost everywhere in the open unit interval. -/
theorem ae_mem_Ioo_arcsineMeasure (hX : HasLaw X arcsineMeasure P) :
    ∀ᵐ ω ∂P, X ω ∈ Set.Ioo (0 : ℝ) 1 :=
  hX.ae_iff measurableSet_Ioo.mem |>.2 TauCeti.Probability.ae_mem_Ioo_arcsineMeasure

/-- Every natural power of an arcsine random variable is integrable. -/
theorem integrable_pow_arcsineMeasure (hX : HasLaw X arcsineMeasure P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_arcsineMeasure n)

/-- The natural raw moments of an arcsine random variable. -/
theorem integral_pow_arcsineMeasure (hX : HasLaw X arcsineMeasure P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P =
      Real.Gamma (1 / 2 + n) * Real.Gamma (1 / 2 + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma (1 / 2 + 1 / 2 + n)) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_arcsineMeasure]

/-- The expectation of an arcsine random variable is one half. -/
theorem integral_arcsineMeasure (hX : HasLaw X arcsineMeasure P) : ∫ ω, X ω ∂P = 1 / 2 := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_arcsineMeasure]

/-- The variance of an arcsine random variable is one eighth. -/
theorem variance_arcsineMeasure (hX : HasLaw X arcsineMeasure P) :
    variance X P = 1 / 8 := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_arcsineMeasure]

/-- Every real exponential moment of an arcsine random variable is integrable. -/
theorem integrable_exp_mul_arcsineMeasure (hX : HasLaw X arcsineMeasure P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  refine hX.integrable_fun_comp (f := fun x : ℝ ↦ Real.exp (t * x)) ?_
  have ht : t ∈ integrableExpSet id arcsineMeasure := by simp
  simpa only [integrableExpSet, Set.mem_ofPred_eq, id_eq] using ht

end ProbabilityTheory.HasLaw
