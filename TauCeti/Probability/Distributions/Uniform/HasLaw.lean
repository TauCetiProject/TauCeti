/-
Copyright (c) 2026 Fabian Zaiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Zaiser
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Observable formulas for interval-uniform random variables

This file transfers the elementary moment and transform formulas for
TauCeti.Probability.uniformMeasure to random variables carrying that law. It gives integrability,
expectation, variance, the exact exponential-integrability domain, moment and cumulant generating
functions, and the characteristic function of the image law.

The measure-level results remain in TauCeti.Probability.Distributions.Uniform.Basic; the
declarations here are the ProbabilityTheory.HasLaw interface used when a random variable, rather
than its distribution, is the input.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 26.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {a b : ℝ}

/-- An interval-uniform random variable is integrable, including when its totalized law is zero. -/
theorem integrable_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) : Integrable X P := by
  apply hX.integrable
  exact TauCeti.Probability.integrable_uniformMeasure
    (Continuous.integrableOn_Ioc continuous_id)

/-- The expectation of an interval-uniform random variable is the midpoint of its interval. -/
theorem integral_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) :
    ∫ ω, X ω ∂P = (a + b) / 2 := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_uniformMeasure hab]

/-- The variance of an interval-uniform random variable is one twelfth of the squared interval
length. -/
theorem variance_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) :
    variance X P = (b - a) ^ 2 / 12 := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_uniformMeasure hab]

/-- Every real exponential moment of an interval-uniform random variable is integrable. -/
theorem integrable_exp_mul_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  simpa only [Function.comp_def] using
    hX.integrable_comp
      (TauCeti.Probability.integrable_exp_mul_id_uniformMeasure (a := a) (b := b) (t := t))

/-- The exact exponential-integrability domain of an interval-uniform random variable is all of
the real line. -/
theorem integrableExpSet_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) :
    integrableExpSet X P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hX.integrable_exp_mul_uniformMeasure t

/-- The moment-generating function at zero of an interval-uniform random variable. -/
theorem mgf_uniformMeasure_zero (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) :
    mgf X P 0 = 1 := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_uniformMeasure_zero hab]

/-- The moment-generating function of an interval-uniform random variable away from zero. -/
theorem mgf_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b)
    {t : ℝ} (ht : t ≠ 0) :
    mgf X P t = (Real.exp (t * b) - Real.exp (t * a)) / ((b - a) * t) := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_uniformMeasure hab ht]

/-- The moment-generating function of a nondegenerate interval-uniform random variable is
strictly positive. -/
theorem mgf_uniformMeasure_pos (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) (t : ℝ) :
    0 < mgf X P t := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq]
  exact TauCeti.Probability.mgf_id_uniformMeasure_pos hab t

/-- The cumulant-generating function at zero of an interval-uniform random variable. -/
theorem cgf_uniformMeasure_zero (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) :
    cgf X P 0 = 0 := by
  rw [cgf, hX.mgf_uniformMeasure_zero hab, Real.log_one]

/-- The cumulant-generating function of an interval-uniform random variable away from zero. -/
theorem cgf_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b)
    {t : ℝ} (ht : t ≠ 0) :
    cgf X P t =
      Real.log ((Real.exp (t * b) - Real.exp (t * a)) / ((b - a) * t)) := by
  rw [cgf, hX.mgf_uniformMeasure hab ht]

/-- The characteristic function at zero of the image law of an interval-uniform random
variable. -/
theorem charFun_map_uniformMeasure_zero
    (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b) :
    charFun (P.map X) 0 = 1 := by
  rw [hX.map_eq, TauCeti.Probability.charFun_uniformMeasure_zero hab]

/-- The characteristic function of the image law of an interval-uniform random variable away
from zero. -/
theorem charFun_map_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P) (hab : a < b)
    {t : ℝ} (ht : t ≠ 0) :
    charFun (P.map X) t =
      (Complex.exp (Complex.I * b * t) - Complex.exp (Complex.I * a * t)) /
        (Complex.I * ((b - a : ℝ)) * t) := by
  rw [hX.map_eq, TauCeti.Probability.charFun_uniformMeasure hab ht]

end ProbabilityTheory.HasLaw
