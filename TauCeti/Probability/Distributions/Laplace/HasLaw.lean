/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Laplace.Basic

/-!
# Observable formulas for Laplace random variables

This file transfers the elementary moment and transform formulas for
`TauCeti.Probability.laplaceMeasure` to random variables carrying that law. It gives every
absolute central moment, the expectation and variance, the exact exponential-integrability
domain, the moment- and cumulant-generating functions, and the characteristic function of the
image law.

The measure-level formulas remain in `TauCeti.Probability.Distributions.Laplace.Basic`; the
declarations here are the `ProbabilityTheory.HasLaw` interface used when a random variable,
rather than its distribution, is the input.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 24.
-/

public section

open MeasureTheory
open scoped Nat

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m b : ℝ}

/-- Every natural power of the absolute deviation of a Laplace random variable from its location
is integrable. -/
theorem integrable_pow_abs_sub_laplaceMeasure
    (hX : HasLaw X (laplaceMeasure m b) P) (n : ℕ) :
    Integrable (fun ω ↦ |X ω - m| ^ n) P :=
  hX.integrable_fun_comp
    (TauCeti.Probability.integrable_pow_abs_sub_laplaceMeasure m n)

/-- The absolute central moments of a Laplace random variable with positive scale. -/
theorem integral_pow_abs_sub_laplaceMeasure
    (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) (n : ℕ) :
    ∫ ω, |X ω - m| ^ n ∂P = n ! * b ^ n := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ |x - m| ^ n),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_abs_sub_laplaceMeasure hb]

/-- The deviation of a Laplace random variable from its location is integrable. -/
theorem integrable_sub_const_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) :
    Integrable (fun ω ↦ X ω - m) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_sub_const_laplaceMeasure m)

/-- A Laplace random variable is integrable. -/
theorem integrable_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) :
    Integrable X P := by
  simpa only [id_eq] using
    hX.integrable_fun_comp (TauCeti.Probability.integrable_id_laplaceMeasure m)

/-- The expected deviation of a Laplace random variable from its location vanishes. -/
theorem integral_sub_const_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) :
    ∫ ω, (X ω - m) ∂P = 0 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x - m), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sub_const_laplaceMeasure]

/-- The expectation of a Laplace random variable is its location parameter. -/
theorem integral_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) :
    ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_laplaceMeasure hb]

/-- The variance of a Laplace random variable with positive scale is twice the squared scale. -/
theorem variance_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) :
    variance X P = 2 * b ^ 2 := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_laplaceMeasure hb]

/-- The exponential of a scalar multiple of a Laplace random variable is integrable exactly when
the scalar lies strictly between the two reciprocal-scale endpoints. -/
theorem integrable_exp_mul_laplaceMeasure_iff
    (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔ t ∈ Set.Ioo (-b⁻¹) b⁻¹ := by
  rw [← TauCeti.Probability.integrable_exp_mul_laplaceMeasure_iff hb m t,
    ← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  simp only [Function.comp_def]

/-- The exact exponential-integrability domain of a Laplace random variable with positive scale.
-/
theorem integrableExpSet_laplaceMeasure
    (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) :
    integrableExpSet X P = Set.Ioo (-b⁻¹) b⁻¹ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  exact hX.integrable_exp_mul_laplaceMeasure_iff hb t

/-- The moment-generating function of a Laplace random variable, on its exact finiteness domain.
-/
theorem mgf_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) {t : ℝ}
    (ht : t ∈ Set.Ioo (-b⁻¹) b⁻¹) :
    mgf X P t = Real.exp (m * t) / (1 - b ^ 2 * t ^ 2) := by
  rw [← TauCeti.Probability.mgf_id_laplaceMeasure m ht, ← hX.map_eq,
    mgf_map hX.aemeasurable (by fun_prop), Function.id_comp]

/-- The cumulant-generating function of a Laplace random variable, on its exact finiteness
domain. -/
theorem cgf_laplaceMeasure (hX : HasLaw X (laplaceMeasure m b) P) {t : ℝ}
    (ht : t ∈ Set.Ioo (-b⁻¹) b⁻¹) :
    cgf X P t = Real.log (Real.exp (m * t) / (1 - b ^ 2 * t ^ 2)) := by
  rw [cgf, hX.mgf_laplaceMeasure ht]

/-- The characteristic function of the image law of a Laplace random variable with positive
scale. -/
theorem charFun_map_laplaceMeasure
    (hX : HasLaw X (laplaceMeasure m b) P) (hb : 0 < b) (t : ℝ) :
    charFun (P.map X) t = Complex.exp (Complex.I * m * t) / (1 + b ^ 2 * t ^ 2) := by
  rw [hX.map_eq, TauCeti.Probability.charFun_laplaceMeasure hb]

end ProbabilityTheory.HasLaw
