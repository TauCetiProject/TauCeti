/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Observable formulas for the Bernoulli distribution

This file transfers the probability-generating function and exponential-transform theory of the
Bernoulli measure to random variables carrying that law. The probability-generating function uses
the native natural-valued law, while exponential moments use the real-valued law on `{0, 1}`.

## Main results

* `ProbabilityTheory.HasLaw.pgf_bernoulliMeasure` computes the probability-generating function;
* `ProbabilityTheory.HasLaw.integrableExpSet_bernoulliMeasure` gives the exact exponential domain;
* `ProbabilityTheory.HasLaw.mgf_bernoulliMeasure` and
  `ProbabilityTheory.HasLaw.cgf_bernoulliMeasure` compute the real exponential transforms.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 3.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The probability-generating function of a natural-valued Bernoulli random variable. -/
theorem pgf_bernoulliMeasure {X : Ω → ℕ} {p : unitInterval}
    (hX : HasLaw X Ber((1 : ℕ), 0, p) P) (t : ℝ) :
    pgf X P t = 1 - (p : ℝ) + (p : ℝ) * t :=
  (TauCeti.Probability.HasLaw.pgf_eq hX t).trans
    (TauCeti.Probability.pgf_bernoulliMeasure p t)

/-- Every real exponential moment of a real-valued Bernoulli random variable is integrable. -/
theorem integrable_exp_mul_bernoulliMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber((1 : ℝ), 0, p) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  simpa only [Function.comp_def] using hX.integrable_fun_comp
    (integrable_bernoulliMeasure (1 : ℝ) 0 p fun x ↦ Real.exp (t * x))

/-- The exact exponential-integrability domain of a real-valued Bernoulli random variable is all
of `ℝ`. -/
theorem integrableExpSet_bernoulliMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber((1 : ℝ), 0, p) P) : integrableExpSet X P = Set.univ := by
  ext t
  simpa only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true] using
    hX.integrable_exp_mul_bernoulliMeasure t

/-- The moment-generating function of a real-valued Bernoulli random variable. -/
theorem mgf_bernoulliMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber((1 : ℝ), 0, p) P) (t : ℝ) :
    mgf X P t = 1 - (p : ℝ) + (p : ℝ) * Real.exp t := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq]
  exact TauCeti.Probability.mgf_id_bernoulliMeasure p t

/-- The cumulant-generating function of a real-valued Bernoulli random variable. -/
theorem cgf_bernoulliMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber((1 : ℝ), 0, p) P) (t : ℝ) :
    cgf X P t = Real.log (1 - (p : ℝ) + (p : ℝ) * Real.exp t) := by
  rw [cgf, hX.mgf_bernoulliMeasure]

end ProbabilityTheory.HasLaw
