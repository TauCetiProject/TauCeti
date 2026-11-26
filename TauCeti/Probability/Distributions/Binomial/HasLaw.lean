/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic

/-!
# Observable formulas for the binomial distribution

This file transfers the probability-generating function, second moment, and exponential-transform
theory of the binomial measure to random variables carrying that law. The probability-generating
function uses the native natural-valued law, while moments and exponential transforms use the real
cast law.

## Main results

* `ProbabilityTheory.HasLaw.pgf_binomial` computes the probability-generating function;
* `ProbabilityTheory.HasLaw.integral_sq_map_cast_binomial` gives the second raw moment;
* `ProbabilityTheory.HasLaw.integrableExpSet_map_cast_binomial` gives the exact exponential domain;
* `ProbabilityTheory.HasLaw.mgf_map_cast_binomial` and
  `ProbabilityTheory.HasLaw.cgf_map_cast_binomial` compute the real exponential transforms.

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

/-- The probability-generating function of a natural-valued binomial random variable. -/
theorem pgf_binomial {X : Ω → ℕ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(n, p) P) (t : ℝ) :
    pgf X P t = (1 - (p : ℝ) + (p : ℝ) * t) ^ n :=
  (TauCeti.Probability.HasLaw.pgf_eq hX t).trans
    (TauCeti.Probability.pgf_binomial n p t)

/-- Every real exponential moment of a real-valued binomial random variable is integrable. -/
theorem integrable_exp_mul_map_cast_binomial {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  simpa only [Function.comp_def] using
    hX.integrable_fun_comp (integrable_map_cast_binomial fun x : ℝ ↦ Real.exp (t * x))

/-- The exact exponential-integrability domain of a real-valued binomial random variable is all
of `ℝ`. -/
theorem integrableExpSet_map_cast_binomial {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) : integrableExpSet X P = Set.univ := by
  ext t
  simpa only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true] using
    hX.integrable_exp_mul_map_cast_binomial t

/-- The second raw moment of a real-valued binomial random variable. -/
theorem integral_sq_map_cast_binomial {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) :
    ∫ ω, X ω ^ 2 ∂P = (p : ℝ) * (1 - p) * n + ((p : ℝ) * n) ^ 2 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ 2), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sq_id_map_cast_binomial]

/-- The moment-generating function of a real-valued binomial random variable. -/
theorem mgf_map_cast_binomial {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) (t : ℝ) :
    mgf X P t = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq]
  exact TauCeti.Probability.mgf_id_map_cast_binomial n p t

/-- The cumulant-generating function of a real-valued binomial random variable. -/
theorem cgf_map_cast_binomial {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) (t : ℝ) :
    cgf X P t = Real.log ((1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n) := by
  rw [cgf, hX.mgf_map_cast_binomial]

end ProbabilityTheory.HasLaw
