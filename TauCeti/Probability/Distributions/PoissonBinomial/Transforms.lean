/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.Distributions.PoissonBinomial.Moments
import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Transforms of the Poisson-binomial distribution

This file computes the moment-generating and characteristic functions of the real cast of a
Poisson-binomial count. Both factor as products of the corresponding Bernoulli transforms, and
the exponential-integrability domain is all of `ℝ` because the law has finite support.

## Main results

* `integrableExpSet_id_map_cast_poissonBinomialMeasure` gives the exact exponential-integrability
  domain;
* `mgf_id_map_cast_poissonBinomialMeasure` gives the moment-generating function;
* `cgf_id_map_cast_poissonBinomialMeasure` gives the cumulant-generating function;
* `charFun_map_cast_poissonBinomialMeasure` gives the characteristic function.

## References

* Y. H. Wang, “On the number of successes in independent trials”, *Statistica Sinica* 3 (1993),
  295–312.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every real exponential is integrable against a real-cast Poisson-binomial law. -/
@[simp]
theorem integrableExpSet_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) :
    integrableExpSet id ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_univ, iff_true]
  exact integrable_map_cast_poissonBinomialMeasure (fun x : ℝ ↦ Real.exp (t * id x)) p

/-- The moment-generating function of a real-cast Poisson-binomial law is the product of its
Bernoulli moment-generating functions. -/
@[simp]
theorem mgf_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) (t : ℝ) :
    mgf id ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      ∏ i, (1 - (p i : ℝ) + (p i : ℝ) * Real.exp t) := by
  rw [mgf_id_map_natCast, pgf_poissonBinomialMeasure]

/-- The cumulant-generating function of a real-cast Poisson-binomial law is the sum of its
Bernoulli cumulant-generating functions. -/
@[simp]
theorem cgf_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) (t : ℝ) :
    cgf id ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      ∑ i, Real.log (1 - (p i : ℝ) + (p i : ℝ) * Real.exp t) := by
  rw [cgf, mgf_id_map_cast_poissonBinomialMeasure, Real.log_prod]
  intro i _
  have hpos := mgf_id_bernoulliMeasure_pos (p i) t
  rw [mgf_id_bernoulliMeasure] at hpos
  exact hpos.ne'

/-- The characteristic function of a real-cast Poisson-binomial law is the product of its
Bernoulli characteristic functions. -/
@[simp]
theorem charFun_map_cast_poissonBinomialMeasure (p : ι → unitInterval) (t : ℝ) :
    charFun ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      ∏ i, (1 - (p i : ℂ) + (p i : ℂ) * Complex.exp (Complex.I * t)) := by
  rw [← map_sum_natCast_pi_bernoulliMeasure p]
  let P := Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)
  let X : ι → (ι → ℕ) → ℝ := fun i x ↦ x i
  have hindep : iIndepFun X P :=
    (iIndepFun_pi (X := fun _ ↦ (Nat.cast : ℕ → ℝ)) fun _ ↦
      Measurable.of_discrete.aemeasurable)
  have hchar := congrFun (hindep.charFun_map_fun_sum_eq_prod fun _ ↦
    Measurable.of_discrete.aemeasurable) t
  rw [hchar]
  rw [Fintype.prod_apply]
  apply Finset.prod_congr rfl
  intro i _
  have hcast : HasLaw (X i) Ber((1 : ℝ), 0, p i) P := by
    simpa [P, X] using hasLaw_cast_eval_bernoulliMeasure p i
  rw [hcast.map_eq, charFun_bernoulliMeasure]

end TauCeti.Probability
