/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Basic
import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Moments of the Poisson-binomial distribution

This file develops integration and moments for the real cast of a Poisson-binomial count. Every
function is integrable against the native law because it has finite support. In particular, all
natural moments exist, the mean is the sum of the success probabilities, and the variance is the
sum of the Bernoulli variances.

## Main results

* `integral_pow_id_map_cast_poissonBinomialMeasure` gives every natural raw moment as a finite
  sum over success sets;
* `integral_id_map_cast_poissonBinomialMeasure` computes the mean;
* `variance_id_map_cast_poissonBinomialMeasure` computes the variance.

## References

* Y. H. Wang, “On the number of successes in independent trials”, *Statistica Sinica* 3 (1993),
  295–312.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every function on `ℝ` is integrable against the real cast of a Poisson-binomial law. -/
@[simp]
theorem integrable_map_cast_poissonBinomialMeasure {E : Type*} [NormedAddGroup E]
    (f : ℝ → E) (p : ι → unitInterval) :
    Integrable f ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  exact integrable_poissonBinomialMeasure (fun k ↦ f (k : ℝ)) p

/-- Every natural raw moment of a real-cast Poisson-binomial law is the corresponding finite
sum over success sets. -/
theorem integral_pow_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ) =
      ∑ s : Finset ι, (poissonBinomialWeight p s : ℝ) * (s.card : ℝ) ^ n := by
  rw [integral_map Measurable.of_discrete.aemeasurable
      (integrable_map_cast_poissonBinomialMeasure (fun x : ℝ ↦ x ^ n) p).aestronglyMeasurable,
    integral_poissonBinomialMeasure]
  simp only [smul_eq_mul]

private theorem hasLaw_sum_cast_poissonBinomialMeasure (p : ι → unitInterval) :
    HasLaw (fun x : ι → ℕ ↦ ∑ i, (x i : ℝ))
      ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ))
      (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) := by
  refine ⟨Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦
    (measurable_from_nat.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  exact map_sum_natCast_pi_bernoulliMeasure p

/-- The mean of a real-cast Poisson-binomial law is the sum of its success probabilities. -/
@[simp]
theorem integral_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) :
    ∫ x : ℝ, x ∂(poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ) =
      ∑ i, (p i : ℝ) := by
  rw [← (hasLaw_sum_cast_poissonBinomialMeasure p).integral_eq]
  have hsumfun : (fun x : ι → ℕ ↦ ∑ i, (x i : ℝ)) =
      ∑ i, fun x : ι → ℕ ↦ (x i : ℝ) := by
    funext x
    simp
  rw [hsumfun]
  have hint (i : ι) : Integrable (fun x : ι → ℕ ↦ (x i : ℝ))
      (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) :=
    (hasLaw_cast_eval_bernoulliMeasure p i).integrable
      (integrable_bernoulliMeasure (1 : ℝ) 0 (p i) id)
  calc
    ∫ x : ι → ℕ, (∑ i, fun x : ι → ℕ ↦ (x i : ℝ)) x
        ∂(Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) =
        ∑ i, ∫ x : ι → ℕ, (x i : ℝ)
          ∂(Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) := by
      simpa using integral_finsetSum Finset.univ fun i _ ↦ hint i
    _ = ∑ i, (p i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_of_hasLaw_bernoulliMeasure (hasLaw_cast_eval_bernoulliMeasure p i)

/-- The variance of a real-cast Poisson-binomial law is the sum of the component Bernoulli
variances. -/
@[simp]
theorem variance_id_map_cast_poissonBinomialMeasure (p : ι → unitInterval) :
    variance id ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) =
      ∑ i, (p i : ℝ) * (1 - p i) := by
  rw [← (hasLaw_sum_cast_poissonBinomialMeasure p).variance_eq]
  have hsumfun : (fun x : ι → ℕ ↦ ∑ i, (x i : ℝ)) =
      ∑ i, fun x : ι → ℕ ↦ (x i : ℝ) := by
    funext x
    simp
  rw [hsumfun]
  rw [variance_sum_pi]
  · apply Finset.sum_congr rfl
    intro i _
    exact variance_of_hasLaw_bernoulliMeasure (hasLaw_natCast_bernoulliMeasure (p i))
  · intro i
    exact (hasLaw_natCast_bernoulliMeasure (p i)).memLp
      ((memLp_two_iff_integrable_sq (by fun_prop)).2
        (integrable_bernoulliMeasure (1 : ℝ) 0 (p i) (fun x ↦ x ^ 2)))

end TauCeti.Probability
