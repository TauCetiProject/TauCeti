/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
public import TauCeti.Probability.Distributions.Gamma.Poisson
public import TauCeti.Probability.Distributions.Poisson.Sum

/-!
# Aggregation and marginals of negative-multinomial laws

Merging categories preserves the negative-multinomial family, with the same success weight
and with category weights summed over fibres. No surjectivity is needed: empty fibres have
weight zero and hence count zero. The total count and each coordinate have negative-binomial
laws. All results include shape zero and zero category weights.

The identities follow the Gamma–Poisson construction, using independent Poisson aggregation
and Gamma scaling rather than summing the multivariate singleton masses. They allow a count
vector to be coarsened and its scalar marginals to be analyzed with the negative-binomial API.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Merging any finite collection of categories preserves the negative-multinomial law.
The success weight stays fixed, and the category weights add over fibres. -/
@[simp]
theorem map_funOnFinite_map_negativeMultinomialMeasure (f : ι → κ) {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    (negativeMultinomialMeasure r p₀ p).map (FunOnFinite.map (M := ℕ) f) =
      negativeMultinomialMeasure r p₀ (FunOnFinite.map (M := ℝ≥0) f p) := by
  classical
  have hsum : ∑ j, (FunOnFinite.map (M := ℝ≥0) f p j : ℝ) = ∑ i, (p i : ℝ) := by
    simp only [FunOnFinite.map_apply_apply, NNReal.coe_sum]
    exact Finset.sum_fiberwise Finset.univ f (fun i => (p i : ℝ))
  have hp' : p₀ + ∑ j, (FunOnFinite.map (M := ℝ≥0) f p j : ℝ) = 1 := by rwa [hsum]
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_zero hp₀ hp,
      negativeMultinomialMeasure_zero hp₀ hp', Measure.map_dirac' (by fun_prop)]
    congr 1
    ext j
    simp [FunOnFinite.map_apply_apply]
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp,
    negativeMultinomialMeasure_of_pos hr hp₀ hp',
    Measure.map_bind (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable
      (.of_discrete)]
  apply Measure.bind_congr_right
  filter_upwards [] with x
  rw [map_funOnFinite_map_pi_poissonMeasure]
  congr 1
  funext j
  rw [FunOnFinite.map_apply_apply, Finset.sum_mul]

/-- Each negative-multinomial coordinate is negative-binomial. A zero category weight
gives success probability one, so its count is constantly zero. -/
@[simp]
theorem map_eval_negativeMultinomialMeasure {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    (negativeMultinomialMeasure r p₀ p).map (fun k => k i) =
      negativeBinomialMeasure r (p₀ / (p₀ + p i)) := by
  have hden : 0 < p₀ + (p i : ℝ) := by positivity
  have hprob : 0 < p₀ / (p₀ + p i) := div_pos hp₀ hden
  have hprob1 : p₀ / (p₀ + p i) ≤ 1 :=
    (div_le_one hden).mpr (le_add_of_nonneg_right (p i).coe_nonneg)
  rcases hr.eq_or_lt with rfl | hr
  · simp [negativeMultinomialMeasure_zero hp₀ hp,
      negativeBinomialMeasure_zero hprob hprob1]
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp,
    Measure.map_bind (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable
      (.of_discrete)]
  simp_rw [(measurePreserving_eval _ i).map_eq]
  exact bind_gammaMeasure_poissonMeasure_mul_toNNReal hr hp₀ (p i)

/-- The total of all negative-multinomial counts has negative-binomial law with the
original shape and success probability. Empty category types and Dirac boundaries are included. -/
@[simp]
theorem map_sum_negativeMultinomialMeasure {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    (negativeMultinomialMeasure r p₀ p).map (fun k => ∑ i, k i) =
      negativeBinomialMeasure r p₀ := by
  have hprob1 : p₀ ≤ 1 := by
    have : 0 ≤ ∑ i, (p i : ℝ) := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    linarith
  rcases hr.eq_or_lt with rfl | hr
  · simp [negativeMultinomialMeasure_zero hp₀ hp, negativeBinomialMeasure_zero hp₀ hprob1]
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp,
    Measure.map_bind (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable
      (.of_discrete)]
  simp_rw [map_sum_pi_poissonMeasure, ← Finset.sum_mul]
  rw [bind_gammaMeasure_poissonMeasure_mul_toNNReal hr hp₀,
    NNReal.coe_sum, hp, div_one]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [Fintype ι] [Fintype κ] {X : Ω → ι → ℕ} {r p₀ : ℝ} {p : ι → ℝ≥0}

/-- Merging categories of a random negative-multinomial count vector adds their weights. -/
theorem funOnFinite_map_negativeMultinomialMeasure
    (hX : HasLaw X (negativeMultinomialMeasure r p₀ p) P) (f : ι → κ)
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    HasLaw (fun ω => FunOnFinite.map (M := ℕ) f (X ω))
      (negativeMultinomialMeasure r p₀ (FunOnFinite.map (M := ℝ≥0) f p)) P :=
  (HasLaw.mk (.of_discrete)
    (map_funOnFinite_map_negativeMultinomialMeasure f hr hp₀ hp)).fun_comp hX

/-- A coordinate of a random negative-multinomial vector has its negative-binomial marginal. -/
theorem eval_negativeMultinomialMeasure
    (hX : HasLaw X (negativeMultinomialMeasure r p₀ p) P)
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    HasLaw (fun ω => X ω i) (negativeBinomialMeasure r (p₀ / (p₀ + p i))) P :=
  (HasLaw.mk (.of_discrete) (map_eval_negativeMultinomialMeasure hr hp₀ hp i)).fun_comp hX

/-- The total of a random negative-multinomial vector has negative-binomial law. -/
theorem sum_negativeMultinomialMeasure
    (hX : HasLaw X (negativeMultinomialMeasure r p₀ p) P)
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    HasLaw (fun ω => ∑ i, X ω i) (negativeBinomialMeasure r p₀) P :=
  (HasLaw.mk (.of_discrete) (map_sum_negativeMultinomialMeasure hr hp₀ hp)).fun_comp hX

end ProbabilityTheory.HasLaw
