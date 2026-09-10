/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Transforms

/-!
# Aggregation of multinomial cells

Combining cells of a multinomial count vector again gives a multinomial distribution. For a map
`f : ι → κ`, the count in a target cell `j` is the sum of all source counts over the fibre of
`j`, while `Convexity.StdSimplex.map f` sums the corresponding cell probabilities.

The proof identifies the Euclidean casts by their characteristic functions. The multinomial
formula reduces the result to grouping a finite sum by the fibres of `f`.

## Main definitions and results

* `TauCeti.Probability.multinomialAggregate`: aggregate a count vector along a map of cells.
* `TauCeti.Probability.map_multinomialAggregate_multinomialMeasure`: aggregation sends a
  multinomial law to the multinomial law with aggregated probabilities.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open Classical in
/-- Aggregate a count vector by summing the counts in every fibre of a map of cells. -/
def multinomialAggregate (f : ι → κ) (k : ι → ℕ) (j : κ) : ℕ :=
  ∑ i with f i = j, k i

open Classical in
omit [Fintype κ] in
/-- The count in an aggregated cell is the sum of the counts in its fibre. -/
@[simp]
theorem multinomialAggregate_apply (f : ι → κ) (k : ι → ℕ) (j : κ) :
    multinomialAggregate f k j = ∑ i with f i = j, k i := (rfl)

omit [Fintype κ] in
/-- Aggregating count vectors is measurable for the discrete measurable structures. -/
theorem measurable_multinomialAggregate (f : ι → κ) :
    Measurable (multinomialAggregate f) :=
  measurable_of_countable _

/-- Pull a Euclidean frequency vector back along a map of cells. -/
private def pullbackFrequency (f : ι → κ) (t : EuclideanSpace ℝ κ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i ↦ t (f i)

omit [Fintype ι] [Fintype κ] in
@[simp]
private theorem pullbackFrequency_apply (f : ι → κ) (t : EuclideanSpace ℝ κ) (i : ι) :
    pullbackFrequency f t i = t (f i) := (rfl)

private theorem inner_multinomialAggregate (f : ι → κ) (k : ι → ℕ)
    (t : EuclideanSpace ℝ κ) :
    inner ℝ (multinomialToEuclidean (multinomialAggregate f k)) t =
      inner ℝ (multinomialToEuclidean k) (pullbackFrequency f t) := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    multinomialToEuclidean_apply, multinomialAggregate_apply, pullbackFrequency_apply]
  push_cast
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ j, ∑ i with f i = j, (k i : ℝ) * t (f i) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2, mul_comm]
    _ = _ := by
      simpa [mul_comm] using
        Finset.sum_fiberwise Finset.univ f (fun i ↦ (k i : ℝ) * t (f i))

private theorem sum_map_weights_mul_cexp (f : ι → κ) (p : StdSimplex NNReal ι)
    (t : EuclideanSpace ℝ κ) :
    ∑ j, (((p.map f).weights j : NNReal) : ℂ) * Complex.exp (Complex.I * (t j : ℂ)) =
      ∑ i, (p.weights i : ℂ) * Complex.exp (Complex.I * (t (f i) : ℂ)) := by
  classical
  have hweights (j : κ) : (p.map f).weights j = ∑ i with f i = j, p.weights i := by
    rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
      Finset.sum_apply,
      ← Finset.sum_eq_of_subset (s₁ := {i | f i = j}) (by simp) _
        (fun i _ hi ↦ Finsupp.single_eq_of_ne' (by simpa using hi))]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain rfl : f i = j := by simpa using hi
    simp
  simp_rw [hweights]
  push_cast
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ j, ∑ i with f i = j,
        (p.weights i : ℂ) * Complex.exp (Complex.I * (t (f i) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by
      simpa using Finset.sum_fiberwise Finset.univ f
        (fun i ↦ (p.weights i : ℂ) * Complex.exp (Complex.I * (t (f i) : ℂ)))

/-- **Aggregation law for the multinomial distribution.** Combining cells along `f` gives the
multinomial law whose target-cell probabilities are the sums of the source probabilities over
the fibres of `f`. -/
theorem map_multinomialAggregate_multinomialMeasure (f : ι → κ) (n : ℕ)
    (p : StdSimplex NNReal ι) :
    (multinomialMeasure n p).map (multinomialAggregate f) = multinomialMeasure n (p.map f) := by
  apply (measurableEmbedding_multinomialToEuclidean (ι := κ)).map_injective
  let _ := isProbabilityMeasure_multinomialMeasure n p
  let _ := isProbabilityMeasure_multinomialMeasure n (p.map f)
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun (((multinomialMeasure n p).map (multinomialAggregate f)).map
        multinomialToEuclidean) t =
        charFun ((multinomialMeasure n p).map multinomialToEuclidean)
          (pullbackFrequency f t) := by
      rw [charFun_apply, charFun_apply,
        Measure.map_map measurable_multinomialToEuclidean (measurable_multinomialAggregate f),
        integral_map (measurable_multinomialToEuclidean.comp
          (measurable_multinomialAggregate f)).aemeasurable (by fun_prop),
        integral_map measurable_multinomialToEuclidean.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with k
      rw [Function.comp_apply, inner_multinomialAggregate]
    _ = (∑ i, (p.weights i : ℂ) *
          Complex.exp (Complex.I * (t (f i) : ℂ))) ^ n := by
      rw [charFun_multinomial]
      simp only [pullbackFrequency_apply]
    _ = (∑ j, ((p.map f).weights j : ℂ) *
          Complex.exp (Complex.I * (t j : ℂ))) ^ n := by
      rw [sum_map_weights_mul_cexp]
    _ = charFun ((multinomialMeasure n (p.map f)).map multinomialToEuclidean) t :=
      (charFun_multinomial n (p.map f) t).symm

end TauCeti.Probability
