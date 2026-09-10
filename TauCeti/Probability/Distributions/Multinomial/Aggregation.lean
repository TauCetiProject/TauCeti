/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Transforms
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Aggregation of multinomial cells

Combining cells of a multinomial count vector again gives a multinomial distribution. For a map
`f : ι → κ`, the count in a target cell `j` is the sum of all source counts over the fibre of
`j`, which is Mathlib's `FunOnFinite.map f`, while `Convexity.StdSimplex.map f` sums the
corresponding cell probabilities.

This aggregation law supports coarsening a multinomial model by merging categories while
preserving its multinomial form.

## Main results

* `TauCeti.Probability.map_funOnFinite_map_multinomialMeasure`: aggregation sends a
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

omit [Fintype ι] [Fintype κ] in
/-- Aggregating count vectors is measurable for the discrete measurable structures. -/
theorem measurable_funOnFinite_map [Finite ι] [Finite κ] (f : ι → κ) :
    Measurable (FunOnFinite.map (M := ℕ) f) :=
  measurable_of_countable _

/-- Pull a Euclidean frequency vector back along a map of cells. -/
private def pullbackFrequency (f : ι → κ) (t : EuclideanSpace ℝ κ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i ↦ t (f i)

omit [Fintype ι] [Fintype κ] in
@[simp]
private theorem pullbackFrequency_apply (f : ι → κ) (t : EuclideanSpace ℝ κ) (i : ι) :
    pullbackFrequency f t i = t (f i) := (rfl)

private theorem inner_multinomialToEuclidean_funOnFinite_map (f : ι → κ) (k : ι → ℕ)
    (t : EuclideanSpace ℝ κ) :
    inner ℝ (multinomialToEuclidean (FunOnFinite.map f k)) t =
      inner ℝ (multinomialToEuclidean k) (pullbackFrequency f t) := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    multinomialToEuclidean_apply, FunOnFinite.map_apply_apply, pullbackFrequency_apply]
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
  rw [StdSimplex.weights_map]
  calc
    _ = (p.weights.mapDomain f).sum fun j x ↦
        (x : ℂ) * Complex.exp (Complex.I * (t j : ℂ)) := by
      rw [Finsupp.sum_fintype]
      simp
    _ = p.weights.sum fun i x ↦
        (x : ℂ) * Complex.exp (Complex.I * (t (f i) : ℂ)) := by
      apply Finsupp.sum_mapDomain_index
      · simp
      · intro j x y
        push_cast
        ring
    _ = _ := by
      rw [Finsupp.sum_fintype]
      simp

/-- **Aggregation law for the multinomial distribution.** Combining cells along `f` gives the
multinomial law whose target-cell probabilities are the sums of the source probabilities over
the fibres of `f`. -/
theorem map_funOnFinite_map_multinomialMeasure (f : ι → κ) (n : ℕ)
    (p : StdSimplex NNReal ι) :
    (multinomialMeasure n p).map (FunOnFinite.map (M := ℕ) f) =
      multinomialMeasure n (p.map f) := by
  apply (measurableEmbedding_multinomialToEuclidean (ι := κ)).map_injective
  let _ := isProbabilityMeasure_multinomialMeasure n p
  let _ := isProbabilityMeasure_multinomialMeasure n (p.map f)
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun (((multinomialMeasure n p).map (FunOnFinite.map (M := ℕ) f)).map
        multinomialToEuclidean) t =
        charFun ((multinomialMeasure n p).map multinomialToEuclidean)
          (pullbackFrequency f t) := by
      rw [charFun_apply, charFun_apply,
        Measure.map_map measurable_multinomialToEuclidean (measurable_funOnFinite_map f),
        integral_map (measurable_multinomialToEuclidean.comp
          (measurable_funOnFinite_map f)).aemeasurable (by fun_prop),
        integral_map measurable_multinomialToEuclidean.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with k
      rw [Function.comp_apply, inner_multinomialToEuclidean_funOnFinite_map]
    _ = (∑ i, (p.weights i : ℂ) *
          Complex.exp (Complex.I * (t (f i) : ℂ))) ^ n := by
      rw [charFun_map_multinomialToEuclidean_multinomialMeasure]
      simp only [pullbackFrequency_apply]
    _ = (∑ j, ((p.map f).weights j : ℂ) *
          Complex.exp (Complex.I * (t j : ℂ))) ^ n := by
      rw [sum_map_weights_mul_cexp]
    _ = charFun ((multinomialMeasure n (p.map f)).map multinomialToEuclidean) t :=
      (charFun_map_multinomialToEuclidean_multinomialMeasure n (p.map f) t).symm

end TauCeti.Probability
