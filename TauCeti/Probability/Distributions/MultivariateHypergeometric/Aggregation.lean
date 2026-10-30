/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Probability.HasLaw

/-!
# Aggregation of multivariate hypergeometric counts

Merging categories in sampling without replacement preserves the multivariate hypergeometric
law. Both the observed counts and the population sizes are summed over the fibres of the
category map, using Mathlib's `FunOnFinite.map`. The map need not be surjective: an empty fibre
has population size and observed count zero. Empty category types and oversize samples are
included as well.

The measure identity and its `HasLaw` corollary permit coarsening a sample's categories before
computing marginal laws. The counting argument uses the fibrewise form of Vandermonde's
identity in `TauCeti.Data.Nat.Choose.Vandermonde`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Merging categories of a multivariate hypergeometric sample sums their population sizes.
This holds for arbitrary category maps, including empty fibres, and at all sample sizes. -/
@[simp]
theorem map_funOnFinite_map_multivariateHypergeometricMeasure (f : ι → κ) (K : ι → ℕ)
    (n : ℕ) :
    (multivariateHypergeometricMeasure K n).map (FunOnFinite.map (M := ℕ) f) =
      multivariateHypergeometricMeasure (FunOnFinite.map f K) n := by
  classical
  have hfiber (v : ι → ℕ) (j : κ) :
      FunOnFinite.map f v j = ∑ i : {i // f i = j}, v i := by
    rw [FunOnFinite.map_apply_apply]
    exact Finset.sum_subtype _ (by simp) v
  have htotal (v : ι → ℕ) : ∑ j, FunOnFinite.map f v j = ∑ i, v i := by
    simp_rw [hfiber]
    exact Fintype.sum_fiberwise f v
  apply Measure.ext_of_singleton
  intro l
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton l),
    multivariateHypergeometricMeasure_def, Measure.finsetSum_apply,
    multivariateHypergeometricMeasure_singleton]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator, Pi.one_apply,
    Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  calc
    _ = (∑ k ∈ (Finset.univ.piAntidiag n).filter
          (fun k ↦ FunOnFinite.map f k = l), ∏ i, ((K i).choose (k i) : ℝ≥0∞)) /
        ((∑ i, K i).choose n : ℝ≥0∞) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [multivariateHypergeometricWeight_def,
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1, div_eq_mul_inv]
    _ = (if ∑ j, l j = n then ∏ j, ((FunOnFinite.map f K j).choose (l j) : ℝ≥0∞)
          else 0) / ((∑ i, K i).choose n : ℝ≥0∞) := by
      congr 1
      simp_rw [funext_iff, hfiber]
      exact_mod_cast Finset.sum_filter_piAntidiag_fiberwise_prod_choose f K l n
    _ = _ := by
      split_ifs with hl
      · rw [multivariateHypergeometricWeight_def, htotal, hl]
      · simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- The category totals of a multivariate hypergeometric random vector have the law with
the corresponding aggregated population sizes. -/
theorem HasLaw.funOnFinite_map_multivariateHypergeometricMeasure {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ι → ℕ}
    {K : ι → ℕ} {n : ℕ} (hX : HasLaw X (multivariateHypergeometricMeasure K n) P)
    (f : ι → κ) :
    HasLaw (fun ω ↦ FunOnFinite.map f (X ω))
      (multivariateHypergeometricMeasure (FunOnFinite.map f K) n) P := by
  rw [← map_funOnFinite_map_multivariateHypergeometricMeasure]
  exact (hasLaw_map (measurable_of_countable (FunOnFinite.map (M := ℕ) f)).aemeasurable).comp hX

end ProbabilityTheory
