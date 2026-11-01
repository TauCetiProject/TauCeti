/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Marginal
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.Probability.HasLaw

/-!
# Aggregation of the multivariate hypergeometric distribution

Merging categories of a population along a map `f : ι → κ` turns a multivariate hypergeometric
sample into a multivariate hypergeometric sample from the merged population: the merged category
`j` contains the `∑ i with f i = j, K i` objects of the categories in the fibre of `f` over `j`,
and the merged count vector is Mathlib's `FunOnFinite.map f`.  At the level of masses this is the
grouped Vandermonde identity `Finset.sum_filter_piAntidiag_prod_choose_fiberwise`.

Merging a set `s` of categories against all the others shows that the total number of objects
drawn from `s` is hypergeometric.  These group totals determine the covariances of the counts.

## Main results

* `TauCeti.Probability.map_funOnFinite_map_multivariateHypergeometricMeasure`: aggregation of
  categories along a map.
* `TauCeti.Probability.map_sum_multivariateHypergeometricMeasure`: the total count drawn from a
  set of categories is hypergeometric.
* `ProbabilityTheory.HasLaw.funOnFinite_map_multivariateHypergeometricMeasure`: aggregation of
  the count vector of a random sample.

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

/-- **Aggregation law for the multivariate hypergeometric distribution.** Merging categories
along `f` gives the multivariate hypergeometric law of the merged population, whose category
sizes are the totals of the original sizes over the fibres of `f`. -/
@[simp]
theorem map_funOnFinite_map_multivariateHypergeometricMeasure (f : ι → κ) (K : ι → ℕ)
    (n : ℕ) :
    (multivariateHypergeometricMeasure K n).map (FunOnFinite.map (M := ℕ) f) =
      multivariateHypergeometricMeasure (FunOnFinite.map f K) n := by
  classical
  have hsum (k : ι → ℕ) : ∑ j, FunOnFinite.map f k j = ∑ i, k i := by
    simpa only [FunOnFinite.map_apply_apply] using Finset.sum_fiberwise Finset.univ f k
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply (FunOnFinite.continuous_map ℕ f).measurable (MeasurableSet.singleton m),
    multivariateHypergeometricMeasure_def, Measure.finsetSum_apply,
    multivariateHypergeometricMeasure_singleton]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator, Pi.one_apply,
    Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  split_ifs with hm
  · subst hm
    calc
      _ = ∑ k ∈ Finset.piAntidiag Finset.univ (∑ j, m j) with
            ∀ j, ∑ i with f i = j, k i = m j,
          (∏ i, ((K i).choose (k i) : ℝ≥0∞)) * ((∑ i, K i).choose (∑ j, m j) : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun k hk ↦ ?_
        · simp [funext_iff, FunOnFinite.map_apply_apply]
        · rw [multivariateHypergeometricWeight_def, div_eq_mul_inv,
            (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1]
      _ = (∏ j, ((∑ i with f i = j, K i).choose (m j) : ℝ≥0∞)) *
          ((∑ i, K i).choose (∑ j, m j) : ℝ≥0∞)⁻¹ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Finset.sum_filter_piAntidiag_prod_choose_fiberwise f K m
      _ = _ := by
        rw [multivariateHypergeometricWeight_def, hsum K, div_eq_mul_inv]
        simp only [FunOnFinite.map_apply_apply]
  · -- Merging preserves the total count, so no count vector of total `n` merges to `m`.
    refine Finset.sum_eq_zero fun k hk ↦ absurd ?_ hm
    obtain ⟨hkn, rfl⟩ := Finset.mem_filter.mp hk
    rw [hsum, (Finset.mem_piAntidiag.mp hkn).1]

/-- The total number of objects drawn from a set `s` of categories of a multivariate
hypergeometric sample is hypergeometric: the population size is the total of the category sizes,
and the marked objects are those of the categories in `s`. -/
theorem map_sum_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) (s : Finset ι) :
    (multivariateHypergeometricMeasure K n).map (fun k ↦ ∑ i ∈ s, k i) =
      hypergeometricMeasure (∑ i, K i) (∑ i ∈ s, K i) n := by
  classical
  -- Merge the categories in `s` into `true` and all others into `false`.
  let g : ι → Bool := fun i ↦ decide (i ∈ s)
  have hg (k : ι → ℕ) : FunOnFinite.map g k true = ∑ i ∈ s, k i := by
    simp [g, FunOnFinite.map_apply_apply]
  have htotal : ∑ b, FunOnFinite.map g K b = ∑ i, K i := by
    simpa only [FunOnFinite.map_apply_apply] using Finset.sum_fiberwise Finset.univ g K
  calc
    _ = ((multivariateHypergeometricMeasure K n).map (FunOnFinite.map (M := ℕ) g)).map
        (fun k ↦ k true) := by
      rw [Measure.map_map (measurable_pi_apply true) (FunOnFinite.continuous_map ℕ g).measurable]
      exact congrArg (Measure.map · _) (funext fun k ↦ (hg k).symm)
    _ = _ := by
      rw [map_funOnFinite_map_multivariateHypergeometricMeasure,
        map_eval_multivariateHypergeometricMeasure, htotal, hg]

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
