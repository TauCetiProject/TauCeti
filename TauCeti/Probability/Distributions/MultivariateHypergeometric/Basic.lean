/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Choose.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The multivariate hypergeometric distribution

A population of `N = ∑ i, K i` objects is split into finitely many categories, category `i`
containing `K i` objects.  Drawing `n` objects uniformly without replacement, the vector `k` of
counts drawn from each category has the multivariate hypergeometric law, with mass

```text
  (∏ i, choose (K i) (k i)) / choose N n
```

at count vectors `k` whose coordinates sum to `n`, and zero mass elsewhere.  Since a count vector
with `k i ≤ K i` for all `i` has total at most `N`, the law is the zero measure when `n > N`.

This file defines the law as a finite weighted sum of Dirac measures on count vectors `ι → ℕ`,
proves its normalization from the multivariate Vandermonde identity, and provides its singleton
masses, exact support, deterministic boundary laws, finite-sum integration formula and parameter
measurability.

## Main definitions and results

* `TauCeti.Probability.multivariateHypergeometricWeight`: the `ℝ≥0∞`-valued mass of a count
  vector.
* `TauCeti.Probability.multivariateHypergeometricMeasure`: the multivariate hypergeometric
  measure on count vectors.
* `TauCeti.Probability.isProbabilityMeasure_multivariateHypergeometricMeasure`: normalization
  when the sample size does not exceed the population size.
* `TauCeti.Probability.multivariateHypergeometricMeasure_singleton`: the exact singleton mass.
* `TauCeti.Probability.multivariateHypergeometricMeasure_singleton_ne_zero_iff`: the exact
  support.
* `TauCeti.Probability.multivariateHypergeometricMeasure_zero_sample` and
  `TauCeti.Probability.multivariateHypergeometricMeasure_full_sample`: the deterministic
  sample-size boundaries.
* `TauCeti.Probability.integral_multivariateHypergeometricMeasure`: integration as a finite
  weighted sum.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

open scoped Classical in
section

/-- The mass assigned to a count vector `k` by category sizes `K`, for the sample size `∑ i, k i`.

The multivariate hypergeometric measure of sample size `n` assigns this mass to the count vectors
of total `n`. -/
def multivariateHypergeometricWeight (K k : ι → ℕ) : ℝ≥0∞ :=
  (∏ i, ((K i).choose (k i) : ℝ≥0∞)) / ((∑ i, K i).choose (∑ i, k i) : ℝ≥0∞)

/-- The defining formula of the multivariate hypergeometric weight. -/
theorem multivariateHypergeometricWeight_def (K k : ι → ℕ) :
    multivariateHypergeometricWeight K k =
      (∏ i, ((K i).choose (k i) : ℝ≥0∞)) / ((∑ i, K i).choose (∑ i, k i) : ℝ≥0∞) := (rfl)

/-- A multivariate hypergeometric weight is nonzero exactly when no category is overdrawn. -/
@[simp]
theorem multivariateHypergeometricWeight_ne_zero_iff (K k : ι → ℕ) :
    multivariateHypergeometricWeight K k ≠ 0 ↔ ∀ i, k i ≤ K i := by
  simp [multivariateHypergeometricWeight, ENNReal.div_eq_zero_iff, Finset.prod_eq_zero_iff,
    Nat.choose_eq_zero_iff, ENNReal.natCast_ne_top]

/-- Every multivariate hypergeometric weight is finite. -/
@[simp]
theorem multivariateHypergeometricWeight_ne_top (K k : ι → ℕ) :
    multivariateHypergeometricWeight K k ≠ ∞ := by
  by_cases hk : ∀ i, k i ≤ K i
  · rw [multivariateHypergeometricWeight]
    refine ENNReal.div_ne_top (ENNReal.prod_ne_top fun _ _ ↦ ENNReal.natCast_ne_top _) ?_
    exact_mod_cast Nat.choose_ne_zero (Finset.sum_le_sum fun i _ ↦ hk i)
  · rw [← multivariateHypergeometricWeight_ne_zero_iff, not_not] at hk
    simp [hk]

/-- The real value of a multivariate hypergeometric weight. -/
@[simp]
theorem multivariateHypergeometricWeight_toReal (K k : ι → ℕ) :
    (multivariateHypergeometricWeight K k).toReal =
      (∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose (∑ i, k i) : ℝ) := by
  simp [multivariateHypergeometricWeight, ENNReal.toReal_div, ENNReal.toReal_prod]

/-- The multivariate hypergeometric weights of the count vectors of total `n` sum to one when
`n` does not exceed the population size. -/
theorem sum_multivariateHypergeometricWeight (K : ι → ℕ) {n : ℕ} (hn : n ≤ ∑ i, K i) :
    ∑ k ∈ Finset.piAntidiag Finset.univ n, multivariateHypergeometricWeight K k = 1 := by
  calc
    _ = ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (∏ i, ((K i).choose (k i) : ℝ≥0∞)) / ((∑ i, K i).choose n : ℝ≥0∞) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [multivariateHypergeometricWeight, (Finset.mem_piAntidiag.mp hk).1]
    _ = ((∑ i, K i).choose n : ℝ≥0∞) / ((∑ i, K i).choose n : ℝ≥0∞) := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ≥0∞) * ((∑ i, K i).choose n : ℝ≥0∞)⁻¹)
        (Finset.sum_piAntidiag_prod_choose Finset.univ K n)
    _ = 1 := ENNReal.div_self (by exact_mod_cast Nat.choose_ne_zero hn) (by simp)

/-- The multivariate hypergeometric distribution with category sizes `K` and sample size `n`.

It is the law of the category counts in a uniform sample of size `n` drawn without replacement
from a population with `K i` objects in category `i`.  It is a probability measure when
`n ≤ ∑ i, K i`, and the zero measure otherwise. -/
def multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) : Measure (ι → ℕ) :=
  ∑ k ∈ Finset.piAntidiag Finset.univ n, multivariateHypergeometricWeight K k • Measure.dirac k

/-- The multivariate hypergeometric measure as its defining finite weighted sum of Dirac
measures. -/
theorem multivariateHypergeometricMeasure_def (K : ι → ℕ) (n : ℕ) :
    multivariateHypergeometricMeasure K n =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        multivariateHypergeometricWeight K k • Measure.dirac k := (rfl)

/-- The multivariate hypergeometric law depends measurably on the category sizes and the sample
size. -/
theorem measurable_multivariateHypergeometricMeasure :
    Measurable fun p : (ι → ℕ) × ℕ ↦ multivariateHypergeometricMeasure p.1 p.2 :=
  Measurable.of_discrete

/-- The singleton mass of a multivariate hypergeometric law is the weight of the count vector
when its total is the sample size, and zero otherwise. -/
@[simp]
theorem multivariateHypergeometricMeasure_singleton (K : ι → ℕ) (n : ℕ) (k : ι → ℕ) :
    multivariateHypergeometricMeasure K n {k} =
      if ∑ i, k i = n then multivariateHypergeometricWeight K k else 0 := by
  simp [multivariateHypergeometricMeasure, Measure.finsetSum_apply, Pi.single_apply, mul_ite,
    Finset.mem_piAntidiag]

/-- The real singleton mass of a multivariate hypergeometric law, in the usual binomial form. -/
theorem multivariateHypergeometricMeasure_real_singleton (K : ι → ℕ) (n : ℕ) (k : ι → ℕ) :
    (multivariateHypergeometricMeasure K n).real {k} =
      if ∑ i, k i = n then
        (∏ i, ((K i).choose (k i) : ℝ)) / ((∑ i, K i).choose n : ℝ)
      else 0 := by
  rw [measureReal_def, multivariateHypergeometricMeasure_singleton]
  split_ifs with hk
  · rw [multivariateHypergeometricWeight_toReal, hk]
  · simp

/-- The singleton mass of a multivariate hypergeometric law is nonzero exactly for the count
vectors of total `n` which overdraw no category. -/
theorem multivariateHypergeometricMeasure_singleton_ne_zero_iff (K : ι → ℕ) (n : ℕ)
    (k : ι → ℕ) :
    multivariateHypergeometricMeasure K n {k} ≠ 0 ↔ ∑ i, k i = n ∧ ∀ i, k i ≤ K i := by
  rw [multivariateHypergeometricMeasure_singleton]
  split_ifs with hk <;> simp [hk]

/-- Drawing more objects than the population contains gives the zero measure. -/
theorem multivariateHypergeometricMeasure_eq_zero_of_lt {K : ι → ℕ} {n : ℕ}
    (hn : ∑ i, K i < n) : multivariateHypergeometricMeasure K n = 0 := by
  apply Measure.ext_of_singleton
  intro k
  by_contra hk
  rw [Measure.coe_zero, Pi.zero_apply, ← ne_eq,
    multivariateHypergeometricMeasure_singleton_ne_zero_iff] at hk
  have hle : ∑ i, k i ≤ ∑ i, K i := Finset.sum_le_sum fun i _ ↦ hk.2 i
  omega

/-- The multivariate hypergeometric law is a probability measure when the sample size does not
exceed the population size. -/
theorem isProbabilityMeasure_multivariateHypergeometricMeasure (K : ι → ℕ) {n : ℕ}
    (hn : n ≤ ∑ i, K i) : IsProbabilityMeasure (multivariateHypergeometricMeasure K n) := by
  rw [isProbabilityMeasure_iff, multivariateHypergeometricMeasure, Measure.finsetSum_apply]
  simpa using sum_multivariateHypergeometricWeight K hn

/-- The multivariate hypergeometric law is a probability measure exactly when the sample size
does not exceed the population size. -/
theorem isProbabilityMeasure_multivariateHypergeometricMeasure_iff (K : ι → ℕ) (n : ℕ) :
    IsProbabilityMeasure (multivariateHypergeometricMeasure K n) ↔ n ≤ ∑ i, K i := by
  refine ⟨fun h ↦ ?_, isProbabilityMeasure_multivariateHypergeometricMeasure K⟩
  by_contra hn
  rw [multivariateHypergeometricMeasure_eq_zero_of_lt (lt_of_not_ge hn)] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure (ι → ℕ)) rfl

/-- A multivariate hypergeometric law is concentrated on count vectors of total `n` which
overdraw no category. -/
theorem ae_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) :
    ∀ᵐ k ∂multivariateHypergeometricMeasure K n, ∑ i, k i = n ∧ ∀ i, k i ≤ K i := by
  rw [ae_iff_of_countable]
  intro k hk
  exact (multivariateHypergeometricMeasure_singleton_ne_zero_iff K n k).mp hk

/-! ## Deterministic boundary laws -/

/-- A valid multivariate hypergeometric law whose support is contained in one count vector is the
Dirac law there. -/
theorem multivariateHypergeometricMeasure_eq_dirac_of_support {K : ι → ℕ} {n : ℕ}
    (hn : n ≤ ∑ i, K i) {l : ι → ℕ} (h : ∀ k : ι → ℕ, ∑ i, k i = n → (∀ i, k i ≤ K i) → k = l) :
    multivariateHypergeometricMeasure K n = Measure.dirac l := by
  let _ := isProbabilityMeasure_multivariateHypergeometricMeasure K hn
  have hae : (fun k : ι → ℕ ↦ k) =ᵐ[multivariateHypergeometricMeasure K n] fun _ ↦ l := by
    filter_upwards [ae_multivariateHypergeometricMeasure K n] with k hk
    exact h k hk.1 hk.2
  simpa using Measure.map_congr hae

/-- Drawing no objects gives the Dirac law at the zero count vector. -/
@[simp]
theorem multivariateHypergeometricMeasure_zero_sample (K : ι → ℕ) :
    multivariateHypergeometricMeasure K 0 = Measure.dirac 0 :=
  multivariateHypergeometricMeasure_eq_dirac_of_support (Nat.zero_le _) fun _ hk _ ↦
    funext fun i ↦ by simpa using (Finset.sum_eq_zero_iff.mp hk) i (Finset.mem_univ i)

/-- Drawing the entire population gives the Dirac law at the vector of category sizes. -/
@[simp]
theorem multivariateHypergeometricMeasure_full_sample (K : ι → ℕ) :
    multivariateHypergeometricMeasure K (∑ i, K i) = Measure.dirac K :=
  multivariateHypergeometricMeasure_eq_dirac_of_support le_rfl fun _ hk hle ↦
    funext fun i ↦ (Finset.sum_eq_sum_iff_of_le fun j _ ↦ hle j).mp hk i (Finset.mem_univ i)

/-! ## Integration -/

/-- Every function is integrable against a multivariate hypergeometric law, since the law has
finite support. -/
theorem integrable_multivariateHypergeometricMeasure {E : Type*} [SeminormedAddGroup E]
    (f : (ι → ℕ) → E) (K : ι → ℕ) (n : ℕ) :
    Integrable f (multivariateHypergeometricMeasure K n) :=
  integrable_finsetSum_measure.mpr fun k _ ↦
    (integrable_dirac (by simp)).smul_measure (multivariateHypergeometricWeight_ne_top K k)

/-- Integration against a multivariate hypergeometric law is the corresponding finite weighted
sum over the count vectors of total `n`. -/
theorem integral_multivariateHypergeometricMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : (ι → ℕ) → E) (K : ι → ℕ) (n : ℕ) :
    ∫ k, f k ∂multivariateHypergeometricMeasure K n =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (multivariateHypergeometricWeight K k).toReal • f k := by
  rw [multivariateHypergeometricMeasure, integral_finsetSum_measure]
  · simp
  · exact fun k _ ↦
      (integrable_dirac (by simp)).smul_measure (multivariateHypergeometricWeight_ne_top K k)

end

end Probability

end TauCeti
