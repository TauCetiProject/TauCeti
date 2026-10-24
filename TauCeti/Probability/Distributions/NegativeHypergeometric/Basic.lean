/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.Data.Nat.Choose.Sum

/-!
# The negative hypergeometric distribution

Draw without replacement from a population of `N` objects, `K` of which are successes, until the
`r`th success appears. The negative hypergeometric law is the law of the number of failures drawn
before that moment. For `r ≤ K ≤ N`, its mass at `k` is

```text
  choose (k + r - 1) k * choose (N - r - k) (K - r) / choose N K     (k ≤ N - K),
```

and it vanishes for `k > N - K`. When `r = 0` no draw is needed, and the law is the Dirac
measure at zero.

This file defines the law as a finite weighted sum of Dirac measures, proves its normalization
from the weighted upper-index Vandermonde convolution
`Nat.sum_range_ascFactorial_mul_choose_mul_choose`, and
provides its mass, support, integration, rising factorial moment, mean and variance APIs.
Outside the parameter range `r ≤ K ≤ N` the measure is zero.

## Main definitions and results

* `TauCeti.Probability.negativeHypergeometricWeight`: the `ℝ≥0∞`-valued mass function.
* `TauCeti.Probability.negativeHypergeometricMeasure`: the totalized negative hypergeometric
  measure on `ℕ`.
* `TauCeti.Probability.isProbabilityMeasure_negativeHypergeometricMeasure`: normalization in the
  valid parameter range.
* `TauCeti.Probability.negativeHypergeometricMeasure_singleton` and
  `TauCeti.Probability.negativeHypergeometricMeasure_singleton_ne_zero_iff`: the singleton masses
  and the exact support.
* `TauCeti.Probability.negativeHypergeometricMeasure_zero_successes`: waiting for no success
  gives the Dirac law at zero.
* `TauCeti.Probability.integral_ascFactorial_negativeHypergeometricMeasure`: the rising factorial
  moments `E[(X + r)⁽ᵐ⁾] = r⁽ᵐ⁾ * C(N + m, K + m) / C(N, K)`.
* `TauCeti.Probability.integral_id_map_cast_negativeHypergeometricMeasure`: the mean
  `r (N - K) / (K + 1)` of the real cast law.
* `TauCeti.Probability.variance_id_map_cast_negativeHypergeometricMeasure`: its variance
  `r (N + 1) (N - K) (K - r + 1) / ((K + 1)² (K + 2))`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {N K r : ℕ}

/-- The mass assigned to `k` failures by the negative hypergeometric parameters `(N, K, r)`:
population size `N`, success count `K`, and number `r` of successes awaited.

The explicit `k ≤ N - K` branch is necessary because natural subtraction is totalized: without
it, the displayed quotient need not vanish when there are fewer than `k` failures. -/
def negativeHypergeometricWeight (N K r k : ℕ) : ℝ≥0∞ :=
  if k ≤ N - K then
    ((k + r - 1).choose k : ℝ≥0∞) * ((N - r - k).choose (K - r) : ℝ≥0∞) / (N.choose K : ℝ≥0∞)
  else 0

/-- The negative hypergeometric weight agrees with its defining ratio when `k ≤ N - K`. -/
@[simp]
theorem negativeHypergeometricWeight_of_le {k : ℕ} (hk : k ≤ N - K) :
    negativeHypergeometricWeight N K r k =
      ((k + r - 1).choose k : ℝ≥0∞) * ((N - r - k).choose (K - r) : ℝ≥0∞) /
        (N.choose K : ℝ≥0∞) := by
  simp [negativeHypergeometricWeight, hk]

/-- The negative hypergeometric weight vanishes when `N - K < k`. -/
@[simp]
theorem negativeHypergeometricWeight_of_not_le {k : ℕ} (hk : ¬ k ≤ N - K) :
    negativeHypergeometricWeight N K r k = 0 := by
  simp [negativeHypergeometricWeight, hk]

/-- Every negative hypergeometric weight is finite when the success count does not exceed the
population size. -/
theorem negativeHypergeometricWeight_ne_top (hK : K ≤ N) (r k : ℕ) :
    negativeHypergeometricWeight N K r k ≠ ∞ := by
  rw [negativeHypergeometricWeight]
  have hC : (N.choose K : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hK
  split_ifs
  · exact ENNReal.div_ne_top (by simp [ENNReal.mul_eq_top]) hC
  · exact ENNReal.zero_ne_top

/-- The real value of a negative hypergeometric weight. -/
theorem negativeHypergeometricWeight_toReal (k : ℕ) :
    (negativeHypergeometricWeight N K r k).toReal =
      if k ≤ N - K then
        ((k + r - 1).choose k : ℝ) * ((N - r - k).choose (K - r) : ℝ) / (N.choose K : ℝ)
      else 0 := by
  rw [negativeHypergeometricWeight]
  split_ifs
  · rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    norm_cast
  · simp

/-- The negative hypergeometric measure with population size `N`, success count `K`, and number
`r` of successes awaited: the law of the number of failures drawn without replacement before the
`r`th success.

It is a probability measure when `r ≤ K ≤ N`, and is the zero measure otherwise. -/
def negativeHypergeometricMeasure (N K r : ℕ) : Measure ℕ :=
  if r ≤ K ∧ K ≤ N then
    ∑ k ∈ Finset.range (N - K + 1), negativeHypergeometricWeight N K r k • Measure.dirac k
  else 0

/-- The negative hypergeometric law depends measurably on its three natural-valued
parameters. -/
theorem measurable_negativeHypergeometricMeasure :
    Measurable fun p : ℕ × ℕ × ℕ ↦ negativeHypergeometricMeasure p.1 p.2.1 p.2.2 :=
  Measurable.of_discrete

/-- Outside the valid parameter range, the negative hypergeometric measure is zero. -/
@[simp]
theorem negativeHypergeometricMeasure_eq_zero_of_invalid (h : ¬ (r ≤ K ∧ K ≤ N)) :
    negativeHypergeometricMeasure N K r = 0 := by
  simp [negativeHypergeometricMeasure, h]

/-- In the valid parameter range, the negative hypergeometric measure is its defining finite
sum. -/
theorem negativeHypergeometricMeasure_eq_sum_dirac (hr : r ≤ K) (hK : K ≤ N) :
    negativeHypergeometricMeasure N K r =
      ∑ k ∈ Finset.range (N - K + 1), negativeHypergeometricWeight N K r k • Measure.dirac k := by
  simp [negativeHypergeometricMeasure, hr, hK]

/-! ## Normalization -/

/-- The negative hypergeometric weights sum to one in the valid parameter range. -/
theorem sum_negativeHypergeometricWeight (hr : r ≤ K) (hK : K ≤ N) :
    ∑ k ∈ Finset.range (N - K + 1), negativeHypergeometricWeight N K r k = 1 := by
  have hsum := Nat.sum_range_ascFactorial_mul_choose_mul_choose hr hK 0
  simp only [Nat.ascFactorial_zero, one_mul, Nat.add_zero] at hsum
  calc _ = ∑ k ∈ Finset.range (N - K + 1),
        ((k + r - 1).choose k : ℝ≥0∞) * ((N - r - k).choose (K - r) : ℝ≥0∞) /
          (N.choose K : ℝ≥0∞) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [negativeHypergeometricWeight_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    _ = (N.choose K : ℝ≥0∞) / (N.choose K : ℝ≥0∞) := by
        rw [← ENNReal.sum_div, ← hsum, Nat.cast_sum]
        simp only [Nat.cast_mul]
    _ = 1 := ENNReal.div_self (by exact_mod_cast Nat.choose_ne_zero hK)
        (ENNReal.natCast_ne_top _)

/-- The negative hypergeometric law is a probability measure in the valid parameter range. -/
theorem isProbabilityMeasure_negativeHypergeometricMeasure (hr : r ≤ K) (hK : K ≤ N) :
    IsProbabilityMeasure (negativeHypergeometricMeasure N K r) := by
  rw [isProbabilityMeasure_iff, negativeHypergeometricMeasure_eq_sum_dirac hr hK]
  simpa [Measure.finsetSum_apply] using sum_negativeHypergeometricWeight hr hK

/-! ## Masses and support -/

/-- The singleton mass of a valid negative hypergeometric law is its defining weight. -/
@[simp]
theorem negativeHypergeometricMeasure_singleton (hr : r ≤ K) (hK : K ≤ N) (k : ℕ) :
    negativeHypergeometricMeasure N K r {k} = negativeHypergeometricWeight N K r k := by
  rw [negativeHypergeometricMeasure_eq_sum_dirac hr hK, Measure.finsetSum_apply]
  by_cases hk : k ≤ N - K
  · rw [Finset.sum_eq_single k]
    · simp
    · simp_all
    · simp_all
  · rw [Finset.sum_eq_zero, negativeHypergeometricWeight_of_not_le hk]
    intro j hj
    have hjk : j ≠ k := by
      have := Finset.mem_range.mp hj
      omega
    simp [hjk]

/-- The real singleton mass of a valid negative hypergeometric law. -/
theorem negativeHypergeometricMeasure_real_singleton (hr : r ≤ K) (hK : K ≤ N) (k : ℕ) :
    (negativeHypergeometricMeasure N K r).real {k} =
      if k ≤ N - K then
        ((k + r - 1).choose k : ℝ) * ((N - r - k).choose (K - r) : ℝ) / (N.choose K : ℝ)
      else 0 := by
  rw [measureReal_def, negativeHypergeometricMeasure_singleton hr hK,
    negativeHypergeometricWeight_toReal]

/-- A valid negative hypergeometric law charges exactly the failure counts `k ≤ N - K`, except
that waiting for no success (`r = 0`) charges only `k = 0`. -/
theorem negativeHypergeometricMeasure_singleton_ne_zero_iff (hr : r ≤ K) (hK : K ≤ N) (k : ℕ) :
    negativeHypergeometricMeasure N K r {k} ≠ 0 ↔ k ≤ N - K ∧ (k = 0 ∨ 0 < r) := by
  rw [negativeHypergeometricMeasure_singleton hr hK]
  by_cases hk : k ≤ N - K
  · rw [negativeHypergeometricWeight_of_le hk]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, Nat.cast_eq_zero,
      Nat.choose_eq_zero_iff, ENNReal.natCast_ne_top, or_false, not_or, not_lt, hk, true_and]
    omega
  · simp [hk]

/-- Waiting for no success gives the Dirac law at zero failures. -/
@[simp]
theorem negativeHypergeometricMeasure_zero_successes (hK : K ≤ N) :
    negativeHypergeometricMeasure N K 0 = Measure.dirac 0 := by
  rw [negativeHypergeometricMeasure_eq_sum_dirac (Nat.zero_le K) hK, Finset.sum_range_succ']
  simp [negativeHypergeometricWeight, Nat.choose_succ_self,
    ENNReal.div_self (by exact_mod_cast Nat.choose_ne_zero hK : (N.choose K : ℝ≥0∞) ≠ 0)]

/-! ## Integration -/

/-- Every function is integrable against a negative hypergeometric measure, since the measure has
finite support. -/
theorem integrable_negativeHypergeometricMeasure {E : Type*} [SeminormedAddGroup E]
    (f : ℕ → E) (N K r : ℕ) : Integrable f (negativeHypergeometricMeasure N K r) := by
  rw [negativeHypergeometricMeasure]
  split_ifs with h
  · exact integrable_finsetSum_measure.mpr fun _ _ ↦
      (integrable_dirac (by simp)).smul_measure (negativeHypergeometricWeight_ne_top h.2 r _)
  · simp

/-- Every function on `ℝ` is integrable against the real-valued cast of a negative
hypergeometric law. -/
@[simp]
theorem integrable_map_cast_negativeHypergeometricMeasure {E : Type*} [SeminormedAddGroup E]
    (f : ℝ → E) (N K r : ℕ) :
    Integrable f ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  exact integrable_negativeHypergeometricMeasure (fun k ↦ f (k : ℝ)) N K r

/-- The real-valued cast of every negative hypergeometric law has all exponential moments. This
includes the invalid parameter range, where the totalized law is the zero measure. -/
@[simp]
theorem integrableExpSet_id_map_cast_negativeHypergeometricMeasure (N K r : ℕ) :
    integrableExpSet id ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) =
      Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_univ, iff_true]
  exact integrable_map_cast_negativeHypergeometricMeasure (fun x : ℝ ↦ Real.exp (t * id x)) N K r

/-- Integration against a valid negative hypergeometric measure is the corresponding finite
weighted sum. -/
theorem integral_negativeHypergeometricMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℕ → E) (hr : r ≤ K) (hK : K ≤ N) :
    ∫ k, f k ∂negativeHypergeometricMeasure N K r =
      ∑ k ∈ Finset.range (N - K + 1), (negativeHypergeometricWeight N K r k).toReal • f k := by
  rw [negativeHypergeometricMeasure_eq_sum_dirac hr hK, integral_finsetSum_measure]
  · simp
  · exact fun _ _ ↦
      (integrable_dirac (by simp)).smul_measure (negativeHypergeometricWeight_ne_top hK r _)

/-! ## Moments -/

/-- **Rising factorial moments of the negative hypergeometric law.** If `X` counts the failures
before the `r`th success, then `X + r` is the number of draws, and
`E[(X + r)⁽ᵐ⁾] = r⁽ᵐ⁾ * C(N + m, K + m) / C(N, K)`, where `n⁽ᵐ⁾ = n.ascFactorial m` is the
rising factorial. -/
theorem integral_ascFactorial_negativeHypergeometricMeasure (hr : r ≤ K) (hK : K ≤ N) (m : ℕ) :
    ∫ k, ((k + r).ascFactorial m : ℝ) ∂negativeHypergeometricMeasure N K r =
      (r.ascFactorial m : ℝ) * ((N + m).choose (K + m) : ℝ) / (N.choose K : ℝ) := by
  have hsum :=
    congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_ascFactorial_mul_choose_mul_choose hr hK m)
  push_cast at hsum
  rw [integral_negativeHypergeometricMeasure _ hr hK, ← hsum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ N - K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [negativeHypergeometricWeight_toReal, hk, ↓reduceIte, smul_eq_mul]
  ring

/-- The first two moments of the number of draws `X + r`, as finite sums. -/
private theorem sum_negativeHypergeometricWeight_toReal_mul (hr : r ≤ K) (hK : K ≤ N)
    (a b c : ℝ) :
    ∑ k ∈ Finset.range (N - K + 1), (negativeHypergeometricWeight N K r k).toReal *
        (a * (((k : ℝ) + r) * ((k : ℝ) + r + 1)) + b * ((k : ℝ) + r) + c) =
      a * ((r : ℝ) * (r + 1) * ((N : ℝ) + 1) * (N + 2) / (((K : ℝ) + 1) * (K + 2))) +
        b * ((r : ℝ) * ((N : ℝ) + 1) / ((K : ℝ) + 1)) + c := by
  have hm : ∀ m, ∑ k ∈ Finset.range (N - K + 1),
      (negativeHypergeometricWeight N K r k).toReal * ((k + r).ascFactorial m : ℝ) =
        (r.ascFactorial m : ℝ) * ((N + m).choose (K + m) : ℝ) / (N.choose K : ℝ) := by
    intro m
    rw [← integral_ascFactorial_negativeHypergeometricMeasure hr hK m,
      integral_negativeHypergeometricMeasure _ hr hK]
    simp only [smul_eq_mul]
  -- Expand the integrand in the rising factorials `(k + r)⁽²⁾`, `(k + r)⁽¹⁾` and `(k + r)⁽⁰⁾`.
  have hexp : ∀ k ∈ Finset.range (N - K + 1),
      (negativeHypergeometricWeight N K r k).toReal *
          (a * (((k : ℝ) + r) * ((k : ℝ) + r + 1)) + b * ((k : ℝ) + r) + c) =
        a * ((negativeHypergeometricWeight N K r k).toReal * ((k + r).ascFactorial 2 : ℝ)) +
          b * ((negativeHypergeometricWeight N K r k).toReal * ((k + r).ascFactorial 1 : ℝ)) +
          c * ((negativeHypergeometricWeight N K r k).toReal * ((k + r).ascFactorial 0 : ℝ)) := by
    intro k _
    simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
    push_cast
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hm 0, hm 1, hm 2]
  -- Express the binomial ratios through `(N + 1) / (K + 1)` and `(N + 2) / (K + 2)`.
  have hC : (N.choose K : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hK
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  have hK2 : (K : ℝ) + 2 ≠ 0 := by positivity
  have hc1 : ((N + 1).choose (K + 1) : ℝ) * ((K : ℝ) + 1) = ((N : ℝ) + 1) * N.choose K := by
    exact_mod_cast (Nat.add_one_mul_choose_eq N K).symm
  have hc2 : ((N + 2).choose (K + 2) : ℝ) * ((K : ℝ) + 2) =
      ((N : ℝ) + 2) * (N + 1).choose (K + 1) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq (N + 1) (K + 1)).symm
  simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.add_zero]
  push_cast
  field_simp
  linear_combination (a * (r : ℝ) * (r + 1) * ((K : ℝ) + 1)) * hc2 +
    (a * (r : ℝ) * (r + 1) * ((N : ℝ) + 2) + b * r * ((K : ℝ) + 2)) * hc1

/-- The mean of the real cast of a valid negative hypergeometric law is `r (N - K) / (K + 1)`. -/
@[simp]
theorem integral_id_map_cast_negativeHypergeometricMeasure (hr : r ≤ K) (hK : K ≤ N) :
    ∫ x, x ∂((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) =
      (r : ℝ) * ((N : ℝ) - K) / ((K : ℝ) + 1) := by
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_negativeHypergeometricMeasure (fun k ↦ (k : ℝ)) hr hK]
  have h := sum_negativeHypergeometricWeight_toReal_mul hr hK 0 1 (-r)
  simp only [smul_eq_mul]
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  calc _ = ∑ k ∈ Finset.range (N - K + 1), (negativeHypergeometricWeight N K r k).toReal *
        (0 * (((k : ℝ) + r) * ((k : ℝ) + r + 1)) + 1 * ((k : ℝ) + r) + -r) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = _ := by
      rw [h]
      field_simp
      ring

/-- The variance of the real cast of a valid negative hypergeometric law is
`r (N + 1) (N - K) (K - r + 1) / ((K + 1)² (K + 2))`. -/
@[simp]
theorem variance_id_map_cast_negativeHypergeometricMeasure (hr : r ≤ K) (hK : K ≤ N) :
    variance id ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) =
      (r : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) - K) * ((K : ℝ) - r + 1) /
        (((K : ℝ) + 1) ^ 2 * ((K : ℝ) + 2)) := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  have hmem : MemLp id 2 ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_map_cast_negativeHypergeometricMeasure (fun x : ℝ ↦ x ^ 2) N K r)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_id_map_cast_negativeHypergeometricMeasure hr hK,
    integral_map (by fun_prop) (by fun_prop),
    integral_negativeHypergeometricMeasure (fun k ↦ (k : ℝ) ^ 2) hr hK]
  -- `k ^ 2 = (k + r) (k + r + 1) - (2 r + 1) (k + r) + r ^ 2`.
  have h := sum_negativeHypergeometricWeight_toReal_mul hr hK 1 (-(2 * r + 1)) ((r : ℝ) ^ 2)
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  have hK2 : (K : ℝ) + 2 ≠ 0 := by positivity
  simp only [smul_eq_mul]
  calc _ = ∑ k ∈ Finset.range (N - K + 1), (negativeHypergeometricWeight N K r k).toReal *
        (1 * (((k : ℝ) + r) * ((k : ℝ) + r + 1)) + -(2 * r + 1) * ((k : ℝ) + r) + (r : ℝ) ^ 2) -
        ((r : ℝ) * ((N : ℝ) - K) / ((K : ℝ) + 1)) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = _ := by
      rw [h]
      field_simp
      ring

end Probability

end TauCeti
