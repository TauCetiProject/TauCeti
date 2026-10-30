/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeHypergeometric.Basic
public import TauCeti.Probability.Distributions.Hypergeometric.Symmetry
public import TauCeti.Probability.Cdf
import TauCeti.Data.Nat.Choose.Sum

/-!
# Negative hypergeometric cumulative probabilities

The number of failures before the `r`th success is at most `k` exactly when the first
`k + r` draws contain at least `r` successes. This file proves the corresponding equality
between negative hypergeometric cumulative masses and hypergeometric tails, using the partial
Vandermonde identity in `TauCeti.Data.Nat.Choose.Sum`. Capping the number of draws by the
population size gives an identity at every cutoff, including those beyond the support.

The finite cumulative sum also gives the cdf of the real cast law, with the negative-cutoff
branch handled before taking the natural floor.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {N K r k : ℕ}

/-- The cumulative mass is the finite sum of the explicit negative hypergeometric masses.
The support guard keeps natural subtraction from introducing spurious terms. -/
theorem negativeHypergeometricMeasure_real_Iic_eq_sum (hr : r ≤ K) (hK : K ≤ N) (k : ℕ) :
    (negativeHypergeometricMeasure N K r).real (Iic k) =
      ∑ j ∈ Finset.range (k + 1),
        if j ≤ N - K then
          ((j + r - 1).choose j : ℝ) * ((N - r - j).choose (K - r) : ℝ) /
            (N.choose K : ℝ)
        else 0 := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  have hset : (Iic k : Set ℕ) = (Finset.range (k + 1) : Set ℕ) := by
    ext j
    simp
  rw [hset, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun j _ ↦
    negativeHypergeometricMeasure_real_singleton hr hK j

/-- Once the cutoff includes every possible failure count, the cumulative mass is one.
This includes waiting for zero successes. -/
theorem negativeHypergeometricMeasure_real_Iic_eq_one (hr : r ≤ K) (hK : K ≤ N)
    (hk : N - K ≤ k) :
    (negativeHypergeometricMeasure N K r).real (Iic k) = 1 := by
  rw [measureReal_def, negativeHypergeometricMeasure_eq_sum_dirac hr hK,
    Measure.finsetSum_apply]
  have hsum := sum_negativeHypergeometricWeight hr hK
  convert congrArg ENNReal.toReal hsum using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    simp [hjk]
  · simp

private theorem negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail_of_le
    (hr : 0 < r) (hrK : r ≤ K) (hK : K ≤ N) (hk : k + r ≤ N) :
    (negativeHypergeometricMeasure N K r).real (Iic k) =
      (hypergeometricMeasure N K (k + r)).real (Ici r) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hk
  have htail : (hypergeometricMeasure N K (k + r)).real (Ici r) =
      1 - (hypergeometricMeasure N K (k + r)).real (Iio r) := by
    simpa using
      (probReal_compl_eq_one_sub (μ := hypergeometricMeasure N K (k + r)) measurableSet_Iio)
  have hleft : (negativeHypergeometricMeasure N K r).real (Iic k) =
      (∑ i ∈ Finset.range (k + 1),
        ((i + r - 1).choose i : ℝ) * ((N - r - i).choose (K - r) : ℝ)) /
        (N.choose K : ℝ) := by
    rw [negativeHypergeometricMeasure_real_Iic_eq_sum hrK hK, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    by_cases hiK : i ≤ N - K
    · simp [hiK]
    · have hi : i ≤ k := by simpa using hi
      simp [hiK, Nat.choose_eq_zero_of_lt (by omega : N - r - i < K - r)]
  have hright : (hypergeometricMeasure N K (k + r)).real (Iio r) =
      (∑ j ∈ Finset.range r,
        ((k + r).choose j : ℝ) * ((N - k - r).choose (K - j) : ℝ)) /
        (N.choose K : ℝ) := by
    rw [hypergeometricMeasure_comm N K (k + r)]
    let _ := isProbabilityMeasure_hypergeometricMeasure hk hK
    have hset : (Iio r : Set ℕ) = (Finset.range r : Set ℕ) := by ext j; simp
    rw [hset, ← sum_measureReal_singleton, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjK : j ≤ K := by
      have := Finset.mem_range.mp hj
      omega
    rw [hypergeometricMeasure_real_singleton hk hK, ite_eq_left hjK]
    simp only [Nat.sub_sub]
  have hsum := congrArg (Nat.cast : ℕ → ℝ)
    (Nat.sum_range_choose_mul_choose_add_sum_range_choose_mul_choose hr hrK hk)
  push_cast at hsum
  have hC : (N.choose K : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hK
  rw [htail, hleft, hright]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, hsum, div_self hC]

/-- The probability of at most `k` failures before success `r` is the probability of at least
`r` successes in the first `min N (k + r)` draws. The cap handles cutoffs past the population,
and the identity includes the boundary `r = 0`. -/
theorem negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail
    (hr : r ≤ K) (hK : K ≤ N) (k : ℕ) :
    (negativeHypergeometricMeasure N K r).real (Iic k) =
      (hypergeometricMeasure N K (min N (k + r))).real (Ici r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · let _ := isProbabilityMeasure_hypergeometricMeasure hK (min_le_left N (k + 0))
    simp [negativeHypergeometricMeasure_zero_successes hK]
  · by_cases hk : k + r ≤ N
    · rw [min_eq_right hk]
      exact negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail_of_le hrpos hr hK hk
    · rw [min_eq_left (by omega), hypergeometricMeasure_full_sample hK,
        negativeHypergeometricMeasure_real_Iic_eq_one hr hK (by omega)]
      simp [hr]

/-- At a nonnegative real cutoff, the negative hypergeometric cdf sums its explicit masses
through the natural floor. -/
theorem cdf_map_cast_negativeHypergeometricMeasure (hr : r ≤ K) (hK : K ≤ N)
    {x : ℝ} (hx : 0 ≤ x) :
    cdf ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) x =
      ∑ j ∈ Finset.range (⌊x⌋₊ + 1),
        if j ≤ N - K then
          ((j + r - 1).choose j : ℝ) * ((N - r - j).choose (K - r) : ℝ) /
            (N.choose K : ℝ)
        else 0 := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  rw [Measure.cdf_map_natCast _ hx]
  exact negativeHypergeometricMeasure_real_Iic_eq_sum hr hK _

/-- The real cast negative hypergeometric law has no mass below zero. -/
theorem cdf_map_cast_negativeHypergeometricMeasure_of_neg (hr : r ≤ K) (hK : K ≤ N)
    {x : ℝ} (hx : x < 0) :
    cdf ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- A native natural-valued random variable with a negative hypergeometric law has its
cumulative probabilities given by hypergeometric sampling tails. -/
theorem measureReal_le_of_hasLaw_negativeHypergeometricMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ}
    (hr : r ≤ K) (hK : K ≤ N) (hX : HasLaw X (negativeHypergeometricMeasure N K r) P)
    (k : ℕ) :
    P.real {ω | X ω ≤ k} =
      (hypergeometricMeasure N K (min N (k + r))).real (Ici r) := by
  rw [hX.measureReal_eq (p := fun j ↦ j ≤ k) measurableSet_Iic]
  exact negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail hr hK k

end TauCeti.Probability
