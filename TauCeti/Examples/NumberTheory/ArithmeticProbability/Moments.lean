/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticProbability.Moments

/-!
# Examples of divisibility probabilities and prime-sum moments

All examples use the uniform probability measure on `{1, …, N}`.

* For `N = 5`, the probability that `2` divides the sample is `2 / 5`, with signed error
  `-1 / 10` against `1 / 2`; a divisor `7 > N` has probability `0`.
* For `N = 12`, the probability that both `4` and `6` divide the sample is `1 / 12`, through
  `lcm 4 6 = 12`, not `⌊12 / 24⌋ / 12 = 0`. For `N = 5`, the probability that both `2` and `3`
  divide the sample is `0`, while the product of the marginal probabilities is `2 / 25`.
* For `N = 5` the centered product of the divisibility indicators of `2` and `3` averages to
  `-1 / 15`, not to the model value `0`. The centered square of the indicator of `2` averages to
  exactly `1 / 4` for every `N`.
* Take `P = {2, 3}` and `a p = p`, so the model mean is `A = 2` and the model variance is `V = 3`.
  For `N = 5` the values on `1, …, 5` are `0, 2, 3, 2, 0`, with mean `7 / 5` and second moment
  `9 / 5` about `A`. For the complete period `N = 6` the mean is `2` and the second moment is `3`.
-/

open MeasureTheory TauCeti.Probability ArithmeticFunction

-- For `N = 5`, the probability that `2` divides the sample is `⌊5 / 2⌋ / 5 = 2 / 5`.
example : (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 2 ∣ n} = 2 / 5 := by
  rw [empiricalMeasure_add_one_real_dvd]
  norm_num

-- Its signed error against the model value `1 / 2` is `-1 / 10`.
example : (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 2 ∣ n} - ((2 : ℕ) : ℝ)⁻¹ =
    -1 / 10 := by
  rw [empiricalMeasure_add_one_real_dvd_sub_inv]
  norm_num

-- A divisor larger than `N` divides no sample point.
example : (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 7 ∣ n} = 0 := by
  rw [empiricalMeasure_add_one_real_dvd]
  norm_num

-- Joint divisibility goes through the `lcm`: for `N = 12`, `4` and `6` both divide only `12`.
example : (empiricalMeasure (· + 1) 11 : Measure ℕ).real {n | 4 ∣ n ∧ 6 ∣ n} = 1 / 12 := by
  rw [empiricalMeasure_add_one_real_dvd_and_dvd]
  norm_num

-- For `N = 5` no sample point is divisible by both `2` and `3`, so the events are dependent:
-- the product of their probabilities is `2 / 5 * 1 / 5 = 2 / 25`.
example : (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 2 ∣ n ∧ 3 ∣ n} = 0 ∧
    (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 2 ∣ n} *
      (empiricalMeasure (· + 1) 4 : Measure ℕ).real {n | 3 ∣ n} = 2 / 25 := by
  rw [empiricalMeasure_add_one_real_dvd_and_dvd_of_coprime (by norm_num),
    empiricalMeasure_add_one_real_dvd, empiricalMeasure_add_one_real_dvd]
  norm_num

-- For `N = 5` the centered divisibility indicators of `2` and `3` have average product
-- `-1 / 15`, although the model value for distinct primes is `0`.
example : ∫ n, ((if 2 ∣ n then 1 else 0) - ((2 : ℕ) : ℝ)⁻¹) *
      ((if 3 ∣ n then 1 else 0) - ((3 : ℕ) : ℝ)⁻¹)
    ∂(empiricalMeasure (· + 1) 4 : Measure ℕ) = -1 / 15 := by
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul]
  norm_num

-- The centered square of the indicator of `2` is `1 / 4` pointwise, so its average is exactly the
-- model value `1 / 2 - 1 / 4` for every `N`.
example (m : ℕ) : ∫ n, ((if 2 ∣ n then 1 else 0) - ((2 : ℕ) : ℝ)⁻¹) *
      ((if 2 ∣ n then 1 else 0) - ((2 : ℕ) : ℝ)⁻¹)
    ∂(empiricalMeasure (· + 1) m : Measure ℕ) = 1 / 4 := by
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul, Nat.lcm_self]
  have hm : (m + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  ring

-- For `N = 5`, `P = {2, 3}` and `a p = p`, the mean of the weighted sum is `7 / 5`, not the
-- model mean `2`.
example : ∫ n, primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) n
    ∂(empiricalMeasure (· + 1) 4 : Measure ℕ) = 7 / 5 := by
  rw [integral_primeDivisibilitySum_empiricalMeasure_add_one]
  norm_num

-- For `N = 5` the second moment about the model mean `2` is `9 / 5`, not the model variance `3`.
example : ∫ n, (primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) n -
      ∑ p ∈ ({2, 3} : Finset ℕ), (p : ℝ) / p) ^ 2
    ∂(empiricalMeasure (· + 1) 4 : Measure ℕ) = 9 / 5 := by
  rw [integral_empiricalMeasure_add_one]
  simp [Finset.sum_range_succ, primeDivisibilitySum_apply, Finset.filter_insert,
    Finset.filter_singleton]
  norm_num

-- Over the complete period `N = 6` the mean is the model mean `2` ...
example : ∫ n, primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) n
    ∂(empiricalMeasure (· + 1) 5 : Measure ℕ) = 2 := by
  rw [integral_primeDivisibilitySum_empiricalMeasure_add_one_of_dvd (by decide)]
  norm_num

-- ... and the second moment about it is the model variance `2 ^ 2 / 4 + 3 ^ 2 * 2 / 9 = 3`.
example : ∫ n, (primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) n -
      ∑ p ∈ ({2, 3} : Finset ℕ), (p : ℝ) / p) ^ 2
    ∂(empiricalMeasure (· + 1) 5 : Measure ℕ) = 3 := by
  rw [integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_of_dvd (by decide)
    (by decide)]
  norm_num
