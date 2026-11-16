/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Hypergeometric moments of arbitrary order

The falling-factorial moments of a hypergeometric count have the closed form
`E[(X)ₘ] = (n)ₘ (K)ₘ / (N)ₘ`. Expanding powers in falling factorials gives every natural
raw moment of the real cast law as a finite sum with Stirling-number coefficients.
These formulas include order zero, empty populations and samples, and orders larger than
the population: natural falling factorials and real division give the correct zero terms.

Integrability at every order is supplied by `integrable_hypergeometricMeasure` and
`integrable_map_cast_hypergeometricMeasure`.

The factorial-moment calculation uses `Nat.sum_range_descFactorial_mul_choose_mul_choose`;
the raw-moment expansion uses Mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

/-- Every falling-factorial moment of a valid hypergeometric count.

The quotient is in `ℝ`. If `n < m`, the moment vanishes, including the case `N < m` where
both the numerator and denominator are zero. At order zero its value is one. -/
theorem integral_descFactorial_hypergeometricMeasure {N K n : ℕ}
    (hK : K ≤ N) (hn : n ≤ N) (m : ℕ) :
    ∫ k, (k.descFactorial m : ℝ) ∂hypergeometricMeasure N K n =
      (n.descFactorial m : ℝ) * (K.descFactorial m : ℝ) / (N.descFactorial m : ℝ) := by
  rw [integral_hypergeometricMeasure _ hK]
  simp only [smul_eq_mul]
  by_cases hm : m ≤ n
  · have hsum := Nat.sum_range_descFactorial_mul_choose_mul_choose hm K (N - K)
    rw [Nat.add_sub_of_le hK] at hsum
    have hchoose : (n.descFactorial m : ℝ) * (N.choose n : ℝ) =
        (N.descFactorial m : ℝ) * ((N - m).choose (n - m) : ℝ) := by
      exact_mod_cast Nat.descFactorial_mul_choose hm N
    have hden : (N.choose n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hn
    have hdesc : (N.descFactorial m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr (hm.trans hn)).ne'
    calc
      _ = ((∑ k ∈ Finset.range (n + 1),
          k.descFactorial m * (K.choose k * (N - K).choose (n - k)) : ℕ) : ℝ) /
            (N.choose n : ℝ) := by
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hypergeometricWeight_of_le (Finset.mem_range_succ_iff.mp hk),
          ENNReal.toReal_div, ENNReal.toReal_mul]
        simp only [ENNReal.toReal_natCast]
        ring
      _ = (K.descFactorial m : ℝ) * ((N - m).choose (n - m) : ℝ) /
          (N.choose n : ℝ) := by rw [hsum, Nat.cast_mul]
      _ = _ := by
        field_simp [hden, hdesc]
        linear_combination -(K.descFactorial m : ℝ) * hchoose
  · have hnm : n < m := Nat.lt_of_not_ge hm
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnm]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr
      (lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hk) hnm)]
    simp

/-- Every natural raw moment of the real cast of a valid hypergeometric law, expressed as
a finite sum of its falling-factorial moments with Stirling numbers of the second kind.
All orders are integrable by `integrable_map_cast_hypergeometricMeasure`. -/
theorem integral_pow_map_cast_hypergeometricMeasure {N K n : ℕ}
    (hK : K ≤ N) (hn : n ≤ N) (m : ℕ) :
    ∫ x, x ^ m ∂(hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ) =
      ∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : ℝ) *
        ((n.descFactorial j : ℝ) * (K.descFactorial j : ℝ) /
          (N.descFactorial j : ℝ)) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial,
    Nat.cast_sum, Nat.cast_mul]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_descFactorial_hypergeometricMeasure hK hn]
  · intro j _
    exact (integrable_hypergeometricMeasure _ N K n).const_mul _

end TauCeti.Probability
