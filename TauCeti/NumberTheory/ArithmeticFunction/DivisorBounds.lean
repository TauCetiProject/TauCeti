/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.TwistedDivisorSum
public import Mathlib.Analysis.PSeries

/-!
# Bounds for twisted divisor sums

The absolute value of a complex twisted divisor sum is bounded by the ordinary divisor
sum. For exponent `e > 1`, exchanging complementary divisors bounds the latter by
`n^e ∑' d, d^(-e)`. In particular, the twisted sums are `O(n^e)`, uniformly in the
characters. These estimates control the Fourier coefficients of character Eisenstein series
of weight at least three. The restriction `e > 1` is essential: the reciprocal series
diverges at exponent one.

For the exponent-one divisor sum, `sigma_one_le_rpow_mul_tsum` instead bounds `σ₁(n)`
by `n^s ∑' d, d^(-s)` for every real `s > 1`. Thus `σ₁(n) = O(n^(1+ε))` for
every `ε > 0`, as needed for the exceptional weight-two Eisenstein series.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.9, Proposition 5.9.1.
-/

public noncomputable section

namespace TauCeti

/-- The norm of a twisted divisor sum is at most the ordinary real divisor sum. -/
theorem norm_twistedDivisorSum_le (e : ℕ) {u v : ℕ}
    (psi : DirichletCharacter ℂ u) (phi : DirichletCharacter ℂ v) (n : ℕ) :
    ‖DirichletCharacter.twistedDivisorSum e psi phi n‖ ≤
      ∑ d ∈ n.divisors, (d : ℝ) ^ e := by
  rw [DirichletCharacter.twistedDivisorSum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  calc
    ‖psi (n / d)‖ * ‖phi d‖ * (d : ℝ) ^ e ≤ 1 * 1 * (d : ℝ) ^ e := by
      gcongr
      · exact DirichletCharacter.norm_le_one _ _
      · exact DirichletCharacter.norm_le_one _ _
    _ = (d : ℝ) ^ e := by ring

/-- For exponent greater than one, a divisor sum is bounded by `n^e` times the convergent
reciprocal-power series. This includes `n = 0`, whose divisor set is empty. -/
theorem sum_divisors_pow_le (e : ℕ) (he : 1 < e) (n : ℕ) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ e ≤
      (n : ℝ) ^ e * ∑' d : ℕ, ((d : ℝ) ^ e)⁻¹ := by
  have hnonneg : ∀ d : ℕ, 0 ≤ ((d : ℝ) ^ e)⁻¹ := fun d ↦ by positivity
  have hsum := Real.summable_nat_pow_inv.mpr he
  have hflip : (∑ d ∈ n.divisors, (d : ℝ) ^ e) =
      ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ e := by
    exact (Nat.sum_divisorsAntidiagonal' (fun _ d ↦ (d : ℝ) ^ e)).symm.trans
      (Nat.sum_divisorsAntidiagonal (fun _ d ↦ (d : ℝ) ^ e))
  rw [hflip]
  calc
    (∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ e) =
        ∑ d ∈ n.divisors, (n : ℝ) ^ e * ((d : ℝ) ^ e)⁻¹ := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd), div_pow, div_eq_mul_inv]
      exact hd0
    _ = (n : ℝ) ^ e * ∑ d ∈ n.divisors, ((d : ℝ) ^ e)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ e * ∑' d : ℕ, ((d : ℝ) ^ e)⁻¹ := by
      gcongr
      exact hsum.sum_le_tsum n.divisors (fun d _ ↦ hnonneg d)

/-- The exponent-one divisor sum is bounded by `n^s` times a convergent reciprocal-power
series for every `s > 1`. This includes `n = 0`, where the divisor sum is zero. -/
theorem sigma_one_le_rpow_mul_tsum {s : ℝ} (hs : 1 < s) (n : ℕ) :
    (ArithmeticFunction.sigma 1 n : ℝ) ≤
      (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
  have hsum := Real.summable_nat_rpow_inv.mpr hs
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum]
  calc
    (∑ d ∈ n.divisors, (((n / d) ^ 1 : ℕ) : ℝ)) ≤
        ∑ d ∈ n.divisors, (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
      refine Finset.sum_le_sum fun d hd ↦ ?_
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      have hq : 1 ≤ ((n / d : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      calc
        _ = ((n / d : ℕ) : ℝ) ^ (1 : ℝ) := by simp
        _ ≤ ((n / d : ℕ) : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hq hs.le
        _ = (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
          rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0,
            Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg d), div_eq_mul_inv]
    _ = (n : ℝ) ^ s * ∑ d ∈ n.divisors, ((d : ℝ) ^ s)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
      gcongr
      exact hsum.sum_le_tsum n.divisors (fun d _ ↦ by positivity)

end TauCeti
