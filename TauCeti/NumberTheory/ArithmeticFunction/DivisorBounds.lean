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

More generally, `sigma_le_rpow_mul_tsum` bounds `σₖ(n)` by `n^s ∑' d, d^(-s)`
when `k ≤ s` and `s > 1`. In particular, it bounds `σ₁(n)`
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

/-- For `k ≤ s` and `s > 1`, the divisor sum `σₖ(n)` is bounded by `n^s` times the
convergent reciprocal-power series. This includes `n = 0`, where the divisor sum is zero. -/
theorem sigma_le_rpow_mul_tsum (k : ℕ) {s : ℝ} (hk : (k : ℝ) ≤ s) (hs : 1 < s)
    (n : ℕ) :
    (ArithmeticFunction.sigma k n : ℝ) ≤
      (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
  have hsum := Real.summable_nat_rpow_inv.mpr hs
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum]
  calc
    (∑ d ∈ n.divisors, (((n / d) ^ k : ℕ) : ℝ)) ≤
        ∑ d ∈ n.divisors, (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
      refine Finset.sum_le_sum fun d hd ↦ ?_
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      have hq : 1 ≤ ((n / d : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      calc
        _ = ((n / d : ℕ) : ℝ) ^ (k : ℝ) := by
          rw [Nat.cast_pow, Real.rpow_natCast]
        _ ≤ ((n / d : ℕ) : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hq hk
        _ = (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
          rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0,
            Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg d), div_eq_mul_inv]
    _ = (n : ℝ) ^ s * ∑ d ∈ n.divisors, ((d : ℝ) ^ s)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
      gcongr
      exact hsum.sum_le_tsum n.divisors (fun d _ ↦ by positivity)

/-- For exponent greater than one, a divisor sum is bounded by `n^e` times the convergent
reciprocal-power series. This includes `n = 0`, whose divisor set is empty. -/
theorem sum_divisors_pow_le (e : ℕ) (he : 1 < e) (n : ℕ) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ e ≤
      (n : ℝ) ^ e * ∑' d : ℕ, ((d : ℝ) ^ e)⁻¹ := by
  simpa only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow,
    Real.rpow_natCast] using sigma_le_rpow_mul_tsum e le_rfl (by exact_mod_cast he) n

end TauCeti
