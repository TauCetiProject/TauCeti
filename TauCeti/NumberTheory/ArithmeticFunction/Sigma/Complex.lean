/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.Divisors

/-!
# Complex divisor sums

The finite divisor sum `∑ d ∈ n.divisors, (d : ℂ) ^ w` is entire in its complex exponent.
Exchanging complementary divisors gives its reflection in the exponent. Both statements include
`n = 0`, whose native divisor set is empty.

These are the coefficient properties used by the Fourier expansion and functional equation of
the level-one nonholomorphic Eisenstein series. They use the native finite sum directly.

## References

* Alex Kontorovich, Terence Tao and contributors,
  [Prime Number Theorem and More][PNTComplexDivisors], `IwaniecKowalskiCh1.lean`,
  `ArithmeticFunction.sigmaR` and `ArithmeticFunction.sigmaR_apply`, for the complex divisor sum.

[PNTComplexDivisors]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

namespace Complex

/-- The complex divisor sum is entire as a function of its exponent, including at index zero. -/
@[fun_prop]
theorem differentiable_sum_divisors_cpow (n : ℕ) :
    Differentiable ℂ (fun w : ℂ ↦ ∑ d ∈ n.divisors, (d : ℂ) ^ w) := by
  intro w
  refine DifferentiableAt.fun_sum fun d hd ↦ ?_
  exact differentiableAt_id.const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr ((Nat.pos_of_mem_divisors hd).ne')))

/-- Reflection of the exponent in a complex divisor sum, including the empty sum at zero. -/
theorem sum_divisors_cpow_neg (n : ℕ) (w : ℂ) :
    (∑ d ∈ n.divisors, (d : ℂ) ^ (-w)) =
      (n : ℂ) ^ (-w) * ∑ d ∈ n.divisors, (d : ℂ) ^ w := by
  rw [← Nat.sum_div_divisors (f := fun d : ℕ ↦ (d : ℂ) ^ (-w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ((Nat.pos_of_mem_divisors hd).ne')
  have hp : (d : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hd0)
  have H := natCast_mul_natCast_cpow d (n / d) (-w)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at H
  rw [H, cpow_neg (d : ℂ) w]
  field_simp

end Complex
