/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Complex divisor sums

The finite divisor sum `∑ d ∈ n.divisors, (d : ℂ) ^ w` is entire in its complex exponent.
Exchanging complementary divisors gives its reflection in the exponent. Both statements include
`n = 0`, whose native divisor set is empty.

These are the coefficient properties used by the Fourier expansion and functional equation of
the level-one nonholomorphic Eisenstein series. They use the native finite sum directly.

The same sum, packaged as an arithmetic function, is the divisor power sum
`ArithmeticFunction.sigmaC ν n = ∑_{d ∣ n} d ^ ν`. It is the Dirichlet convolution of `ζ` with
the power function `ArithmeticFunction.cpow ν : n ↦ n ^ ν`, hence multiplicative, and it agrees
with Mathlib's `ArithmeticFunction.sigma k` at natural exponents.

## Main definitions

* `ArithmeticFunction.cpow ν`: the arithmetic function `n ↦ n ^ ν`, with value `0` at `0`.
* `ArithmeticFunction.sigmaC ν`: the divisor power sum `n ↦ ∑_{d ∣ n} d ^ ν`.

## Main results

* `ArithmeticFunction.sigmaC_natCast`: `σ_k` is the cast of `ArithmeticFunction.sigma k`.
* `ArithmeticFunction.sigmaC_eq_zeta_mul_cpow`: `σ_ν = ζ * (n ↦ n ^ ν)`.
* `ArithmeticFunction.isMultiplicative_sigmaC` and `ArithmeticFunction.sigmaC_apply_prime_pow`:
  `σ_ν` is multiplicative, with `σ_ν(p ^ a) = ∑_{j ≤ a} (p ^ ν) ^ j`.
* `ArithmeticFunction.sigmaC_eq_cpow_mul_sigmaC_neg`: the reflection `σ_ν(n) = n ^ ν σ_{-ν}(n)`.

## References

* Alex Kontorovich, Terence Tao and contributors,
  [Prime Number Theorem and More][PNTComplexDivisors], `IwaniecKowalskiCh1.lean`,
  `ArithmeticFunction.sigmaR` and `ArithmeticFunction.sigmaR_apply`, for the complex divisor sum,
  and `ArithmeticFunction.powR`, `ArithmeticFunction.sigmaR_eq_zeta_mul_powR` and
  `ArithmeticFunction.isMultiplicative_sigmaR`, for its convolution structure.

[PNTComplexDivisors]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

namespace Nat

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
  have hp : (d : ℂ) ^ w ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have H := Complex.natCast_mul_natCast_cpow d (n / d) (-w)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at H
  rw [H, Complex.cpow_neg (d : ℂ) w]
  field_simp

end Nat

namespace ArithmeticFunction

open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

/-- The arithmetic function `n ↦ n ^ ν` with complex exponent `ν`, with value `0` at `0`. -/
@[expose] noncomputable def cpow (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by simp⟩

/-- Away from `0`, `cpow ν n` is the complex power `n ^ ν`. -/
@[simp]
theorem cpow_apply (ν : ℂ) {n : ℕ} (hn : n ≠ 0) : cpow ν n = (n : ℂ) ^ ν := by
  simp [cpow, hn]

/-- The power function `n ↦ n ^ ν` is multiplicative. -/
theorem isMultiplicative_cpow (ν : ℂ) : IsMultiplicative (cpow ν) := by
  refine ⟨by simp, fun {m n} _ ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, Complex.natCast_mul_natCast_cpow]

/-- The divisor power sum `σ_ν(n) = ∑_{d ∣ n} d ^ ν` with complex exponent `ν`. Its value at `0`
is the empty sum `0`. -/
@[expose] noncomputable def sigmaC (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ ∑ d ∈ n.divisors, (d : ℂ) ^ ν, by simp⟩

/-- `σ_ν(n)` is the sum of `d ^ ν` over the divisors `d` of `n`. -/
@[simp]
theorem sigmaC_apply (ν : ℂ) (n : ℕ) : sigmaC ν n = ∑ d ∈ n.divisors, (d : ℂ) ^ ν :=
  rfl

/-- At a natural exponent `k`, `σ_k` is the cast of Mathlib's `ArithmeticFunction.sigma k`. -/
theorem sigmaC_natCast (k : ℕ) : sigmaC k = (σ k : ArithmeticFunction ℂ) := by
  ext n
  simp [sigma_apply]

/-- `σ_ν` is the Dirichlet convolution of `ζ` with `n ↦ n ^ ν`. -/
theorem sigmaC_eq_zeta_mul_cpow (ν : ℂ) : sigmaC ν = (ζ : ArithmeticFunction ℂ) * cpow ν := by
  ext n
  rw [coe_zeta_mul_apply, sigmaC_apply]
  exact Finset.sum_congr rfl fun d hd ↦ (cpow_apply ν (Nat.pos_of_mem_divisors hd).ne').symm

/-- The divisor power sum `σ_ν` is multiplicative. -/
theorem isMultiplicative_sigmaC (ν : ℂ) : IsMultiplicative (sigmaC ν) :=
  sigmaC_eq_zeta_mul_cpow ν ▸ isMultiplicative_zeta.natCast.mul (isMultiplicative_cpow ν)

/-- The value of `σ_ν` at a prime power: `σ_ν(p ^ a) = ∑_{j ≤ a} p ^ {jν}`. -/
theorem sigmaC_apply_prime_pow (ν : ℂ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigmaC ν (p ^ a) = ∑ j ∈ Finset.range (a + 1), ((p : ℂ) ^ ν) ^ j := by
  simp [Nat.divisors_prime_pow hp, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Reflection of the exponent: `σ_ν(n) = n ^ ν σ_{-ν}(n)`, including at `n = 0`. -/
theorem sigmaC_eq_cpow_mul_sigmaC_neg (ν : ℂ) (n : ℕ) :
    sigmaC ν n = (n : ℂ) ^ ν * sigmaC (-ν) n := by
  simpa using Nat.sum_divisors_cpow_neg n (-ν)

end ArithmeticFunction
