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
`TauCeti.ArithmeticFunction.sigmaC ν n = ∑_{d ∣ n} d ^ ν`. It is the Dirichlet convolution of
`ζ` with the power function `TauCeti.ArithmeticFunction.cpow ν : n ↦ n ^ ν`, hence
multiplicative, and it agrees with Mathlib's `ArithmeticFunction.sigma k` at natural exponents.

## Main definitions

* `TauCeti.ArithmeticFunction.cpow ν`: the arithmetic function `n ↦ n ^ ν`, with value `0` at
  `0`.
* `TauCeti.ArithmeticFunction.sigmaC ν`: the divisor power sum `n ↦ ∑_{d ∣ n} d ^ ν`.

## Main results

* `TauCeti.ArithmeticFunction.cpow_apply_mul`: `n ↦ n ^ ν` is completely multiplicative.
* `TauCeti.ArithmeticFunction.sigmaC_natCast`: `σ_k` is the cast of
  `ArithmeticFunction.sigma k`.
* `TauCeti.ArithmeticFunction.sigmaC_eq_zeta_mul_cpow`: `σ_ν = ζ * (n ↦ n ^ ν)`.
* `TauCeti.ArithmeticFunction.isMultiplicative_sigmaC` and
  `TauCeti.ArithmeticFunction.sigmaC_apply_prime_pow`: `σ_ν` is multiplicative, with
  `σ_ν(p ^ a) = ∑_{j ≤ a} (p ^ ν) ^ j`.
* `TauCeti.ArithmeticFunction.sigmaC_eq_cpow_pmul_sigmaC_neg`: the reflection
  `σ_ν(n) = n ^ ν σ_{-ν}(n)`.
* `TauCeti.ArithmeticFunction.norm_sigmaC_le`: `‖σ_ν(n)‖ ≤ τ(n) n ^ max(Re ν, 0)`.

## References

* Alex Kontorovich, Terence Tao and contributors,
  [Prime Number Theorem and More][PNTComplexDivisors], `IwaniecKowalskiCh1.lean`,
  `ArithmeticFunction.sigmaR` and `ArithmeticFunction.sigmaR_apply`, for the complex divisor sum,
  and `ArithmeticFunction.powR`, `ArithmeticFunction.sigmaR_eq_zeta_mul_powR` and
  `ArithmeticFunction.isMultiplicative_sigmaR`, for its convolution structure; and, at
  [revision 301f8be][PNTComplexDivisorsBound], `ArithmeticFunction.ramanujan_norm_sigmaR_le`, for
  the norm bound.

[PNTComplexDivisors]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
[PNTComplexDivisorsBound]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/301f8be/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
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
  have H := Complex.natCast_mul_cpow d ((n / d : ℕ) : ℂ) (-w)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at H
  rw [H, Complex.cpow_neg (d : ℂ) w]
  field_simp

end Nat

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace TauCeti.ArithmeticFunction

/-- The arithmetic function `n ↦ n ^ ν` with complex exponent `ν`, with value `0` at `0`. -/
noncomputable def cpow (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by simp⟩

/-- Away from `0`, `cpow ν n` is the complex power `n ^ ν`. -/
@[simp]
theorem cpow_apply (ν : ℂ) {n : ℕ} (hn : n ≠ 0) : cpow ν n = (n : ℂ) ^ ν := by
  simp [cpow, hn]

/-- The power function `n ↦ n ^ ν` is completely multiplicative. -/
theorem cpow_apply_mul (ν : ℂ) (m n : ℕ) : cpow ν (m * n) = cpow ν m * cpow ν n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, Complex.natCast_mul_cpow]

/-- The power function `n ↦ n ^ ν` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_cpow (ν : ℂ) : IsMultiplicative (cpow ν) :=
  ⟨by simp, fun {m n} _ ↦ cpow_apply_mul ν m n⟩

/-- At a natural exponent `k`, `cpow k` is the cast of Mathlib's `ArithmeticFunction.pow k`. -/
theorem cpow_natCast (k : ℕ) : cpow k = (pow k : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, pow_apply]

/-- At exponent `0`, `cpow 0` is the constant function `ζ`. -/
theorem cpow_zero : cpow 0 = (ζ : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn]

/-- Adding exponents multiplies the power functions pointwise. -/
theorem cpow_add (ν μ : ℂ) : cpow (ν + μ) = (cpow ν).pmul (cpow μ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]

/-- Each value `n ^ ν` of the power function is entire in the exponent `ν`. -/
@[fun_prop]
theorem differentiable_cpow (n : ℕ) : Differentiable ℂ (fun ν : ℂ ↦ cpow ν n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [cpow_apply _ hn]
  exact fun _ ↦ differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))

/-- The divisor power sum `σ_ν(n) = ∑_{d ∣ n} d ^ ν` with complex exponent `ν`. Its value at `0`
is the empty sum `0`. -/
noncomputable def sigmaC (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ ∑ d ∈ n.divisors, (d : ℂ) ^ ν, by simp⟩

/-- `σ_ν(n)` is the sum of `d ^ ν` over the divisors `d` of `n`. -/
theorem sigmaC_apply (ν : ℂ) (n : ℕ) : sigmaC ν n = ∑ d ∈ n.divisors, (d : ℂ) ^ ν :=
  (rfl)

/-- Each value `σ_ν(n)` is entire in the exponent `ν`. -/
@[fun_prop]
theorem differentiable_sigmaC (n : ℕ) : Differentiable ℂ (fun ν : ℂ ↦ sigmaC ν n) := by
  simpa only [sigmaC_apply] using Nat.differentiable_sum_divisors_cpow n

/-- At a natural exponent `k`, `σ_k` is the cast of Mathlib's `ArithmeticFunction.sigma k`. -/
theorem sigmaC_natCast (k : ℕ) : sigmaC k = (σ k : ArithmeticFunction ℂ) := by
  ext n
  simp [sigmaC_apply, sigma_apply]

/-- `σ_ν` is the Dirichlet convolution of `ζ` with `n ↦ n ^ ν`. -/
theorem sigmaC_eq_zeta_mul_cpow (ν : ℂ) : sigmaC ν = (ζ : ArithmeticFunction ℂ) * cpow ν := by
  ext n
  rw [coe_zeta_mul_apply, sigmaC_apply]
  exact Finset.sum_congr rfl fun d hd ↦ (cpow_apply ν (Nat.pos_of_mem_divisors hd).ne').symm

/-- The divisor power sum `σ_ν` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_sigmaC (ν : ℂ) : IsMultiplicative (sigmaC ν) :=
  sigmaC_eq_zeta_mul_cpow ν ▸ isMultiplicative_zeta.natCast.mul (isMultiplicative_cpow ν)

/-- `σ_ν(1) = 1`. -/
@[simp]
theorem sigmaC_one (ν : ℂ) : sigmaC ν 1 = 1 :=
  (isMultiplicative_sigmaC ν).map_one

/-- The value of `σ_ν` at a prime power: `σ_ν(p ^ a) = ∑_{j ≤ a} p ^ {jν}`. -/
theorem sigmaC_apply_prime_pow (ν : ℂ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigmaC ν (p ^ a) = ∑ j ∈ Finset.range (a + 1), ((p : ℂ) ^ ν) ^ j := by
  simp [sigmaC_apply, Nat.divisors_prime_pow hp, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul]

/-- Reflection of the exponent: `σ_ν(n) = n ^ ν σ_{-ν}(n)`, that is, `σ_ν` is the pointwise
product of `cpow ν` and `σ_{-ν}`. -/
theorem sigmaC_eq_cpow_pmul_sigmaC_neg (ν : ℂ) : sigmaC ν = (cpow ν).pmul (sigmaC (-ν)) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [pmul_apply, cpow_apply ν hn]
  simpa [sigmaC_apply] using Nat.sum_divisors_cpow_neg n (-ν)

/-- `‖σ_ν(n)‖ ≤ τ(n) n ^ max(Re ν, 0)`: each of the `τ(n)` divisors `d ≤ n` contributes
`d ^ Re ν ≤ n ^ max(Re ν, 0)`. -/
theorem norm_sigmaC_le (ν : ℂ) (n : ℕ) :
    ‖sigmaC ν n‖ ≤ n.divisors.card * (n : ℝ) ^ max ν.re 0 := by
  rw [sigmaC_apply, ← nsmul_eq_mul, ← Finset.sum_const]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdn : (d : ℝ) ≤ n := by
    exact_mod_cast Nat.divisor_le hd
  rw [Complex.norm_natCast_cpow_of_pos hd0]
  calc (d : ℝ) ^ ν.re ≤ (d : ℝ) ^ max ν.re 0 :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd0) (le_max_left _ _)
    _ ≤ (n : ℝ) ^ max ν.re 0 := by gcongr

end TauCeti.ArithmeticFunction
