/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp

/-!
# Jordan's totient function

Jordan's totient function of order `k` is the Dirichlet convolution `J_k = μ * pow k`, so
`J_k n = ∑_{d ∣ n} μ d * (n / d) ^ k`. It is the Möbius inverse of `n ↦ n ^ k`, that is,
`∑_{d ∣ n} J_k d = n ^ k`, and it has the Euler product
`J_k n = n ^ k * ∏_{p ∣ n} (1 - p⁻ᵏ)`. For `k = 1` it is Euler's totient function.

The decomposition `n ^ k = ∑_{d ∣ n} J_k d` is what turns a family of identities indexed by
`gcd (m, d) ^ k` into identities indexed by the common divisors of `m` and `d`, which can then be
inverted along the divisor lattice.

## Main definitions and results

* `ArithmeticFunction.jordanTotient k`: Jordan's totient function `J_k = μ * pow k`, with integer
  values.
* `ArithmeticFunction.sum_divisors_jordanTotient`: `∑_{d ∣ n} J_k d = n ^ k` for `n ≠ 0`.
* `ArithmeticFunction.gcd_pow_eq_sum_jordanTotient`: `gcd (m, d) ^ k` is the sum of `J_k e` over
  the common divisors `e` of `m` and `d`.
* `ArithmeticFunction.jordanTotient_eq_prod`: the Euler product
  `J_k n = n ^ k * ∏_{p ∣ n} (1 - (p ^ k)⁻¹)`.
* `ArithmeticFunction.jordanTotient_one_apply`: `J_1 = φ`.
* `ArithmeticFunction.jordanTotient_pos`: `J_k n > 0` for `k ≠ 0` and `n ≠ 0`.

## References

* L. E. Dickson, *History of the theory of numbers*, Vol. I, Chapter V.
* T. M. Apostol, *Introduction to analytic number theory*, Chapter 2, Exercise 15.
-/

public section

open Finset

namespace ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Jordan's totient function `J_k = μ * pow k` of order `k`, so that
`J_k n = ∑_{d ∣ n} μ d * (n / d) ^ k` (`jordanTotient_apply`). For `n ≠ 0`, `J_k n` is the
number of `k`-tuples in `(ZMod n) ^ k` whose entries together with `n` have greatest common divisor
one. -/
def jordanTotient (k : ℕ) : ArithmeticFunction ℤ :=
  μ * (pow k : ArithmeticFunction ℤ)

theorem jordanTotient_def (k : ℕ) : jordanTotient k = μ * (pow k : ArithmeticFunction ℤ) := (rfl)

theorem jordanTotient_apply (k n : ℕ) :
    jordanTotient k n = ∑ d ∈ n.divisors, μ d * ((n / d : ℕ) : ℤ) ^ k := by
  rw [jordanTotient_def, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦ μ a * (pow k : ArithmeticFunction ℤ) b)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hnd : n / d ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  simp [natCoe_apply, pow_apply, hnd]

/-- `J_k` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_jordanTotient (k : ℕ) : (jordanTotient k).IsMultiplicative :=
  isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- `J_k 1 = 1`. -/
@[simp]
theorem jordanTotient_apply_one (k : ℕ) : jordanTotient k 1 = 1 :=
  (isMultiplicative_jordanTotient k).map_one

/-- `J_k * ζ = pow k`: Jordan's totient function is the Möbius inverse of `n ↦ n ^ k`. -/
@[simp]
theorem jordanTotient_mul_coe_zeta (k : ℕ) :
    jordanTotient k * ζ = (pow k : ArithmeticFunction ℤ) := by
  rw [jordanTotient_def, mul_comm (μ : ArithmeticFunction ℤ), mul_assoc, moebius_mul_coe_zeta,
    mul_one]

/-- The sum of `J_k` over the divisors of a nonzero `n` is `n ^ k`. -/
theorem sum_divisors_jordanTotient (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordanTotient k d = (n : ℤ) ^ k := by
  rw [← coe_mul_zeta_apply, jordanTotient_mul_coe_zeta, natCoe_apply, pow_apply]
  simp [hn]

/-- `gcd (m, d) ^ k` is the sum of `J_k e` over the common divisors `e` of `m` and `d`. -/
theorem gcd_pow_eq_sum_jordanTotient (k m : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ((m.gcd d : ℕ) : ℤ) ^ k = ∑ e ∈ d.divisors with e ∣ m, jordanTotient k e := by
  rw [← sum_divisors_jordanTotient k (Nat.gcd_ne_zero_right hd)]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext e
  simp [Nat.dvd_gcd_iff, hd, Nat.gcd_ne_zero_right hd, and_comm]

/-- The Euler product of Jordan's totient function:
`J_k n = n ^ k * ∏_{p ∣ n} (1 - (p ^ k)⁻¹)` for `n ≠ 0`. -/
theorem jordanTotient_eq_prod {R : Type*} [Field R] [CharZero R] (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (jordanTotient k n : R) = n ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : R) ^ k)⁻¹) := by
  -- the multiplicative function `d ↦ (d ^ k)⁻¹`, made zero at `0`
  let f : ArithmeticFunction R := ⟨fun d ↦ if d = 0 then 0 else ((d : R) ^ k)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [f], fun {m d} hm hd _ ↦ ?_⟩
    simp [f, hm, hd, mul_pow, mul_comm]
  have hprod : ∏ p ∈ n.primeFactors, (1 - ((p : R) ^ k)⁻¹) = ∏ p ∈ n.primeFactors, (1 - f p) :=
    Finset.prod_congr rfl fun p hp ↦ by
      simp [f, (Nat.prime_of_mem_primeFactors hp).ne_zero]
  rw [hprod, hf.prodPrimeFactors_one_sub f hn, jordanTotient_apply, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdR : (d : R) ≠ 0 := Nat.cast_ne_zero.2 hd0
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, coe_mk, f, hd0, ite_false,
    Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR, div_pow]
  field_simp

/-- At a prime `p`, `J_k p = p ^ k - 1`. -/
@[simp]
theorem jordanTotient_apply_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    jordanTotient k p = (p : ℤ) ^ k - 1 := by
  rw [jordanTotient_apply, Nat.Prime.sum_divisors hp]
  simp [moebius_apply_prime hp, Nat.div_self hp.pos, sub_eq_neg_add]

/-- Jordan's totient function of order one is Euler's totient function. -/
@[simp]
theorem jordanTotient_one_apply (n : ℕ) : jordanTotient 1 n = n.totient := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h := (jordanTotient_eq_prod (R := ℚ) 1 hn).trans
    (by simpa using (Nat.totient_eq_mul_prod_factors n).symm)
  exact_mod_cast h

/-- Jordan's totient function of positive order is positive away from `0`. -/
theorem jordanTotient_pos {k : ℕ} (hk : k ≠ 0) {n : ℕ} (hn : n ≠ 0) : 0 < jordanTotient k n := by
  have h := jordanTotient_eq_prod (R := ℚ) k hn
  have hpos : (0 : ℚ) < n ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : ℚ) ^ k)⁻¹) := by
    refine mul_pos (by positivity) (Finset.prod_pos fun p hp ↦ ?_)
    have hp1 : (1 : ℚ) < (p : ℚ) ^ k :=
      one_lt_pow₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) hk
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hp1
  exact_mod_cast h ▸ hpos

end ArithmeticFunction
