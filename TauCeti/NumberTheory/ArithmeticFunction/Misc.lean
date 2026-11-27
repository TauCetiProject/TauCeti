/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Dirichlet convolutions: weighted hyperbola sums and prime powers

Mathlib's `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` rewrites `∑_{0<n≤N} (f * g)(n)` as a sum
over the hyperbola `mℓ ≤ N`. This file adds the weighted form, where each term carries a weight
`w(n)` with values in a module; the weight stays attached to the product `mℓ`, so it need not be
multiplicative (for instance `w(n) = e(nα)`). The proof follows the plan of Mathlib's
`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`, through
`Nat.divisorsAntidiagonal_eq_prod_filter_of_le`.

The file also evaluates a Dirichlet convolution at a prime power `p ^ k` as a sum over the pairs
of exponents with sum `k`, and records the elementary bound `2 ^ Ω n ≤ n`, for `n ≠ 0`, on the
number `Ω n` of prime factors of `n` counted with multiplicity.

## Main results

* `ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum`:
  `∑_{0<n≤N} (f * g)(n) • w(n) = ∑_{0<m≤N} f(m) • ∑_{0<ℓ≤N/m} g(ℓ) • w(mℓ)`.
* `ArithmeticFunction.mul_apply_prime_pow`:
  `(f * g)(p ^ k) = ∑_{i + j = k} f(p ^ i) g(p ^ j)` for a prime `p`.
* `ArithmeticFunction.two_pow_cardFactors_le`: `2 ^ Ω n ≤ n` for `n ≠ 0`, since each of the
  `Ω n` prime factors of `n`, counted with multiplicity, is at least `2`.
-/

public section

open Finset

namespace ArithmeticFunction

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]

/-- Summing a Dirichlet convolution `f * g` against an arbitrary weight `w` over `0 < n ≤ N` is
the sum of `f(m) g(ℓ) w(mℓ)` over the hyperbola `mℓ ≤ N`. The weight stays attached to the
product `mℓ`; it need not be multiplicative. -/
theorem sum_Ioc_mul_smul_eq_sum_sum (f g : ArithmeticFunction R) (w : ℕ → A) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n • w n =
      ∑ m ∈ Ioc 0 N, f m • ∑ ℓ ∈ Ioc 0 (N / m), g ℓ • w (m * ℓ) := by
  calc ∑ n ∈ Ioc 0 N, (f * g) n • w n
      = ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n,
          (f x.1 * g x.2) • w (x.1 * x.2) := by
        refine sum_congr rfl fun n hn ↦ ?_
        rw [mem_Ioc] at hn
        rw [ArithmeticFunction.mul_apply, sum_smul,
          Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
        exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ∈ Ioc 0 N, (f x.1 * g x.2) • w (x.1 * x.2) :=
        sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ m ∈ Ioc 0 N, ∑ ℓ ∈ Ioc 0 N with m * ℓ ≤ N, (f m * g ℓ) • w (m * ℓ) := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun m hm ↦ ?_
        rw [sum_filter]
        refine sum_congr rfl fun ℓ hℓ ↦ ?_
        simp only [mem_Ioc] at hm hℓ
        have : 0 < m * ℓ := Nat.mul_pos hm.1 hℓ.1
        simp [this]
    _ = ∑ m ∈ Ioc 0 N, f m • ∑ ℓ ∈ Ioc 0 (N / m), g ℓ • w (m * ℓ) := by
        refine sum_congr rfl fun m hm ↦ ?_
        rw [smul_sum]
        have hm : 0 < m := (mem_Ioc.1 hm).1
        have : {ℓ ∈ Ioc 0 N | m * ℓ ≤ N} = Ioc 0 (N / m) := by
          ext ℓ
          simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le hm, mul_comm ℓ m]
          constructor
          · exact fun h ↦ ⟨h.1.1, h.2⟩
          · exact fun h ↦ ⟨⟨h.1, h.2.trans' (Nat.le_mul_of_pos_left ℓ hm)⟩, h.2⟩
        rw [this]
        exact sum_congr rfl fun ℓ _ ↦ (smul_smul _ _ _).symm

/-- At a prime power, a Dirichlet convolution is the sum over the pairs of exponents with sum `k`:
`(f * g)(p ^ k) = ∑_{i + j = k} f(p ^ i) g(p ^ j)`. -/
theorem mul_apply_prime_pow (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ ij ∈ antidiagonal k, f (p ^ ij.1) * g (p ^ ij.2) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ f a * g b),
    Nat.sum_divisors_prime_pow hp,
    Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ f (p ^ i) * g (p ^ j))]
  exact sum_congr rfl fun i hi ↦ by
    rw [Nat.pow_div (Nat.lt_succ_iff.1 (mem_range.1 hi)) hp.pos]

open scoped ArithmeticFunction.Omega in
/-- A nonzero natural number `n` is at least `2 ^ Ω n`, since each of its `Ω n` prime factors
(counted with multiplicity) is at least `2`. -/
theorem two_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Ω n ≤ n := by
  conv_rhs => rw [← Nat.prod_primeFactorsList hn]
  rw [cardFactors_apply]
  exact List.pow_length_le_prod _ _ fun p hp ↦ (Nat.prime_of_mem_primeFactorsList hp).two_le

end ArithmeticFunction
