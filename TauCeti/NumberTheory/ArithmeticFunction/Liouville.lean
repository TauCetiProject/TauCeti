/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import Mathlib.Algebra.Ring.GeomSum

/-!
# The Liouville function, the squares and the Möbius function

Write `λ` for the Liouville function, `1_□ = ζ_□` for the indicator of the positive squares and
`μ_□` for the dilation of the Möbius function by squares (`ArithmeticFunction.dilateSq`). This file
proves the three convolution identities

* `λ * ζ = 1_□`, that is `∑_{d ∣ n} λ(d) = 1` if `n ≥ 1` is a square and `0` otherwise;
* `λ = μ * 1_□`, that is `λ(n) = ∑_{d² ∣ n} μ(n / d²)`;
* `μ = λ * μ_□`, that is `μ(n) = ∑_{d² ∣ n} μ(d) λ(n / d²)`.

The first holds because both sides are multiplicative and at `p ^ a` the left side is
`∑_{j ≤ a} (-1) ^ j`, which is `1` for even `a` and `0` for odd `a`. The other two follow from it,
from `μ * ζ = 1` and from its dilation `1_□ * μ_□ = 1`.

The first and second identities, with the proof of the first through the factorization of `n` and
the reindexing of the square divisors, are adapted from `PrimeNumberTheoremAnd/Consequences.lean`
(`sum_divisors_liouville`, `lambda_eq_sum_sq_dvd_mu`) in the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, revision `2e6b7fe`).

## Main declarations

* `ArithmeticFunction.sum_divisors_liouville`, `ArithmeticFunction.liouville_mul_coe_zeta`:
  `λ * ζ = 1_□`.
* `ArithmeticFunction.liouville_eq_moebius_mul_dilateSq`,
  `ArithmeticFunction.liouville_apply_eq_sum`: `λ = μ * 1_□`.
* `ArithmeticFunction.liouville_mul_dilateSq_moebius`, `ArithmeticFunction.moebius_apply_eq_sum`:
  `μ = λ * μ_□`.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.Omega

namespace ArithmeticFunction

/-- The sum of the Liouville function over the divisors of `n ≠ 0` is `1` if `n` is a square
and `0` otherwise. -/
theorem sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, liouville d = if IsSquare n then 1 else 0 := by
  have hmul : (liouville * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
    isMultiplicative_liouville.mul isMultiplicative_zeta.natCast
  have hpow (p k : ℕ) (hp : p.Prime) :
      (liouville * (ζ : ArithmeticFunction ℤ)) (p ^ k) = if Even k then 1 else 0 := by
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp only [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp,
      neg_one_geom_sum, Nat.even_add_one, ite_not]
  rw [← coe_mul_zeta_apply, hmul.multiplicative_factorization _ hn,
    Finsupp.prod, Nat.support_factorization,
    prod_congr rfl fun p hp ↦ hpow p _ (Nat.prime_of_mem_primeFactors hp), prod_boole]
  refine if_congr ?_ rfl rfl
  rw [Nat.isSquare_iff_even_factorization]
  refine ⟨fun h p _ ↦ ?_, fun h p hp ↦ h p (Nat.prime_of_mem_primeFactors hp)⟩
  by_cases hp : p ∈ n.primeFactors
  · exact h p hp
  · rw [Finsupp.notMem_support_iff.1 hp]
    exact ⟨0, rfl⟩

/-- `λ * ζ = 1_□`: the convolution of the Liouville function with `ζ` is the indicator of the
positive squares. -/
theorem liouville_mul_coe_zeta :
    (liouville * ζ : ArithmeticFunction ℤ) = (ζ : ArithmeticFunction ℤ).dilateSq := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [coe_mul_zeta_apply, sum_divisors_liouville hn, dilateSq_apply]
  refine if_congr Iff.rfl ?_ rfl
  rw [natCoe_apply, zeta_apply_ne (Nat.sqrt_pos.2 (Nat.pos_of_ne_zero hn)).ne', Nat.cast_one]

/-- `λ = μ * 1_□`. -/
theorem liouville_eq_moebius_mul_dilateSq :
    (liouville : ArithmeticFunction ℤ) = μ * (ζ : ArithmeticFunction ℤ).dilateSq := by
  rw [← liouville_mul_coe_zeta, mul_comm, mul_assoc, coe_zeta_mul_moebius, mul_one]

/-- `λ(n) = ∑_{d² ∣ n} μ(n / d²)`. -/
theorem liouville_apply_eq_sum (n : ℕ) :
    liouville n = ∑ d ∈ n.divisors with d ^ 2 ∣ n, μ (n / d ^ 2) := by
  rw [liouville_eq_moebius_mul_dilateSq, mul_dilateSq_apply]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors (mem_filter.1 hd).1).ne',
    Nat.cast_one, mul_one]

/-- `μ = λ * μ_□`. -/
theorem liouville_mul_dilateSq_moebius : liouville * (μ : ArithmeticFunction ℤ).dilateSq = μ := by
  rw [liouville_eq_moebius_mul_dilateSq, mul_assoc, ← dilateSq_mul, coe_zeta_mul_moebius,
    dilateSq_one, mul_one]

/-- `μ(n) = ∑_{d² ∣ n} μ(d) λ(n / d²)`. -/
theorem moebius_apply_eq_sum (n : ℕ) :
    μ n = ∑ d ∈ n.divisors with d ^ 2 ∣ n, μ d * liouville (n / d ^ 2) := by
  have h := mul_dilateSq_apply liouville (μ : ArithmeticFunction ℤ) n
  rw [liouville_mul_dilateSq_moebius] at h
  exact h.trans (sum_congr rfl fun d _ ↦ mul_comm _ _)

end ArithmeticFunction
