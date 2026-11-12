/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
import TauCeti.NumberTheory.Chebyshev.LogFactorial

/-!
# Mertens's first theorem over `ℚ`

This file proves Mertens's first theorem with an absolute constant, valid at every real cutoff:

* `|∑_{n ≤ x} Λ(n) / n - log x| ≤ log 4 + 4` for every real `x ≥ 1`;
* `∑_{p ≤ x} log p / p = log x + O(1)` uniformly in real `x ≥ 1`, summing over Mathlib's
  `Nat.primesLE ⌊x⌋₊`;

and its standard consequence for the prime divisors of an integer,

* `∑_{p ∣ N} log p / p ≤ log log N + O(1)` for every natural number `N ≥ 3`.

The proof is Chebyshev's. By `Chebyshev.log_floor_factorial_eq_sum_vonMangoldt`,
`log ⌊x⌋! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋`, which lies between `x ∑_{n ≤ x} Λ(n) / n - ψ(x)` and
`x ∑_{n ≤ x} Λ(n) / n`. Mathlib's `Real.sum_log_le` and `Real.le_sum_log` give
`log ⌊x⌋! = x log x - x + O(log x)`, and its `Chebyshev.psi_le_const_mul_self` gives
`ψ(x) ≤ (log 4 + 4) x`; dividing by `x` gives the von Mangoldt form. The prime powers `p ^ k`
with `k ≥ 2` contribute at most the convergent series `∑_{n not prime} Λ(n) / n`, by
`TauCeti.sum_vonMangoldt_div_le_sum_primesLE_log_div_add_tsum`. For the prime divisors of `N`,
the primes `p ≤ log N` contribute `log log N + O(1)` by the prime form, and the primes
`p > log N` dividing `N` contribute at most `(∑_{p ∣ N} log p) / log N ≤ 1`.

`TauCeti.LFunctions.isBigO_primeSummatory_log_absNorm_div_sub_log` proves Mertens's first theorem
for every number field as an asymptotic statement over prime ideals; the statements here are the
uniform bounds over rational primes, with an explicit constant in the von Mangoldt form.

## Main results

* `TauCeti.abs_sum_vonMangoldt_div_sub_log_le`: `|∑_{n ≤ x} Λ(n) / n - log x| ≤ log 4 + 4`.
* `TauCeti.exists_abs_sum_primesLE_log_div_sub_log_le`: `∑_{p ≤ x} log p / p = log x + O(1)`.
* `TauCeti.exists_sum_primeFactors_log_div_le_log_log_add`:
  `∑_{p ∣ N} log p / p ≤ log log N + O(1)`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  AMS, 2019, Theorem 3.4(a) and its proof.
-/

public section

open Finset Real
open ArithmeticFunction hiding log
open scoped Nat

namespace TauCeti

/-- **Mertens's first theorem, von Mangoldt form.** For every real `x ≥ 1`,
`|∑_{n ≤ x} Λ(n) / n - log x| ≤ log 4 + 4`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x| ≤ log 4 + 4 := by
  set S := ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n
  have hx0 : 0 < x := by linarith
  -- Chebyshev's identity sandwiches `log ⌊x⌋!` between `x S - ψ(x)` and `x S`.
  have hupper : log ⌊x⌋₊ ! ≤ x * S := by
    rw [Chebyshev.log_floor_factorial_eq_sum_vonMangoldt, mul_sum]
    refine sum_le_sum fun n hn ↦ ?_
    have hn : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    calc Λ n * ⌊x / n⌋₊ ≤ Λ n * (x / n) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) vonMangoldt_nonneg
      _ = x * (Λ n / n) := by ring
  have hlower : x * S - Chebyshev.psi x ≤ log ⌊x⌋₊ ! := by
    rw [Chebyshev.log_floor_factorial_eq_sum_vonMangoldt, mul_sum, Chebyshev.psi,
      ← sum_sub_distrib]
    refine sum_le_sum fun n hn ↦ ?_
    have hn : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    calc x * (Λ n / n) - Λ n = Λ n * (x / n - 1) := by field_simp
      _ ≤ Λ n * ⌊x / n⌋₊ := mul_le_mul_of_nonneg_left
          (by linarith [Nat.lt_floor_add_one (x / n)]) vonMangoldt_nonneg
  have hfac_le := sum_log_eq_log_factorial ⌊x⌋₊ ▸ sum_log_le hx
  have hle_fac := sum_log_eq_log_factorial ⌊x⌋₊ ▸ le_sum_log hx
  have hpsi := Chebyshev.psi_le_const_mul_self hx0.le
  have hlog : log x ≤ x - 1 := log_le_sub_one_of_pos hx0
  have hlog4 : 0 ≤ log 4 := log_nonneg (by norm_num)
  -- Multiply through by `x > 0`.
  rw [abs_le, ← mul_le_mul_iff_of_pos_left hx0, ← mul_le_mul_iff_of_pos_left hx0 (b := S - log x)]
  constructor <;> nlinarith

/-- **Mertens's first theorem.** There is an absolute constant `C` with
`|∑_{p ≤ x} log p / p - log x| ≤ C` for every real `x ≥ 1`. -/
theorem exists_abs_sum_primesLE_log_div_sub_log_le :
    ∃ C, ∀ x : ℝ, 1 ≤ x → |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  set B := ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n
  have hB : 0 ≤ B := tsum_nonneg fun n ↦ by positivity [vonMangoldt_nonneg (n := n)]
  refine ⟨log 4 + 4 + B, fun x hx ↦ ?_⟩
  have hM := abs_le.mp (abs_sum_vonMangoldt_div_sub_log_le hx)
  have h₂ := sum_primesLE_log_div_le_sum_vonMangoldt_div ⌊x⌋₊
  have h₁ := sum_vonMangoldt_div_le_sum_primesLE_log_div_add_tsum ⌊x⌋₊
  rw [abs_le]
  constructor <;> linarith [hM.1, hM.2]

/-- The sum of `log p / p` over the prime divisors of `N` is `O(log log N)`: there is an absolute
constant `C` with `∑_{p ∣ N} log p / p ≤ log log N + C` for every natural number `N ≥ 3`. -/
theorem exists_sum_primeFactors_log_div_le_log_log_add :
    ∃ C, ∀ N : ℕ, 3 ≤ N → ∑ p ∈ N.primeFactors, log p / p ≤ log (log N) + C := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_log_div_sub_log_le
  refine ⟨C + 1, fun N hN ↦ ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set y := log N
  have hy : 1 ≤ y := by
    rw [le_log_iff_exp_le hN0]
    linarith [exp_one_lt_three]
  have hy0 : 0 < y := by linarith
  have hlogp (p : ℕ) (hp : p ∈ N.primeFactors) : 0 ≤ log p :=
    log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
  rw [← sum_filter_add_sum_filter_not _ (· ≤ ⌊y⌋₊)]
  -- The primes `p ≤ log N` contribute at most `log log N + C` by Mertens's theorem.
  have hsmall : ∑ p ∈ N.primeFactors with p ≤ ⌊y⌋₊, log p / p ≤ log y + C := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p _ _ ↦ ?_)
      (sub_le_iff_le_add'.mp (abs_le.mp (hC y hy)).2)
    · rw [mem_filter, Nat.mem_primeFactors] at hp
      exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.1⟩
    · positivity
  -- The primes `p > log N` dividing `N` contribute at most `(∑_{p ∣ N} log p) / log N ≤ 1`.
  have hlarge : ∑ p ∈ N.primeFactors with ¬p ≤ ⌊y⌋₊, log p / p ≤ 1 := by
    have hprod : ∑ p ∈ N.primeFactors, log p ≤ y := by
      have hle : ∏ p ∈ N.primeFactors, p ≤ N := Nat.le_of_dvd (by lia) (Nat.prod_primeFactors_dvd N)
      rw [← log_prod (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero),
        ← Nat.cast_prod]
      exact log_le_log (by exact_mod_cast prod_pos fun p hp ↦ Nat.pos_of_mem_primeFactors hp)
        (by exact_mod_cast hle)
    calc ∑ p ∈ N.primeFactors with ¬p ≤ ⌊y⌋₊, log p / p
        ≤ ∑ p ∈ N.primeFactors with ¬p ≤ ⌊y⌋₊, log p / y := by
          refine sum_le_sum fun p hp ↦ ?_
          rw [mem_filter, not_le, Nat.floor_lt hy0.le] at hp
          exact div_le_div_of_nonneg_left (hlogp p hp.1) hy0 hp.2.le
      _ ≤ ∑ p ∈ N.primeFactors, log p / y :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦
            div_nonneg (hlogp p hp) hy0.le
      _ ≤ 1 := by
          rw [← sum_div, div_le_one hy0]
          exact hprod
  exact (add_le_add hsmall hlarge).trans_eq (by ring)

end TauCeti
