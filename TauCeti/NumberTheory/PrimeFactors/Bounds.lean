/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Bounds for products and logarithmic sums over prime divisors

For every fixed `C ≥ 1` and `ε > 0`, the product `C ^ ω(n)` is at most `A n ^ ε`, with `A`
independent of the positive integer `n`, where `ω(n)` counts distinct prime divisors. This controls
finite Euler corrections whose local factors are uniformly bounded.

On the logarithmic side, since `∏_{p ∣ n} p ≤ n` for `n ≠ 0`, the unweighted prime-divisor sum
satisfies `∑_{p ∣ n} log p ≤ log n`. Splitting the primes dividing `n` at the threshold `log n`
and bounding the primes below `log n` by Mertens' first theorem yields the sharp explicit bound

`∑_{p ∣ n} log p / p ≤ log (log n) + (log 4 + 5)`

for all `n : ℕ`, controlling the deleted-prime contribution to logarithmic derivatives `-L'/L(s, χ)`
of imprimitive Dirichlet `L`-functions.

## Main results

* `TauCeti.exists_pow_card_primeFactors_le_mul_rpow`: `C ^ ω(n) ≤ A n ^ ε` for `n ≠ 0`.
* `Nat.prod_primeFactors_eq_filter_lt_mul_filter_ge`,
  `Nat.sum_primeFactors_eq_filter_lt_add_filter_ge`: splitting products and sums over
  `n.primeFactors` at a real threshold `X`.
* `Nat.sum_primeFactors_log_le`, `Nat.sum_primeFactors_log_div_le`: elementary bounds
  `∑_{p ∣ n} log p ≤ log n` and `∑_{p ∣ n} log p / p ≤ log n / 2`.
* `Nat.sum_primeFactors_filter_ge_log_div_le`, `Nat.sum_primeFactors_filter_lt_log_div_le`:
  bounds above and below a threshold `X`.
* `Nat.sum_primeFactors_log_div_le_log_log_add`:
  `∑_{p ∣ n} log p / p ≤ log (log n) + (log 4 + 5)` for every `n : ℕ`.

## References

* H. Davenport, *Multiplicative Number Theory*, elementary divisor and imprimitive-character bounds.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 3.4(a).
-/

public section

open Finset Filter

namespace TauCeti

/-- A fixed exponential of the number of distinct prime factors grows more slowly than any
positive power, uniformly over all positive integers. -/
theorem exists_pow_card_primeFactors_le_mul_rpow {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ A > 0, ∀ n : ℕ, n ≠ 0 → C ^ n.primeFactors.card ≤ A * (n : ℝ) ^ ε := by
  obtain ⟨P, hP⟩ := eventually_atTop.1 <|
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop C)
  refine ⟨C ^ P, pow_pos (lt_of_lt_of_le zero_lt_one hC) _, fun n hn ↦ ?_⟩
  have hsmall : (n.primeFactors.filter (· < P)).card ≤ P := by
    have hsub : n.primeFactors.filter (· < P) ⊆ range P :=
      fun _ hp ↦ mem_range.2 (mem_filter.1 hp).2
    simpa using card_le_card hsub
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  calc
    C ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, C := (prod_const C).symm
    _ ≤ ∏ p ∈ n.primeFactors, (if p < P then C else 1) * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ le_trans zero_le_one hC)
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      split_ifs with h
      · exact le_mul_of_one_le_right (le_trans zero_le_one hC)
          (Real.one_le_rpow hp1 hε.le)
      · simpa using hP p (by omega)
    _ = C ^ (n.primeFactors.filter (· < P)).card * (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε := by
      rw [prod_mul_distrib, ← prod_filter, prod_const, Real.finsetProd_rpow]
      exact fun _ _ ↦ Nat.cast_nonneg _
    _ ≤ C ^ P * (n : ℝ) ^ ε := by gcongr

end TauCeti

namespace Nat

/-- Splitting a product over the distinct prime divisors of `n` at a real threshold `X`. -/
@[to_additive /-- Splitting a sum over the distinct prime divisors of `n` at a real threshold
`X`. -/]
theorem prod_primeFactors_eq_filter_lt_mul_filter_ge {M : Type*} [CommMonoid M] (n : ℕ) (X : ℝ)
    (f : ℕ → M) :
    ∏ p ∈ n.primeFactors, f p =
      (∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < X), f p) *
        ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), f p := by
  rw [← prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ ↦ (p : ℝ) < X)]
  congr 2
  exact filter_congr fun _ _ ↦ not_lt

/-- The sum of `log p` over the distinct prime divisors of `n` is at most `log n`. -/
theorem sum_primeFactors_log_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) :=
      prod_pos fun p hp ↦ mod_cast (prime_of_mem_primeFactors hp).pos
    have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
      simpa only [cast_prod] using (cast_le (α := ℝ)).mpr
        (le_of_dvd (pos_of_ne_zero hn) (prod_primeFactors_dvd n))
    rw [← Real.log_prod fun p hp ↦ mod_cast (prime_of_mem_primeFactors hp).ne_zero]
    exact Real.log_le_log hpos hprod

/-- Elementary bound `∑_{p ∣ n} log p / p ≤ log n / 2` for every `n : ℕ`, using `p ≥ 2` on prime
divisors. -/
theorem sum_primeFactors_log_div_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log n / 2 := by
  calc ∑ p ∈ n.primeFactors, Real.log p / p
      ≤ ∑ p ∈ n.primeFactors, Real.log p / 2 := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp_prime := prime_of_mem_primeFactors hp
        exact div_le_div_of_nonneg_left (Real.log_nonneg (mod_cast hp_prime.one_lt.le)) zero_lt_two
          (mod_cast hp_prime.two_le)
    _ = (∑ p ∈ n.primeFactors, Real.log p) / 2 := (sum_div _ _ _).symm
    _ ≤ Real.log n / 2 := div_le_div_of_nonneg_right (sum_primeFactors_log_le n) zero_le_two

/-- Prime divisors `p ≥ X` of `n` contribute at most `log n / X` to `∑_{p ∣ n} log p / p` for
`X > 0`. -/
theorem sum_primeFactors_filter_ge_log_div_le (n : ℕ) {X : ℝ} (hX : 0 < X) :
    ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / p ≤ Real.log n / X := by
  calc ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / p
      ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / X := by
        refine sum_le_sum fun p hp ↦ ?_
        obtain ⟨hp_mem, hpX⟩ := mem_filter.mp hp
        exact div_le_div_of_nonneg_left
          (Real.log_nonneg (mod_cast (prime_of_mem_primeFactors hp_mem).one_lt.le)) hX hpX
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p / X :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦
          div_nonneg (Real.log_nonneg (mod_cast (prime_of_mem_primeFactors hp).one_lt.le)) hX.le
    _ = (∑ p ∈ n.primeFactors, Real.log p) / X := (sum_div _ _ _).symm
    _ ≤ Real.log n / X := div_le_div_of_nonneg_right (sum_primeFactors_log_le n) hX.le

/-- Prime divisors `p < X` of `n` contribute at most `log X + (log 4 + 4)` to `∑_{p ∣ n} log p / p`
for `X ≥ 1`, by Mertens' first theorem. -/
theorem sum_primeFactors_filter_lt_log_div_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < X), Real.log p / p ≤
      Real.log X + (Real.log 4 + 4) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hsub : n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < X) ⊆
      (primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < X) := by
    intro p hp
    obtain ⟨hp_mem, hlt⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_primesLE.mpr ⟨(le_floor_iff hX0).mpr hlt.le,
      prime_of_mem_primeFactors hp_mem⟩, hlt⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ ?_).trans
    (Chebyshev.sum_primesLE_filter_lt_log_div_le_log_add hX)
  exact div_nonneg (Real.log_nonneg (mod_cast
    (prime_of_mem_primesLE (mem_filter.mp hp).1).one_lt.le)) (cast_nonneg p)

/-- **Logarithmic prime-divisor bound.** For every `n : ℕ`,
`∑_{p ∣ n} log p / p ≤ log (log n) + (log 4 + 5)`. -/
theorem sum_primeFactors_log_div_le_log_log_add (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log (Real.log n) + (Real.log 4 + 5) := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow, cast_ofNat]
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      simp only [primeFactors_zero, sum_empty, cast_zero, Real.log_zero]
      linarith
    · have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      simp only [primeFactors_one, sum_empty, cast_one, Real.log_one, Real.log_zero]
      linarith
    · have hexp : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
      have h1 : 1 < Real.log 4 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
      have hlog2 : 1 / 2 < Real.log 2 := by linarith
      have hll2 : -Real.log 2 < Real.log (Real.log 2) := by
        simpa [one_div, Real.log_inv] using Real.log_lt_log (by norm_num) hlog2
      have h2 := sum_primeFactors_log_div_le 2
      push_cast at h2 ⊢
      linarith
  · have hn3 : (3 : ℝ) ≤ n := mod_cast hn
    have hlog1 : 1 < Real.log n := (Real.lt_log_iff_exp_lt (by linarith)).mpr
      (Real.exp_one_lt_d9.trans_le (by linarith))
    have hlog0 : 0 < Real.log n := zero_lt_one.trans hlog1
    rw [sum_primeFactors_eq_filter_lt_add_filter_ge n (Real.log n)]
    have hlt := sum_primeFactors_filter_lt_log_div_le n hlog1.le
    have hge := (sum_primeFactors_filter_ge_log_div_le n hlog0).trans_eq (div_self hlog0.ne')
    linarith

end Nat
