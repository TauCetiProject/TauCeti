/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Bounds for products and logarithmic sums over prime divisors

For every fixed `C ≥ 1` and `ε > 0`, the product `C ^ ω(n)` is at most `A n ^ ε`, with `A`
independent of the positive integer `n`, where `ω(n)` counts distinct prime divisors. This controls
finite Euler corrections whose local factors are uniformly bounded; the elementary argument
separates the finitely many primes for which `p ^ ε < C`. On `Re s ≥ 0`, each Euler factor
`1 - p⁻ˢ` at a prime divisor `p ∣ N` has norm at most `2 ≤ p`, giving the linear bound
`‖∏_{p ∣ N} (1 - p⁻ˢ)‖ ≤ N` for `N ≠ 0`.

On the logarithmic side, since `∏_{p ∣ n} p ≤ n` for `n ≠ 0`, the unweighted prime-divisor sum
satisfies `∑_{p ∣ n} log p ≤ log n`. Splitting the primes dividing `n` at the threshold `log n`
and bounding the primes below `log n` by Mertens' first theorem yields the explicit bound

`∑_{p ∣ n} log p / p ≤ log (log n) + (log 4 + 5)`

for all `n : ℕ` (with `n = 0, 1` holding via `n.primeFactors = ∅` and `Real.log 0 = 0`), where
only the `log (log n)` order of growth is asymptotically sharp. This controls the deleted-prime
contribution to logarithmic derivatives `-L'/L(s, χ)` of imprimitive Dirichlet `L`-functions.

The same splitting at a real cutoff `y` bounds the Euler factors `(1 - p⁻¹)⁻¹` of the prime
divisors of `n`: those with `p ≤ y` by the full Euler product over the primes up to `y`, and
those with `p > y`, of which there are at most `log n / log y` when `y > 1`, by
`exp (2 log n / (y log y))`.

## Main results

* `TauCeti.exists_pow_card_primeFactors_le_mul_rpow`: `C ^ ω(n) ≤ A n ^ ε` for `n ≠ 0`.
* `TauCeti.norm_prod_primeFactors_one_sub_cpow_neg_le`: `‖∏_{p ∣ N} (1 - p⁻ˢ)‖ ≤ N` for `N ≠ 0` and
  `Re s ≥ 0`.
* `Nat.sum_primeFactors_log_le`, `Nat.sum_primeFactors_log_div_le`: elementary bounds
  `∑_{p ∣ n} log p ≤ log n` and `∑_{p ∣ n} log p / p ≤ log n / 2`.
* `Nat.sum_primeFactors_filter_ge_log_div_le`, `Nat.sum_primeFactors_filter_lt_log_div_le`:
  bounds above and below a threshold `X`.
* `Nat.card_primeFactors_filter_gt_mul_log_le`: `#{p ∣ n : y < p} * log y ≤ log n` for `y ≥ 0`,
  so `n` has at most `log n / log y` prime divisors `p > y` when `y > 1`.
* `Nat.prod_primeFactors_filter_le_one_sub_inv_inv_le`,
  `Nat.prod_primeFactors_filter_gt_one_sub_inv_inv_le`: the Euler factors `(1 - p⁻¹)⁻¹` of the
  prime divisors `p ≤ y` of `n` multiply to at most `∏_{p ≤ y} (1 - p⁻¹)⁻¹`, and those of the
  prime divisors `p > y` to at most `exp (2 log n / (y log y))`, for `y > 1`.
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

/-- On the closed right half-plane `Re s ≥ 0`, the finite Euler-factor product
`∏ p ∈ N.primeFactors, (1 - p⁻ˢ)` for `N ≠ 0` has norm at most `N`, since each factor at a prime
`p ∣ N` has norm at most `1 + p^{-Re s} ≤ 2 ≤ p`. -/
theorem norm_prod_primeFactors_one_sub_cpow_neg_le {N : ℕ} [NeZero N] {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ N := by
  rw [norm_prod]
  calc ∏ p ∈ N.primeFactors, ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖
      ≤ ∏ p ∈ N.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p hp ↦ ?_
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
        have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
        calc ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith
          _ ≤ p := hp2
    _ = ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ N := by exact_mod_cast Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)

end TauCeti

namespace Nat

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

/-- For every real `y ≥ 0`, the prime divisors `p > y` of `n` satisfy
`#{p ∣ n : y < p} * log y ≤ log n`: for `n ≠ 0` their product is at most `n`, and each of them
exceeds `y`. For `y > 1` this bounds their number by `log n / log y`; for `y ≤ 1` the left side is
nonpositive. -/
theorem card_primeFactors_filter_gt_mul_log_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y ≤ Real.log n := by
  rcases hy.eq_or_lt with rfl | hy
  · simpa using Real.log_natCast_nonneg n
  calc (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y
      = ∑ _p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.log y := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.log p :=
        sum_le_sum fun p hp ↦ Real.log_le_log hy (mem_filter.1 hp).2.le
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ Real.log_natCast_nonneg p
    _ ≤ Real.log n := sum_primeFactors_log_le n

/-- The Euler factors of the prime divisors `p ≤ y` of `n` are bounded by the full Euler product
over the primes `p ≤ y`. -/
theorem prod_primeFactors_filter_le_one_sub_inv_inv_le (n : ℕ) (y : ℝ) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y), (1 - (p : ℝ)⁻¹)⁻¹ ≤
      ∏ p ∈ primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hpos : ∀ p : ℕ, p.Prime → 0 < 1 - (p : ℝ)⁻¹ := fun p hp ↦
    sub_pos.2 (inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt))
  refine prod_le_prod_of_subset_of_one_le₀ (fun p hp ↦ ?_) (fun p hp ↦ ?_) fun p hp _ ↦ ?_
  · obtain ⟨hp, hpy⟩ := mem_filter.1 hp
    exact mem_primesLE.2 ⟨le_floor hpy, prime_of_mem_primeFactors hp⟩
  · exact (inv_pos.2 (hpos p (prime_of_mem_primeFactors (mem_filter.1 hp).1))).le
  · exact (one_le_inv₀ (hpos p (prime_of_mem_primesLE hp))).2 (sub_le_self 1 (by positivity))

/-- The Euler factors of the prime divisors `p > y` of `n` multiply to at most
`exp (2 log n / (y log y))`, for every real `y > 1`. -/
theorem prod_primeFactors_filter_gt_one_sub_inv_inv_le (n : ℕ) {y : ℝ} (hy : 1 < y) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), (1 - (p : ℝ)⁻¹)⁻¹ ≤
      Real.exp (2 * Real.log n / (y * Real.log y)) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hfactor : ∀ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 / y) := by
    intro p hp
    obtain ⟨hp, hyp⟩ := mem_filter.1 hp
    have hp2 : (2 : ℝ) ≤ p := mod_cast (prime_of_mem_primeFactors hp).two_le
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ two_pos hp2
    have hlog := Real.abs_log_le_two_mul_one_sub (x := 1 - (p : ℝ)⁻¹) (by linarith)
      (sub_le_self 1 (inv_nonneg.2 (zero_le_two.trans hp2)))
    rw [sub_sub_cancel] at hlog
    have hpy : (p : ℝ)⁻¹ ≤ y⁻¹ := inv_anti₀ hy0 hyp.le
    rw [← Real.exp_log (inv_pos.2 (by linarith : 0 < 1 - (p : ℝ)⁻¹)), Real.log_inv]
    refine Real.exp_le_exp.2 ?_
    rw [div_eq_mul_inv]
    linarith [neg_le_abs (Real.log (1 - (p : ℝ)⁻¹))]
  have hcard : (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y) ≤
      2 * Real.log n / (y * Real.log y) := by
    rw [le_div_iff₀ (mul_pos hy0 hlogy)]
    calc (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y) * (y * Real.log y)
        = 2 * ((#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y) := by field_simp
      _ ≤ 2 * Real.log n := by gcongr; exact card_primeFactors_filter_gt_mul_log_le n hy0.le
  calc ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), (1 - (p : ℝ)⁻¹)⁻¹
      ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.exp (2 / y) :=
        prod_le_prod₀ (fun p _ ↦ inv_nonneg.2 (sub_nonneg.2 (cast_inv_le_one p))) hfactor
    _ = Real.exp ((#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y)) := by
        rw [prod_const, ← Real.exp_natCast_mul]
    _ ≤ Real.exp (2 * Real.log n / (y * Real.log y)) := Real.exp_le_exp.2 hcard

/-- Elementary bound `∑_{p ∣ n} log p / p ≤ log n / 2` for every `n : ℕ`, using `p ≥ 2` on prime
divisors. -/
theorem sum_primeFactors_log_div_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log n / 2 := by
  have hfilt : n.primeFactors.filter (fun p : ℕ ↦ (2 : ℝ) ≤ (p : ℝ)) = n.primeFactors :=
    filter_eq_self.mpr fun p hp ↦ mod_cast (prime_of_mem_primeFactors hp).two_le
  simpa only [hfilt] using sum_primeFactors_filter_ge_log_div_le n zero_lt_two

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
`∑_{p ∣ n} log p / p ≤ log (log n) + (log 4 + 5)` (holding for `n = 0, 1` via `n.primeFactors = ∅`
and `Real.log 0 = 0`). -/
theorem sum_primeFactors_log_div_le_log_log_add (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log (Real.log n) + (Real.log 4 + 5) := by
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      simp only [primeFactors_zero, sum_empty, cast_zero, Real.log_zero]
      linarith
    · have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      simp only [primeFactors_one, sum_empty, cast_one, Real.log_one, Real.log_zero]
      linarith
    · have hlog2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hll2 : -Real.log 2 < Real.log (Real.log 2) := by
        simpa [one_div, Real.log_inv] using Real.log_lt_log (by norm_num) hlog2
      have h2 := sum_primeFactors_log_div_le 2
      push_cast at h2 ⊢
      linarith [Real.log_four_eq]
  · have hn3 : (3 : ℝ) ≤ n := mod_cast hn
    have hlog1 : 1 < Real.log n := (Real.lt_log_iff_exp_lt (by linarith)).mpr
      (Real.exp_one_lt_three.trans_le hn3)
    have hlog0 : 0 < Real.log n := zero_lt_one.trans hlog1
    rw [← sum_filter_add_sum_filter_not n.primeFactors (fun p : ℕ ↦ (p : ℝ) < Real.log n)]
    simp only [not_lt]
    have hlt := sum_primeFactors_filter_lt_log_div_le n hlog1.le
    have hge := (sum_primeFactors_filter_ge_log_div_le n hlog0).trans_eq (div_self hlog0.ne')
    linarith

end Nat
