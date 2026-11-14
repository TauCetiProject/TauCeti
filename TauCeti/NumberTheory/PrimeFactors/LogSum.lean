/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Logarithmic weight of prime divisors

For a nonzero integer `n`, the product of its distinct prime factors divides `n`
(`Nat.prod_primeFactors_dvd`), so `∑_{p ∣ n} log p ≤ log n`, with equality when `n` is squarefree.
Since every prime satisfies `p ≥ 2`, dividing by `p` immediately gives the constant-free bound
`∑_{p ∣ n} log p / p ≤ log n / 2` and a corresponding lower bound on the Mertens sum restricted to
primes not dividing `n`.

Splitting `n.primeFactors` at an arbitrary positive real cutoff `X` separates the primes strictly
below `X`, which lie in `Nat.primesBelow ⌈X⌉₊`, from the primes `p ≥ X`, whose reciprocals are at
most `1 / X` and whose logarithmic sum is at most `log n`. Combining this split with Mertens's
first theorem at `X = log n` yields the sharper bound
`∑_{p ∣ n} log p / p ≤ log (log n) + log 4 + 5` for every natural number `n` (trivially at
`n = 0, 1`, and including `n = 2` where `log (log 2) < 0`), hence
`∑_{p ∣ n} log p / p = O(log log n)`.

## Main results

* `TauCeti.sum_primeFactors_log_le_log`: `∑_{p ∣ n} log p ≤ log n` for every natural number `n`.
* `TauCeti.sum_primeFactors_log_eq_log`: equality when `n` is squarefree.
* `TauCeti.sum_primeFactors_log_div_le_half_log`,
  `TauCeti.sum_primesLE_filter_dvd_log_div_le_half_log`,
  `TauCeti.le_sum_primesLE_floor_filter_not_dvd_log_div`: the constant-free `log n / 2` bound on the
  primes dividing `n`, and the resulting Mertens lower bound on primes `p ≤ x` coprime to `n`.
* `TauCeti.sum_primeFactors_eq_sum_lt_add_sum_ge`: splitting a sum over `n.primeFactors` at an
  arbitrary real cutoff `X` into `(p : ℝ) < X` and `X ≤ (p : ℝ)`.
* `TauCeti.sum_primeFactors_log_div_le_of_pos`: for `X > 0`,
  `∑_{p ∣ n} log p / p ≤ (∑_{p < X} log p / p) + log n / X`.
* `TauCeti.sum_primeFactors_log_div_le`: for every natural number `n`,
  `∑_{p ∣ n} log p / p ≤ log (log n) + log 4 + 5`.
* `TauCeti.sum_primeFactors_log_div_isBigO`:
  `∑_{p ∣ n} log p / p =O[atTop] log (log n)`.

## References

* A. N. Shankar, A. Shankar, Y. Tang, and S. Tayou, *Exceptional jumps of Picard ranks of
  reductions of K3 surfaces over number fields*, Forum Math. Pi 10 (2022), e21, proof of
  Proposition 5.2, p. 27.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-- For every natural number `n`, the sum of `log p` over the distinct prime divisors of `n` is at
most `log n`. -/
theorem sum_primeFactors_log_le_log (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    prod_pos fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hle : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  rw [← Real.log_prod
    (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  exact Real.log_le_log hpos hle

/-- For a squarefree integer `n`, the sum of `log p` over `n.primeFactors` equals `log n`. -/
theorem sum_primeFactors_log_eq_log {n : ℕ} (hn : Squarefree n) :
    ∑ p ∈ n.primeFactors, Real.log p = Real.log n := by
  rw [← Real.log_prod
    (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero),
    ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]

/-- Since every prime factor satisfies `p ≥ 2`, `∑_{p ∣ n} log p / p ≤ log n / 2` for every natural
number `n`. -/
theorem sum_primeFactors_log_div_le_half_log (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log n / 2 := by
  calc ∑ p ∈ n.primeFactors, Real.log p / p
      ≤ ∑ p ∈ n.primeFactors, Real.log p / 2 := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
        exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) zero_lt_two hp2
    _ = (∑ p ∈ n.primeFactors, Real.log p) / 2 := (sum_div _ _ _).symm
    _ ≤ Real.log n / 2 := div_le_div_of_nonneg_right (sum_primeFactors_log_le_log n) zero_le_two

/-- For `n ≠ 0`, the primes `p ≤ k` dividing `n` contribute at most `log n / 2` to `∑ log p / p`. -/
theorem sum_primesLE_filter_dvd_log_div_le_half_log (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ (Nat.primesLE k).filter (· ∣ n), Real.log p / p ≤ Real.log n / 2 := by
  refine (sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ ↦ ?_).trans
    (sum_primeFactors_log_div_le_half_log n)
  · intro p hp
    obtain ⟨hp_le, hdvd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hp_le, hdvd, hn⟩
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    exact div_nonneg (Real.log_nonneg hp1) (by positivity)

/-- **Mertens lower bound away from a modulus**: for real `x ≥ 0` and `n ≠ 0`,
`log x - log n / 2 - (3 / 2 + 2 log 4) ≤ ∑_{p ≤ x, ¬ p ∣ n} log p / p`. -/
theorem le_sum_primesLE_floor_filter_not_dvd_log_div {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    Real.log x - Real.log n / 2 - (3 / 2 + 2 * Real.log 4) ≤
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (¬ · ∣ n), Real.log p / p := by
  have hsplit := sum_filter_add_sum_filter_not (Nat.primesLE ⌊x⌋₊) (· ∣ n)
    (fun p : ℕ ↦ Real.log p / p)
  linarith [le_sum_primesLE_floor_log_div hx,
    sum_primesLE_filter_dvd_log_div_le_half_log ⌊x⌋₊ hn]

/-- Splitting a finite sum over the distinct prime divisors of `n` at a real cutoff `X`: an
endpoint prime `p = X` belongs to the upper sum `X ≤ (p : ℝ)`. -/
theorem sum_primeFactors_eq_sum_lt_add_sum_ge {M : Type*} [AddCommMonoid M] (n : ℕ) (X : ℝ)
    (f : ℕ → M) :
    ∑ p ∈ n.primeFactors, f p =
      (∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < X), f p) +
        ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), f p := by
  rw [← sum_filter_add_sum_filter_not n.primeFactors (fun p : ℕ ↦ (p : ℝ) < X)]
  congr 2
  ext p
  simp

/-- Every prime divisor of `n` strictly below `X` lies in `Nat.primesBelow ⌈X⌉₊`. -/
theorem primeFactors_filter_lt_subset_primesBelow_ceil (n : ℕ) (X : ℝ) :
    n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < X) ⊆ Nat.primesBelow ⌈X⌉₊ := by
  intro p hp
  obtain ⟨hp_mem, hp_lt⟩ := mem_filter.mp hp
  exact Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr hp_lt, Nat.prime_of_mem_primeFactors hp_mem⟩

/-- For `X > 0`, the prime divisors `p ∣ n` with `p ≥ X` contribute at most `log n / X` to
`∑ log p / p`. -/
theorem sum_primeFactors_log_div_ge_le (n : ℕ) {X : ℝ} (hX : 0 < X) :
    ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / p ≤ Real.log n / X := by
  calc ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / p
      ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ X ≤ (p : ℝ)), Real.log p / X := by
        refine sum_le_sum fun p hp ↦ ?_
        obtain ⟨hp_mem, hXp⟩ := mem_filter.mp hp
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp_mem).one_lt.le
        exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hX hXp
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p / X := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦ ?_
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
        exact div_nonneg (Real.log_nonneg hp1) hX.le
    _ = (∑ p ∈ n.primeFactors, Real.log p) / X := (sum_div _ _ _).symm
    _ ≤ Real.log n / X := div_le_div_of_nonneg_right (sum_primeFactors_log_le_log n) hX.le

/-- **Cutoff bound for the logarithmic weight of prime divisors**: for every `n` and every `X > 0`,
`∑_{p ∣ n} log p / p ≤ (∑_{p < X} log p / p) + log n / X`. -/
theorem sum_primeFactors_log_div_le_of_pos (n : ℕ) {X : ℝ} (hX : 0 < X) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤
      (∑ p ∈ Nat.primesBelow ⌈X⌉₊, Real.log p / p) + Real.log n / X := by
  rw [sum_primeFactors_eq_sum_lt_add_sum_ge n X]
  refine add_le_add ?_ (sum_primeFactors_log_div_ge_le n hX)
  refine sum_le_sum_of_subset_of_nonneg (primeFactors_filter_lt_subset_primesBelow_ceil n X)
    fun p hp _ ↦ ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

/-- **Logarithmic weight of prime divisors**: for every natural number `n`,
`∑_{p ∣ n} log p / p ≤ log (log n) + log 4 + 5`. This covers `n = 2` (where `log (log 2) < 0`) as
well as `n = 0, 1` (by `Real.log 0 = 0`). -/
theorem sum_primeFactors_log_div_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log p / p ≤ Real.log (Real.log n) + Real.log 4 + 5 := by
  rcases lt_or_ge n 2 with hn2 | hn
  · interval_cases n <;> simp only [Nat.primeFactors_zero, Nat.primeFactors_one, sum_empty,
      Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one, zero_add] <;>
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  rcases eq_or_lt_of_le hn with rfl | hn3
  · rw [Nat.Prime.primeFactors Nat.prime_two, sum_singleton, Nat.cast_two]
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hll2 : -Real.log 2 ≤ Real.log (Real.log 2) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h2
      rwa [one_div, Real.log_inv] at this
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [h4, Real.log_pow]
      ring
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · have hn_cast : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hlog3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have hlogn : 1 < Real.log n := hlog3.trans_le (Real.log_le_log (by norm_num) hn_cast)
    have hpos : 0 < Real.log n := by linarith
    calc ∑ p ∈ n.primeFactors, Real.log p / p
        ≤ (∑ p ∈ Nat.primesBelow ⌈Real.log n⌉₊, Real.log p / p) + Real.log n / Real.log n :=
          sum_primeFactors_log_div_le_of_pos n hpos
      _ ≤ (Real.log (Real.log n) + Real.log 4 + 4) + 1 := by
          rw [div_self hpos.ne']
          gcongr
          exact sum_primesBelow_ceil_log_div_le hlogn.le
      _ = Real.log (Real.log n) + Real.log 4 + 5 := by ring

/-- Asymptotic form of the prime-divisor bound:
`∑_{p ∣ n} log p / p = O(log log n)` as `n → ∞`. -/
theorem sum_primeFactors_log_div_isBigO :
    (fun n : ℕ ↦ ∑ p ∈ n.primeFactors, Real.log p / p) =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log n)) := by
  refine IsBigO.of_bound (Real.log 4 + 6) ?_
  filter_upwards [eventually_ge_atTop 16] with n hn
  have hn_cast : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : (16 : ℝ) = 2 ^ 4 := by norm_num
  have hlog16 : Real.exp 1 < Real.log 16 := by
    rw [h16, Real.log_pow]
    push_cast
    linarith [Real.exp_one_lt_d9, Real.log_two_gt_d9]
  have hlogn : Real.exp 1 < Real.log n :=
    hlog16.trans_le (Real.log_le_log (by norm_num) hn_cast)
  have hlln : 1 < Real.log (Real.log n) :=
    (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hlogn)).mpr hlogn
  have hsum_nonneg : 0 ≤ ∑ p ∈ n.primeFactors, Real.log p / p := by
    refine sum_nonneg fun p hp ↦ ?_
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    exact div_nonneg (Real.log_nonneg hp1) (by positivity)
  have hsum_le := sum_primeFactors_log_div_le n
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.norm_of_nonneg hsum_nonneg, Real.norm_of_nonneg (by linarith)]
  nlinarith

end TauCeti
