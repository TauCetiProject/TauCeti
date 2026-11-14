/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.Log.Factorial
import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
import TauCeti.NumberTheory.Chebyshev.LogFactorial

/-!
# Mertens' first theorem for rational primes

Chebyshev's identity `log ⌊x⌋₊! = ∑_{1 ≤ n ≤ x} Λ(n) ⌊x / n⌋₊`
(`Chebyshev.log_floor_factorial_eq_sum_vonMangoldt`) sandwiches `log ⌊x⌋₊!` between
`x ∑_{1 ≤ n ≤ x} Λ(n) / n - ψ(x)` and `x ∑_{1 ≤ n ≤ x} Λ(n) / n`. Combining the half-logarithmic
Stirling bounds on `log ⌊x⌋₊!` (`Real.log_floor_factorial_le`, `Real.le_log_floor_factorial`) with
Chebyshev's linear estimate `ψ(x) ≤ (log 4 + 4) x` (`Chebyshev.psi_le_const_mul_self`) proves
Mertens' first theorem in von Mangoldt form with explicit effective constants:
`log x - 3 / 2 ≤ ∑_{1 ≤ n ≤ x} Λ(n) / n ≤ log x + log 4 + 4` for `x ≥ 1`.

Subtracting the convergent higher-prime-power contribution (`≤ 2 log 4` by
`ArithmeticFunction.vonMangoldt.sum_Icc_nonprime_div_le_two_mul_log_four`) transfers the estimate
to Mathlib's finite set of primes `Nat.primesLE ⌊x⌋₊`:
`log x - (2 log 4 + 3 / 2) ≤ ∑_{p ≤ x} log p / p ≤ log x + log 4 + 4`, and in particular
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + 4` for `x ≥ 1` (since `2 log 4 + 3 / 2 ≤ log 4 + 4`).

Changing from the inclusive cutoff `p ≤ x` to the strict cutoff `p < x` drops at most one prime at
`x`, costing at most `log x / x ≤ 1 / 2` for `x ≥ 1`, so the same uniform bound `log 4 + 4` holds
for the strict cutoff and for `Nat.primesBelow n`. Splitting `Nat.primesLE ⌊x⌋₊` at an intermediate
real cutoff `y ≤ x` gives the interval form
`|∑_{y < p ≤ x} log p / p - log (x / y)| ≤ 2 (log 4 + 4)` for `1 ≤ y ≤ x`. As a consequence,
`∑_{p ≤ x} log p / p` diverges to `+∞` and the tail series `∑_{p ≥ y} log p / p` is not summable
for any `y`, contrasting with the `O(1 / y)` tail of `∑_{p ≥ y} log p / p ^ 2`.

## Main results

* `Nat.primesLE_filter_lt`: filtering `Nat.primesLE n` by `· < n` recovers `Nat.primesBelow n`.
* `Nat.prod_primesLE_floor_eq_mul_filter_gt`, `Nat.sum_primesLE_floor_eq_add_filter_gt`: splitting
  products and sums over `Nat.primesLE ⌊x⌋₊` at a real cutoff `y ≤ x`.
* `Chebyshev.log_floor_factorial_le_mul_sum_vonMangoldt_div`,
  `Chebyshev.mul_sum_vonMangoldt_div_sub_psi_le_log_floor_factorial`: the floor-replacement
  sandwich for `log ⌊x⌋₊!`.
* `Chebyshev.sum_vonMangoldt_div_le`, `Chebyshev.log_sub_le_sum_vonMangoldt_div`,
  `Chebyshev.abs_sum_vonMangoldt_div_sub_log_le`, `Chebyshev.isBigO_sum_vonMangoldt_div_sub_log`:
  Mertens' first theorem in von Mangoldt form.
* `Chebyshev.sum_primesLE_log_div_le`, `Chebyshev.log_sub_le_sum_primesLE_log_div`,
  `Chebyshev.abs_sum_primesLE_log_div_sub_log_le`,
  `Chebyshev.abs_sum_primesLE_nat_log_div_sub_log_le`,
  `Chebyshev.isBigO_sum_primesLE_log_div_sub_log`: Mertens' first theorem on `Nat.primesLE`.
* `Chebyshev.sum_primesLE_log_div_sub_filter_lt_le`,
  `Chebyshev.abs_sum_primesLE_filter_lt_log_div_sub_log_le`,
  `Chebyshev.abs_sum_primesBelow_log_div_sub_log_le`,
  `Chebyshev.isBigO_sum_primesLE_filter_lt_log_div_sub_log`: strict-cutoff comparison and Mertens'
  first theorem for `p < x` and `Nat.primesBelow n`.
* `Chebyshev.abs_sum_primesLE_filter_gt_log_div_sub_log_div_le`: interval Mertens estimate on
  `(y, x]`.
* `Chebyshev.tendsto_sum_primesLE_log_div_atTop`, `Chebyshev.not_summable_prime_log_div_ge`:
  divergence of the logarithmic prime sum and non-summability of its tails.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 3.4(a) and its proof, p. 40.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Theorem 425.
-/

public section

open Asymptotics Filter Finset ArithmeticFunction
open scoped Chebyshev Nat Topology

namespace Nat

/-- Filtering `Nat.primesLE n` by strict inequality `· < n` gives `Nat.primesBelow n`. -/
@[simp]
theorem primesLE_filter_lt (n : ℕ) :
    (primesLE n).filter (· < n) = primesBelow n := by
  ext p
  simp only [mem_filter, mem_primesLE, mem_primesBelow]
  exact ⟨fun ⟨⟨_, hp⟩, hlt⟩ ↦ ⟨hlt, hp⟩, fun ⟨hlt, hp⟩ ↦ ⟨⟨hlt.le, hp⟩, hlt⟩⟩

/-- For `y ≤ x`, the product over the primes `p ≤ x` splits into the product over `p ≤ y` and the
product over `y < p ≤ x`, with any prime at `y` retained in the lower part. -/
@[to_additive /-- For `y ≤ x`, the sum over the primes `p ≤ x` splits into the sum over `p ≤ y` and
the sum over `y < p ≤ x`, with any prime at `y` retained in the lower part. -/]
theorem prod_primesLE_floor_eq_mul_filter_gt {M : Type*} [CommMonoid M] (f : ℕ → M)
    {y x : ℝ} (hyx : y ≤ x) :
    ∏ p ∈ primesLE ⌊x⌋₊, f p =
      (∏ p ∈ primesLE ⌊y⌋₊, f p) *
        ∏ p ∈ (primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), f p := by
  rcases lt_or_ge y 0 with hy | hy
  · have hfy : ⌊y⌋₊ = 0 := floor_of_nonpos hy.le
    have hfilt : (primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)) = primesLE ⌊x⌋₊ :=
      filter_eq_self.mpr fun p _ ↦ hy.trans_le (cast_nonneg p)
    rw [hfy, primesLE_zero, prod_empty, one_mul, hfilt]
  · have hle : primesLE ⌊y⌋₊ = (primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ ¬y < (p : ℝ)) := by
      ext p
      simp only [mem_primesLE, mem_filter, not_lt, le_floor_iff hy, le_floor_iff (hy.trans hyx)]
      exact ⟨fun ⟨hpy, hp⟩ ↦ ⟨⟨hpy.trans hyx, hp⟩, hpy⟩, fun ⟨⟨_, hp⟩, hpy⟩ ↦ ⟨hpy, hp⟩⟩
    rw [hle, mul_comm, prod_filter_mul_prod_filter_not]

end Nat

namespace Chebyshev

private theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos zero_lt_two]
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  norm_num
  linarith

private theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : Real.log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos zero_lt_two]
  have h := Real.log_le_sub_one_of_pos (half_pos hx)
  rw [Real.log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith

/-! ### Floor-replacement bounds and the von Mangoldt sum -/

/-- Upper floor replacement in Chebyshev's identity: `log ⌊x⌋₊! ≤ x ∑_{1 ≤ n ≤ x} Λ(n) / n` for
every real `x`. -/
theorem log_floor_factorial_le_mul_sum_vonMangoldt_div (x : ℝ) :
    Real.log ⌊x⌋₊ ! ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
  rcases lt_or_ge x 0 with hx | hx
  · simp [Nat.floor_of_nonpos hx.le]
  rw [log_floor_factorial_eq_sum_vonMangoldt, mul_sum]
  refine sum_le_sum fun n _ ↦ ?_
  calc Λ n * (⌊x / n⌋₊ : ℝ) ≤ Λ n * (x / n) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg n)))
          vonMangoldt_nonneg
    _ = x * (Λ n / n) := by ring

/-- Lower floor replacement in Chebyshev's identity:
`x ∑_{1 ≤ n ≤ x} Λ(n) / n - ψ(x) ≤ log ⌊x⌋₊!` for every real `x`. -/
theorem mul_sum_vonMangoldt_div_sub_psi_le_log_floor_factorial (x : ℝ) :
    x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - ψ x ≤ Real.log ⌊x⌋₊ ! := by
  rw [log_floor_factorial_eq_sum_vonMangoldt, psi, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun n _ ↦ ?_
  calc x * (Λ n / n) - Λ n = Λ n * (x / n - 1) := by ring
    _ ≤ Λ n * (⌊x / n⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.sub_one_lt_floor (x / n)).le vonMangoldt_nonneg

/-- Explicit upper bound in Mertens' first theorem for `Λ`: for `x ≥ 1`,
`∑_{1 ≤ n ≤ x} Λ(n) / n ≤ log x + log 4 + 4`. -/
theorem sum_vonMangoldt_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n ≤ Real.log x + (Real.log 4 + 4) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1 := mul_sum_vonMangoldt_div_sub_psi_le_log_floor_factorial x
  have h2 := Real.log_floor_factorial_le hx
  have h3 := psi_le_const_mul_self hx0.le
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith

/-- Explicit lower bound in Mertens' first theorem for `Λ`: for `x ≥ 0`,
`log x - 3 / 2 ≤ ∑_{1 ≤ n ≤ x} Λ(n) / n`. -/
theorem log_sub_le_sum_vonMangoldt_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - 3 / 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx hx1.le
    simp only [hfl, Ioc_self, sum_empty]
    linarith
  · have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have h1 := Real.le_log_floor_factorial hx1
    have h2 := log_floor_factorial_le_mul_sum_vonMangoldt_div x
    have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
    have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
    refine le_of_mul_le_mul_left ?_ hx0
    nlinarith

/-- **Mertens' first theorem, von Mangoldt form.** For every real `x ≥ 1`,
`|∑_{1 ≤ n ≤ x} Λ(n) / n - log x| ≤ log 4 + 4`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ Real.log 4 + 4 := by
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_sub_le_iff]
  exact ⟨by linarith [sum_vonMangoldt_div_le hx],
    by linarith [log_sub_le_sum_vonMangoldt_div (zero_le_one.trans hx)]⟩

/-- Asymptotic form of Mertens' first theorem for `Λ`:
`∑_{1 ≤ n ≤ x} Λ(n) / n - log x = O(1)` as `x → ∞`. -/
theorem isBigO_sum_vonMangoldt_div_sub_log :
    (fun x : ℝ ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x) =O[atTop] (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  simpa using abs_sum_vonMangoldt_div_sub_log_le hx

/-! ### Passage from `Λ(n) / n` to primes `Nat.primesLE` -/

/-- Decomposition of the finite von Mangoldt sum `∑_{1 ≤ n ≤ N} Λ(n) / n` into its prime part on
`Nat.primesLE N` and its higher-prime-power remainder. -/
theorem sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n / n =
      (∑ p ∈ Nat.primesLE N, Real.log p / p) +
        ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else Λ n) / n := by
  rw [← sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime]
  congr 1
  · have hset : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
      ext p
      simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
      exact ⟨fun ⟨⟨_, hN⟩, hp⟩ ↦ ⟨hN, hp⟩, fun ⟨hN, hp⟩ ↦ ⟨⟨hp.pos, hN⟩, hp⟩⟩
    rw [hset]
    exact sum_congr rfl fun p hp ↦ by rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
  · rw [sum_filter]
    refine sum_congr rfl fun n _ ↦ ?_
    split_ifs <;> simp

/-- The prime sum `∑_{p ≤ x} log p / p` is at most the von Mangoldt sum `∑_{1 ≤ n ≤ x} Λ(n) / n`. -/
theorem sum_primesLE_log_div_le_sum_vonMangoldt_div (x : ℝ) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
  rw [sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add]
  refine le_add_of_nonneg_right (sum_nonneg fun n _ ↦ ?_)
  exact div_nonneg (by split_ifs <;> simp [vonMangoldt_nonneg]) (Nat.cast_nonneg n)

/-- The difference between the von Mangoldt sum and the prime sum up to `x` is at most `2 log 4`. -/
theorem sum_vonMangoldt_div_sub_sum_primesLE_log_div_le (x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ 2 * Real.log 4 := by
  rw [sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add, add_sub_cancel_left]
  have hIoc : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := rfl
  rw [hIoc]
  exact vonMangoldt.sum_Icc_nonprime_div_le_two_mul_log_four ⌊x⌋₊

/-! ### Mertens' first theorem on `Nat.primesLE` -/

/-- Explicit upper bound in Mertens' first theorem: for `x ≥ 1`,
`∑_{p ≤ x} log p / p ≤ log x + log 4 + 4`. -/
theorem sum_primesLE_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ Real.log x + (Real.log 4 + 4) :=
  (sum_primesLE_log_div_le_sum_vonMangoldt_div x).trans (sum_vonMangoldt_div_le hx)

/-- Explicit lower bound in Mertens' first theorem: for `x ≥ 0`,
`log x - (2 log 4 + 3 / 2) ≤ ∑_{p ≤ x} log p / p`. -/
theorem log_sub_le_sum_primesLE_log_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - (2 * Real.log 4 + 3 / 2) ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p := by
  linarith [log_sub_le_sum_vonMangoldt_div hx, sum_vonMangoldt_div_sub_sum_primesLE_log_div_le x]

/-- **Mertens' first theorem.** For every real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + 4`. -/
theorem abs_sum_primesLE_log_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - Real.log x| ≤ Real.log 4 + 4 := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [sum_primesLE_log_div_le hx],
    by linarith [log_sub_le_sum_primesLE_log_div (zero_le_one.trans hx), log_four_le_two]⟩

/-- Natural-cutoff form of Mertens' first theorem: for every `n : ℕ`,
`|∑_{p ≤ n} log p / p - log n| ≤ log 4 + 4`. -/
theorem abs_sum_primesLE_nat_log_div_sub_log_le (n : ℕ) :
    |(∑ p ∈ Nat.primesLE n, Real.log p / p) - Real.log n| ≤ Real.log 4 + 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [Nat.primesLE_zero, sum_empty, Nat.cast_zero, Real.log_zero, sub_self, abs_zero]
    linarith
  · simpa [Nat.floor_natCast] using
      abs_sum_primesLE_log_div_sub_log_le (x := n) (mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- Asymptotic form of Mertens' first theorem on `Nat.primesLE`:
`∑_{p ≤ x} log p / p - log x = O(1)` as `x → ∞`. -/
theorem isBigO_sum_primesLE_log_div_sub_log :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - Real.log x) =O[atTop]
      (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  simpa using abs_sum_primesLE_log_div_sub_log_le hx

/-! ### Strict prime cutoffs `p < x`, `Nat.primesBelow`, and intervals `(y, x]` -/

/-- Replacing the inclusive cutoff `p ≤ x` by the strict cutoff `p < x` does not increase the
logarithmic prime sum. -/
theorem sum_primesLE_filter_lt_log_div_le (x : ℝ) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦
    div_nonneg (Real.log_nonneg (mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
      (Nat.cast_nonneg p)

/-- Changing from the inclusive cutoff `p ≤ x` to the strict cutoff `p < x` removes at most a
single prime at `x`, costing at most `log x / x` for `x ≥ 1`. -/
theorem sum_primesLE_log_div_sub_filter_lt_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) -
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p) ≤
        Real.log x / x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE ⌊x⌋₊) (fun p : ℕ ↦ (p : ℝ) < x),
    add_sub_cancel_left]
  by_cases hmem : ∃ p ∈ Nat.primesLE ⌊x⌋₊, ¬(p : ℝ) < x
  · obtain ⟨q, hq, hq_ge⟩ := hmem
    have hq_le : (q : ℝ) ≤ x := (Nat.le_floor_iff hx0).mp (Nat.le_of_mem_primesLE hq)
    have hqx : (q : ℝ) = x := le_antisymm hq_le (not_lt.mp hq_ge)
    have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ ¬(p : ℝ) < x) ⊆ {q} := by
      intro p hp
      obtain ⟨hp_mem, hp_ge⟩ := mem_filter.mp hp
      have hp_le : (p : ℝ) ≤ x := (Nat.le_floor_iff hx0).mp (Nat.le_of_mem_primesLE hp_mem)
      have hpx : (p : ℝ) = x := le_antisymm hp_le (not_lt.mp hp_ge)
      exact mem_singleton.mpr (Nat.cast_injective (hpx.trans hqx.symm))
    refine (sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ ?_).trans ?_
    · exact div_nonneg (Real.log_nonneg (mod_cast
        (mem_singleton.mp hp ▸ Nat.prime_of_mem_primesLE hq).one_lt.le)) (Nat.cast_nonneg p)
    · rw [sum_singleton, hqx]
  · rw [filter_eq_empty_iff.mpr fun p hp hp_ge ↦ hmem ⟨p, hp, hp_ge⟩, sum_empty]
    exact div_nonneg (Real.log_nonneg hx) hx0

/-- Explicit upper bound for the strict-cutoff prime sum: for `x ≥ 1`,
`∑_{p < x} log p / p ≤ log x + log 4 + 4`. -/
theorem sum_primesLE_filter_lt_log_div_le_log_add {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p ≤
      Real.log x + (Real.log 4 + 4) :=
  (sum_primesLE_filter_lt_log_div_le x).trans (sum_primesLE_log_div_le hx)

/-- Explicit lower bound for the strict-cutoff prime sum: for `x ≥ 0`,
`log x - (2 log 4 + 2) ≤ ∑_{p < x} log p / p`. -/
theorem log_sub_le_sum_primesLE_filter_lt_log_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - (2 * Real.log 4 + 2) ≤
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx hx1.le
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hfl, Nat.primesLE_zero, filter_empty, sum_empty]
    linarith
  · linarith [log_sub_le_sum_primesLE_log_div hx, sum_primesLE_log_div_sub_filter_lt_le hx1,
      log_div_self_le_half hx]

/-- **Mertens' first theorem, strict cutoff.** For every real `x ≥ 1`,
`|∑_{p < x} log p / p - log x| ≤ log 4 + 4`. -/
theorem abs_sum_primesLE_filter_lt_log_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p) - Real.log x| ≤
      Real.log 4 + 4 := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [sum_primesLE_filter_lt_log_div_le_log_add hx],
    by linarith [log_sub_le_sum_primesLE_filter_lt_log_div (zero_le_one.trans hx),
      log_four_le_two]⟩

/-- Strict natural-cutoff form of Mertens' first theorem: for every `n : ℕ`,
`|∑_{p ∈ Nat.primesBelow n} log p / p - log n| ≤ log 4 + 4`. -/
theorem abs_sum_primesBelow_log_div_sub_log_le (n : ℕ) :
    |(∑ p ∈ Nat.primesBelow n, Real.log p / p) - Real.log n| ≤ Real.log 4 + 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [Nat.primesBelow_zero, sum_empty, Nat.cast_zero, Real.log_zero, sub_self, abs_zero]
    linarith
  · simpa [Nat.floor_natCast] using
      abs_sum_primesLE_filter_lt_log_div_sub_log_le (x := n)
        (mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- Asymptotic form of Mertens' first theorem with strict cutoff:
`∑_{p < x} log p / p - log x = O(1)` as `x → ∞`. -/
theorem isBigO_sum_primesLE_filter_lt_log_div_sub_log :
    (fun x : ℝ ↦
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x), Real.log p / p) - Real.log x)
      =O[atTop] (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  simpa using abs_sum_primesLE_filter_lt_log_div_sub_log_le hx

/-- **Interval form of Mertens' first theorem.** For `1 ≤ y ≤ x`,
`|∑_{y < p ≤ x} log p / p - log (x / y)| ≤ 2 (log 4 + 4)`. -/
theorem abs_sum_primesLE_filter_gt_log_div_sub_log_div_le {y x : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    |(∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log p / p) -
        Real.log (x / y)| ≤ 2 * (Real.log 4 + 4) := by
  have hx : 1 ≤ x := hy.trans hyx
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsplit := Nat.sum_primesLE_floor_eq_add_filter_gt (fun p : ℕ ↦ Real.log p / p) hyx
  have hdiff :
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log p / p) -
        Real.log (x / y) =
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - Real.log x) -
        ((∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / p) - Real.log y) := by
    rw [Real.log_div hx0.ne' hy0.ne']
    linarith
  rw [hdiff]
  exact (abs_sub _ _).trans (by linarith [abs_sum_primesLE_log_div_sub_log_le hx,
    abs_sum_primesLE_log_div_sub_log_le hy])

/-! ### Divergence of the logarithmic prime sum and its tails -/

/-- The logarithmic prime sum `∑_{p ≤ x} log p / p` diverges to `+∞` as `x → ∞`. -/
theorem tendsto_sum_primesLE_log_div_atTop :
    Tendsto (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-(2 * Real.log 4 + 3 / 2)) Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop 0] with x hx
  simpa [sub_eq_add_neg] using log_sub_le_sum_primesLE_log_div hx

/-- For every real `y`, the prime tail `∑_{p ≥ y} log p / p` is not summable, contrasting with the
`O(1 / y)` summability of `∑_{p ≥ y} log p / p ^ 2`. -/
theorem not_summable_prime_log_div_ge (y : ℝ) :
    ¬Summable (fun n : ℕ ↦ if n.Prime ∧ y ≤ (n : ℝ) then Real.log n / n else 0) := by
  intro hsum
  set B := (∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / p) +
    ∑' n : ℕ, (if n.Prime ∧ y ≤ (n : ℝ) then Real.log n / n else 0)
  have hub (x : ℝ) (hx : max 1 y ≤ x) : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ B := by
    dsimp only [B]
    rw [Nat.sum_primesLE_floor_eq_add_filter_gt _ ((le_max_right 1 y).trans hx)]
    gcongr
    refine (sum_le_sum fun p hp ↦ ?_).trans
      (hsum.sum_le_tsum _ fun n _ ↦ by split_ifs <;> positivity)
    obtain ⟨hp_mem, hpy⟩ := mem_filter.mp hp
    simp [Nat.prime_of_mem_primesLE hp_mem, hpy.le]
  have hdiv := (tendsto_atTop.mp tendsto_sum_primesLE_log_div_atTop (B + 1)).and
    (eventually_ge_atTop (max 1 y))
  obtain ⟨x, hgt, hx⟩ := hdiv.exists
  linarith [hub x hx]

end Chebyshev
