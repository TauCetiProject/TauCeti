/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Terminating ascending-Pochhammer series

At a nonpositive integer `-n` (`n : ℕ`), the ascending Pochhammer polynomial `ascPochhammer R m`
vanishes for all `m > n` (`ascPochhammer_eval_neg_natCast_of_lt`), and over a division ring of
characteristic zero its normalized coefficient `(-1) ^ m * (-n)_m / m!` equals the binomial
coefficient `n.choose m` (`TauCeti.neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial`).

Consequently, any infinite series indexed by `m : ℕ` whose `m`-th term carries the factor
`(ascPochhammer R m).eval (-(n : R))` has finite support contained in `Finset.range (n + 1)`: it
converges unconditionally (`HasSum`) in any topological space without continuity or radius
hypotheses, depends on any accompanying sequence factor only on `m ≤ n`, and has unconditionally
summable norms in any seminormed ring or normed division ring. This provides the shared analytic
reduction for terminating hypergeometric, binomial, and orthogonal-polynomial addition series.

## Main results

* `TauCeti.hasSum_ascPochhammer_eval_neg_natCast_mul_of_eq_on_le` and
  `TauCeti.hasSum_ascPochhammer_eval_neg_natCast_mul`: unconditional `HasSum` to the
  `Finset.range (n + 1)` sum for `m ↦ (-n)_m * f m`.
* `TauCeti.hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul_of_eq_on_le`,
  `TauCeti.hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul`, and
  `TauCeti.hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_div_pow_of_eq_on_le`:
  over a characteristic-zero division ring (or field for the homogeneous `(s / c) ^ m` form),
  unconditional `HasSum` of terminating normalized Pochhammer series to finite binomial sums.
* `TauCeti.summable_norm_ascPochhammer_eval_neg_natCast_mul` and
  `TauCeti.summable_norm_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul`:
  unconditional norm summability in any seminormed ring or normed division ring.

## References

* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. I, §2.1.
* NIST Digital Library of Mathematical Functions, [§5.2(iii)](https://dlmf.nist.gov/5.2#iii) and
  [§16.2(ii)](https://dlmf.nist.gov/16.2#ii).
-/

public section

namespace TauCeti

open Polynomial
open scoped Nat

/-- At a nonpositive integer `-n`, `(ascPochhammer R m).eval (-n)` vanishes for `m > n`, so any
series `m ↦ (-n)_m * f m` sums unconditionally to its finite prefix over `Finset.range (n + 1)` and
depends on `f` only for `m ≤ n`. -/
theorem hasSum_ascPochhammer_eval_neg_natCast_mul_of_eq_on_le
    {R : Type*} [Ring R] [TopologicalSpace R] (n : ℕ) {f g : ℕ → R}
    (hfg : ∀ m ≤ n, f m = g m) :
    HasSum (fun m : ℕ => (ascPochhammer R m).eval (-(n : R)) * f m)
      (∑ m ∈ Finset.range (n + 1), (ascPochhammer R m).eval (-(n : R)) * g m) := by
  have hfin : HasSum (fun m : ℕ => (ascPochhammer R m).eval (-(n : R)) * f m)
      (∑ m ∈ Finset.range (n + 1), (ascPochhammer R m).eval (-(n : R)) * f m) := by
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    have hlt : n < m :=
      Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    rw [ascPochhammer_eval_neg_natCast_of_lt hlt, zero_mul]
  refine Eq.mp ?_ hfin
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hfg m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]

/-- Unconditional `HasSum` for a terminating ascending-Pochhammer series `m ↦ (-n)_m * f m`. -/
theorem hasSum_ascPochhammer_eval_neg_natCast_mul
    {R : Type*} [Ring R] [TopologicalSpace R] (n : ℕ) (f : ℕ → R) :
    HasSum (fun m : ℕ => (ascPochhammer R m).eval (-(n : R)) * f m)
      (∑ m ∈ Finset.range (n + 1), (ascPochhammer R m).eval (-(n : R)) * f m) :=
  hasSum_ascPochhammer_eval_neg_natCast_mul_of_eq_on_le n fun _ _ => rfl

/-- Over a division ring of characteristic zero, the terminating normalized Pochhammer series
`m ↦ ((-1) ^ m * (-n)_m / m!) * f m` sums unconditionally to the binomial sum
`∑_{m=0}^n C(n, m) * g m` whenever `f` and `g` agree for `m ≤ n`. -/
theorem hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul_of_eq_on_le
    {K : Type*} [DivisionRing K] [CharZero K] [TopologicalSpace K] (n : ℕ) {f g : ℕ → K}
    (hfg : ∀ m ≤ n, f m = g m) :
    HasSum (fun m : ℕ =>
      (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) * f m)
      (∑ m ∈ Finset.range (n + 1), (n.choose m : K) * g m) := by
  simp_rw [neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial]
  have hfin : HasSum (fun m : ℕ => (n.choose m : K) * f m)
      (∑ m ∈ Finset.range (n + 1), (n.choose m : K) * f m) := by
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    have hlt : n < m :=
      Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
  refine Eq.mp ?_ hfin
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hfg m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]

/-- Over a division ring of characteristic zero, the terminating normalized Pochhammer series
`m ↦ ((-1) ^ m * (-n)_m / m!) * f m` sums unconditionally to
`∑_{m=0}^n C(n, m) * f m`. -/
theorem hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul
    {K : Type*} [DivisionRing K] [CharZero K] [TopologicalSpace K] (n : ℕ) (f : ℕ → K) :
    HasSum (fun m : ℕ =>
      (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) * f m)
      (∑ m ∈ Finset.range (n + 1), (n.choose m : K) * f m) :=
  hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul_of_eq_on_le n
    fun _ _ => rfl

/-- Over a field of characteristic zero, for `c ≠ 0`, scaling a terminating normalized Pochhammer
series in `s / c` by `c ^ n` clears the denominators on `m ≤ n` and sums unconditionally to the
homogeneous binomial sum `∑_{m=0}^n C(n, m) * c ^ (n - m) * s ^ m * g m`. -/
theorem hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_div_pow_of_eq_on_le
    {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] (n : ℕ) {c : K} (hc : c ≠ 0) (s : K)
    {f g : ℕ → K} (hfg : ∀ m ≤ n, f m = g m) :
    HasSum (fun m : ℕ =>
      c ^ n * ((-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K)) *
        (s / c) ^ m * f m)
      (∑ m ∈ Finset.range (n + 1), (n.choose m : K) * c ^ (n - m) * s ^ m * g m) := by
  have h := hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul_of_eq_on_le n
    (f := fun m => c ^ n * (s / c) ^ m * f m)
    (g := fun m => c ^ (n - m) * s ^ m * g m) fun m hm => by
      have hpow : c ^ n = c ^ (n - m) * c ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
      rw [hpow, div_pow, mul_assoc (c ^ (n - m)), mul_div_cancel₀ _ (pow_ne_zero m hc), hfg m hm]
  refine Eq.mp ?_ h
  congr 1
  · ext m; ring
  · exact Finset.sum_congr rfl fun m _ => by ring

/-- Homogeneous terminating normalized Pochhammer `HasSum` in `s / c` scaled by `c ^ n`
(`c ≠ 0`). -/
theorem hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_div_pow
    {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] (n : ℕ) {c : K} (hc : c ≠ 0) (s : K)
    (f : ℕ → K) :
    HasSum (fun m : ℕ =>
      c ^ n * ((-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K)) *
        (s / c) ^ m * f m)
      (∑ m ∈ Finset.range (n + 1), (n.choose m : K) * c ^ (n - m) * s ^ m * f m) :=
  hasSum_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_div_pow_of_eq_on_le n hc s
    fun _ _ => rfl

/-- In any seminormed ring, a terminating ascending-Pochhammer series `m ↦ (-n)_m * f m` is
unconditionally norm-summable because all terms with `m > n` vanish. -/
theorem summable_norm_ascPochhammer_eval_neg_natCast_mul
    {R : Type*} [SeminormedRing R] (n : ℕ) (f : ℕ → R) :
    Summable fun m : ℕ => ‖(ascPochhammer R m).eval (-(n : R)) * f m‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun m hm => ?_
  have hlt : n < m :=
    Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  rw [ascPochhammer_eval_neg_natCast_of_lt hlt, zero_mul, norm_zero]

/-- In any normed division ring, the terminating normalized Pochhammer series
`m ↦ ((-1) ^ m * (-n)_m / m!) * f m` is unconditionally norm-summable. -/
theorem summable_norm_neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial_mul
    {K : Type*} [NormedDivisionRing K] (n : ℕ) (f : ℕ → K) :
    Summable fun m : ℕ =>
      ‖(-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) * f m‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun m hm => ?_
  have hlt : n < m :=
    Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  rw [ascPochhammer_eval_neg_natCast_of_lt hlt, mul_zero, zero_div, zero_mul, norm_zero]

end TauCeti
