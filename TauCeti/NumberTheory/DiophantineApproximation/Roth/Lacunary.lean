/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem

/-!
# Transcendence of lacunary series `∑ b ^ (-c ^ k)`

For integers `b ≥ 2` and `c ≥ 2`, the series `ξ = ∑_{k ≥ 1} b ^ (-c ^ k)` is very well
approximated by its partial sums: the sum of the terms with `k ≤ K` is a fraction with
denominator `n = b ^ (c ^ K)`, and the remaining tail is positive and at most
`2 b ^ (-c ^ (K + 1)) = 2 n ^ (-c)`. Hence `ξ` is a Liouville number with exponent `c`
(`TauCeti.liouvilleWith_tsum_inv_pow_pow`), so it is irrational. When `c ≥ 3` the exponent
exceeds `2`, and Roth's theorem in the form `IsAlgebraic.not_liouvilleWith` shows that `ξ` is
transcendental (`TauCeti.transcendental_tsum_inv_pow_pow`). The case `c = 3` is Evertse's
exercise.

Unlike Liouville's number `∑ b ^ (-k!)`, whose transcendence follows from Liouville's
inequality, these series are only shown to be Liouville numbers with the fixed exponent `c`.
Liouville's inequality then excludes algebraic numbers of degree less than `c` only, while Roth's
theorem excludes every algebraic number.

## Main results

* `TauCeti.liouvilleWith_tsum_inv_pow_pow`: `∑_{k ≥ 1} b ^ (-c ^ k)` is a Liouville number with
  exponent `c`.
* `TauCeti.irrational_tsum_inv_pow_pow`: it is irrational when `c ≥ 2`.
* `TauCeti.transcendental_tsum_inv_pow_pow`: it is transcendental when `c ≥ 3`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), chapter 6, Exercise 6.5.
-/

public section

open Filter Finset

namespace TauCeti

variable {b c : ℕ}

/-- The terms of the lacunary series are summable. -/
private theorem summable_inv_pow_pow (hb : 2 ≤ b) (hc : 2 ≤ c) :
    Summable fun k : ℕ ↦ ((b : ℝ)⁻¹) ^ c ^ (k + 1) := by
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hb)
  refine (summable_geometric_of_lt_one hr0 hr1).of_nonneg_of_le (fun _ ↦ by positivity)
    fun k ↦ pow_le_pow_of_le_one hr0 hr1.le ?_
  exact (Nat.lt_pow_self (by omega : 1 < c)).le.trans (Nat.pow_le_pow_right (by omega) k.le_succ)

/-- The tail of the lacunary series after `K` terms is at most twice its first term.

This follows the proof of `LiouvilleNumber.remainder_lt'` and `LiouvilleNumber.aux_calc` in
Mathlib (comparison with a geometric series). -/
private theorem tsum_inv_pow_pow_add_le (hb : 2 ≤ b) (hc : 2 ≤ c) (K : ℕ) :
    ∑' k : ℕ, ((b : ℝ)⁻¹) ^ c ^ (k + K + 1) ≤ 2 * ((b : ℝ)⁻¹) ^ c ^ (K + 1) := by
  set r : ℝ := (b : ℝ)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hb)
  -- Each exponent `c ^ (k + K + 1)` is at least `c ^ (K + 1) + k`, so the tail is dominated by
  -- a geometric series with ratio `r = 1 / b ≤ 1 / 2`.
  have hexp (k : ℕ) : c ^ (K + 1) + k ≤ c ^ (k + K + 1) := by
    have hk : k + 1 ≤ c ^ k := Nat.lt_pow_self (by omega)
    have h1 : 1 ≤ c ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
    rw [show k + K + 1 = (K + 1) + k by ring, pow_add c (K + 1) k]
    nlinarith
  calc ∑' k : ℕ, r ^ c ^ (k + K + 1)
      ≤ ∑' k : ℕ, r ^ c ^ (K + 1) * r ^ k := by
        refine Summable.tsum_le_tsum (fun k ↦ ?_)
          ((summable_nat_add_iff K).2 (summable_inv_pow_pow hb hc))
          ((summable_geometric_of_lt_one hr0 hr1).mul_left _)
        rw [← pow_add]
        exact pow_le_pow_of_le_one hr0 hr1.le (hexp k)
    _ = r ^ c ^ (K + 1) * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ r ^ c ^ (K + 1) * 2 := by
        gcongr
        simpa [r] using sub_one_div_inv_le_two (a := (b : ℝ)) (by exact_mod_cast hb)
    _ = 2 * r ^ c ^ (K + 1) := mul_comm _ _

/-- The sum of the first `K` terms of the lacunary series is a fraction with denominator
`b ^ (c ^ K)`. -/
private theorem sum_range_inv_pow_pow_eq (hb : 2 ≤ b) (hc : 1 ≤ c) (K : ℕ) :
    ∑ k ∈ range K, ((b : ℝ)⁻¹) ^ c ^ (k + 1) =
      ((∑ k ∈ range K, b ^ (c ^ K - c ^ (k + 1)) : ℕ) : ℝ) / ((b ^ c ^ K : ℕ) : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [pow_sub₀ _ hb0 (Nat.pow_le_pow_right hc (mem_range.1 hk)), inv_pow]
  field_simp

/-- **Lacunary series are Liouville numbers.** For integers `b ≥ 2` and `c`, the number
`∑_{k ≥ 1} b ^ (-c ^ k)` is a Liouville number with exponent `c`. When `c ≥ 2`, its partial
sums with denominator `n = b ^ (c ^ K)` approximate it within `3 / n ^ c`. When `c ≤ 1` the
statement holds trivially, since every real number is a Liouville number with exponent `1`. -/
theorem liouvilleWith_tsum_inv_pow_pow (hb : 2 ≤ b) (c : ℕ) :
    LiouvilleWith c (∑' k : ℕ, ((b : ℝ)⁻¹) ^ c ^ (k + 1)) := by
  rcases lt_or_ge c 2 with hc | hc
  · exact (liouvilleWith_one _).mono (by exact_mod_cast Nat.le_of_lt_succ hc)
  refine ⟨3, frequently_atTop.2 fun N ↦ ⟨b ^ c ^ N, ?_, ?_⟩⟩
  · exact (Nat.lt_pow_self (by omega)).le.trans (Nat.lt_pow_self (by omega)).le
  have hsum := summable_inv_pow_pow hb hc
  -- Split off the first `N` terms; the tail is positive and at most `2 / n ^ c`, where
  -- `n = b ^ c ^ N` is the denominator of the partial sum.
  refine ⟨(∑ k ∈ range N, b ^ (c ^ N - c ^ (k + 1)) : ℕ), ?_⟩
  rw [Int.cast_natCast, ← sum_range_inv_pow_pow_eq hb (by omega), ← hsum.sum_add_tsum_nat_add N,
    add_sub_cancel_left]
  have htail : 0 < ∑' k : ℕ, ((b : ℝ)⁻¹) ^ c ^ (k + N + 1) :=
    ((summable_nat_add_iff N).2 hsum).tsum_pos (fun _ ↦ by positivity) 0 (by positivity)
  have hpow : ((b : ℝ)⁻¹) ^ c ^ (N + 1) = 1 / ((b ^ c ^ N : ℕ) : ℝ) ^ (c : ℝ) := by
    simp [← pow_mul, ← pow_succ]
  refine ⟨add_ne_left.2 htail.ne', ?_⟩
  rw [abs_of_pos htail]
  calc _ ≤ 2 * ((b : ℝ)⁻¹) ^ c ^ (N + 1) := tsum_inv_pow_pow_add_le hb hc N
    _ < 3 / ((b ^ c ^ N : ℕ) : ℝ) ^ (c : ℝ) := by
        rw [hpow]
        have : (0 : ℝ) < ((b ^ c ^ N : ℕ) : ℝ) ^ (c : ℝ) := by positivity
        rw [mul_one_div]
        gcongr
        norm_num

/-- For integers `b ≥ 2` and `c ≥ 2`, the number `∑_{k ≥ 1} b ^ (-c ^ k)` is irrational. -/
theorem irrational_tsum_inv_pow_pow (hb : 2 ≤ b) (hc : 2 ≤ c) :
    Irrational (∑' k : ℕ, ((b : ℝ)⁻¹) ^ c ^ (k + 1)) :=
  (liouvilleWith_tsum_inv_pow_pow hb c).irrational (by exact_mod_cast hc)

/-- **Transcendence of lacunary series** (Evertse, Exercise 6.5, for `c = 3`). For integers
`b ≥ 2` and `c ≥ 3`, the number `∑_{k ≥ 1} b ^ (-c ^ k)` is transcendental. -/
theorem transcendental_tsum_inv_pow_pow (hb : 2 ≤ b) (hc : 3 ≤ c) :
    Transcendental ℚ (∑' k : ℕ, ((b : ℝ)⁻¹) ^ c ^ (k + 1)) := fun h ↦
  h.not_liouvilleWith (by exact_mod_cast hc) (liouvilleWith_tsum_inv_pow_pow hb c)

end TauCeti
