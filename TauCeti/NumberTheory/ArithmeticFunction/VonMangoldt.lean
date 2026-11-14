/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.SumPrimePow

/-!
# The von Mangoldt function at the higher prime powers

The weights `Λ(n) / n` at the non-prime `n` are supported on the prime powers `p ^ k` with
`k ≥ 2`, and their sum `∑ₚ ∑_{k ≥ 2} log p / p ^ k = ∑ₚ log p / (p (p - 1))` is finite and at
most `2 log 4`. This explicit absolute constant bounds the higher-prime-power part of every
twisted von Mangoldt series on `1 ≤ re s` and separates the prime and von Mangoldt forms of
Mertens' first theorem.

The summability is the trivial residue class case of Mathlib's
`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`; the explicit bound regroups
by the prime base (`Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log`), sums each geometric tail to
`1 / (p (p - 1)) ≤ 2 / p ^ 2`, and applies Chebyshev's reciprocal-square prime tail bound
(`TauCeti.sum_log_div_sq_le_of_prime`).

## Main results

* `ArithmeticFunction.vonMangoldt.summable_nonprime_div`: `∑ₙ (if n is prime then 0 else Λ(n)) / n`
  converges.
* `ArithmeticFunction.vonMangoldt.sum_Icc_nonprime_div_le`: for every `N`, the finite sum over
  `1 ≤ n ≤ N` is at most `∑_{p ≤ N} log p / (p (p - 1))`.
* `ArithmeticFunction.vonMangoldt.sum_Icc_nonprime_div_le_two_mul_log_four` and
  `ArithmeticFunction.vonMangoldt.tsum_nonprime_div_le`: the finite and infinite sums are at most
  `2 log 4`.
-/

public section

open ArithmeticFunction Finset

namespace ArithmeticFunction.vonMangoldt

/-- The von Mangoldt weights `Λ n / n` at the non-prime `n`, which are supported on the prime
powers `p ^ k` with `k ≥ 2`, are summable. -/
theorem summable_nonprime_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / n := by
  have h (n : ℕ) : residueClass (1 : ZMod 1) n = vonMangoldt n :=
    Set.indicator_of_mem (Subsingleton.elim (n : ZMod 1) 1) _
  simpa only [h] using summable_residueClass_non_primes_div (1 : ZMod 1)

/-- For `p ≠ 1`, the higher-power reciprocals `p ^ (-k)` on `2 ≤ k ≤ M` sum to at most
`1 / (p * (p - 1))`. -/
private theorem sum_Icc_inv_pow_le {p : ℕ} (hp : p ≠ 1) (M : ℕ) :
    ∑ k ∈ Icc 2 M, ((p : ℝ) ^ k)⁻¹ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · refine (sum_eq_zero fun k hk ↦ ?_).trans_le (by norm_num)
    have hk0 : k ≠ 0 := by linarith [(mem_Icc.mp hk).1]
    simp [zero_pow hk0]
  have hp2 : 2 ≤ p := by omega
  have hcast2 : ((p - 2 : ℕ) : ℝ) + 2 = p := by exact_mod_cast Nat.sub_add_cancel hp2
  have hcast1 : ((p - 2 : ℕ) : ℝ) + 1 = (p : ℝ) - 1 := by linarith
  have hhas := TauCeti.hasSum_inv_add_two_pow_add_two (p - 2)
  rw [hcast2, hcast1] at hhas
  have himg : Icc 2 M = (range (M - 1)).image (· + 2) := by
    ext k
    simp only [mem_Icc, mem_image, mem_range]
    exact ⟨fun _ ↦ ⟨k - 2, by omega, by omega⟩, by rintro ⟨_, _, rfl⟩; omega⟩
  rw [himg, sum_image (fun _ _ _ _ h ↦ by omega)]
  simp_rw [← inv_pow]
  refine (hhas.summable.sum_le_tsum (range (M - 1)) fun _ _ ↦ by positivity).trans ?_
  rw [hhas.tsum_eq]
  have hp_pos : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := mod_cast hp2
    linarith
  field_simp
  ring_nf
  exact le_rfl

/-- Regrouping by the prime base bounds the non-prime von Mangoldt sum up to `N` by the
prime-indexed geometric majorant `∑_{p ≤ N} log p / (p (p - 1))`. -/
theorem sum_Icc_nonprime_div_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n ≤
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  set f : ℕ → ℝ := fun n ↦ (if n.Prime then 0 else vonMangoldt n) / n
  have hf (n : ℕ) (hn : ¬IsPrimePow n) : f n = 0 := by
    simp [f, vonMangoldt_eq_zero_iff.mpr hn]
  rw [Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log hf N]
  refine sum_le_sum fun p hp ↦ ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (mod_cast hp_prime.one_lt.le)
  calc ∑ k ∈ Icc 1 (p.log N), f (p ^ k)
      = ∑ k ∈ Icc 2 (p.log N), Real.log p * ((p : ℝ) ^ k)⁻¹ := by
        rcases lt_or_ge (p.log N) 1 with hlt | hge
        · rw [Icc_eq_empty (by omega), Icc_eq_empty (by omega), sum_empty, sum_empty]
        · rw [← insert_Icc_add_one_left_eq_Icc hge, sum_insert (by simp)]
          have hf1 : f (p ^ 1) = 0 := by simp [f, hp_prime]
          rw [hf1, zero_add]
          refine sum_congr rfl fun k hk ↦ ?_
          have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
          have hnot : ¬(p ^ k).Prime := Nat.Prime.not_prime_pow hk2
          simp [f, hnot, vonMangoldt_apply_pow (by omega : k ≠ 0),
            vonMangoldt_apply_prime hp_prime, div_eq_mul_inv]
    _ = Real.log p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ Real.log p * (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_pow_le hp_prime.ne_one (p.log N)) hlog
    _ = Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := mul_one_div _ _

/-- For every `N`, the finite sum of `Λ(n) / n` over non-prime `1 ≤ n ≤ N` is at most `2 log 4`. -/
theorem sum_Icc_nonprime_div_le_two_mul_log_four (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n ≤ 2 * Real.log 4 := by
  calc ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n
      ≤ ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
        sum_Icc_nonprime_div_le N
    _ ≤ ∑ p ∈ Nat.primesLE N, 2 * (Real.log p / (p : ℝ) ^ 2) := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        rw [mul_div_assoc', le_div_iff₀ (sq_pos_of_pos (by linarith)),
          div_mul_eq_mul_div, div_le_iff₀ (by nlinarith)]
        have hsq : (p : ℝ) ^ 2 ≤ 2 * ((p : ℝ) * ((p : ℝ) - 1)) := by nlinarith
        linarith [mul_le_mul_of_nonneg_left hsq hlog]
    _ = 2 * ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ 2 * (2 * Real.log 4 / 2) := by
        gcongr
        exact TauCeti.sum_log_div_sq_le_of_prime zero_lt_two
          (fun p hp ↦ Nat.prime_of_mem_primesLE hp)
          (fun p hp ↦ mod_cast (Nat.prime_of_mem_primesLE hp).two_le)
    _ = 2 * Real.log 4 := by ring

/-- The infinite sum of `Λ(n) / n` over all non-prime `n : ℕ` is at most `2 log 4`. -/
theorem tsum_nonprime_div_le :
    (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / n) ≤ 2 * Real.log 4 := by
  refine summable_nonprime_div.tsum_le_of_sum_le fun s ↦ ?_
  have hs0 : ∑ n ∈ s, (if n.Prime then 0 else vonMangoldt n) / n =
      ∑ n ∈ s.erase 0, (if n.Prime then 0 else vonMangoldt n) / n := by
    by_cases h0 : 0 ∈ s
    · rw [← sum_erase_add _ _ h0]
      simp
    · rw [erase_eq_of_notMem h0]
  rw [hs0]
  refine (sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun _ _ _ ↦
    div_nonneg (by split_ifs <;> simp [vonMangoldt_nonneg]) (Nat.cast_nonneg _)).trans
      (sum_Icc_nonprime_div_le_two_mul_log_four (s.sup id))
  exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (ne_of_mem_erase hn),
    le_sup (f := id) (mem_of_mem_erase hn)⟩

end ArithmeticFunction.vonMangoldt
