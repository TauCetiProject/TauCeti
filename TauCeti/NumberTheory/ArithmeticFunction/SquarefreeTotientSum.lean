/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Data.Nat.Totient
import TauCeti.NumberTheory.SmoothNumbers

/-!
# The squarefree reciprocal-totient sum over integers coprime to a modulus

For every natural number `k` and real `z ≥ 0`,
`∑_{1 ≤ d < z, (d, k) = 1} μ(d)² / φ(d) ≥ (φ(k) / k) log z`,
with constant one and uniformly in `k`. This sum bounds from below the denominator of Selberg's
upper bound for a sieve over the primes not dividing `k` (those dividing `k` are omitted), for
instance to count primes in a progression modulo `k`
(see `TauCeti.NumberTheory.SelbergSieve.CoprimeDiagonal`).

## Main results

* `ArithmeticFunction.sum_Ico_inv_le_mul_sum_moebius_sq_div_totient`: for `k ≠ 0`,
  `∑_{1 ≤ n < N} 1 / n ≤ (k / φ(k)) ∑_{1 ≤ d < N, (d, k) = 1} μ(d)² / φ(d)`.
* `ArithmeticFunction.totient_div_mul_log_le_sum_moebius_sq_div_totient`: the logarithmic
  lower bound above.

## Implementation notes

Each `n < z` is grouped by the product `e` of its prime factors not dividing `k`. The reciprocals
of the `n` with a given `e` sum to at most `(k / φ(k)) / φ(e)`, by the Euler product over the
primes of `e k` (`TauCeti.hasSum_inv_factoredNumbers`). Summing over `e` compares the harmonic
sum `∑_{n < z} 1 / n ≥ log z` with `k / φ(k)` times the coprime sum.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §3, proof of Corollary 3.1, display (3.2).
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius Nat

namespace ArithmeticFunction

/-- The product of the prime factors of `n` that do not divide `k`. -/
private def coprimePart (k n : ℕ) : ℕ := ∏ p ∈ n.primeFactors with ¬p ∣ k, p

private theorem primeFactors_coprimePart (k n : ℕ) :
    (coprimePart k n).primeFactors = n.primeFactors.filter (¬· ∣ k) :=
  Nat.primeFactors_prod fun _ hp ↦ Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1

private theorem coprimePart_dvd (k n : ℕ) : coprimePart k n ∣ n :=
  (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)

private theorem squarefree_coprimePart (k n : ℕ) : Squarefree (coprimePart k n) :=
  (Nat.squarefree_prod_primeFactors n).squarefree_of_dvd
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _))

private theorem coprime_coprimePart (k n : ℕ) : (coprimePart k n).Coprime k :=
  Nat.Coprime.prod_left fun _ hp ↦
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).2
      (mem_filter.mp hp).2

/-- The reciprocals of the `n < N` whose prime factors off `k` multiply to `e` sum to at most
`(k / φ(k)) μ(e)² / φ(e)`. -/
private theorem sum_inv_filter_coprimePart_le {k : ℕ} (hk : k ≠ 0) (N e : ℕ) :
    ∑ n ∈ Ico 1 N with coprimePart k n = e, (n : ℝ)⁻¹ ≤ k / φ k * ((μ e : ℝ) ^ 2 / φ e) := by
  set F := (Ico 1 N).filter (coprimePart k · = e)
  rcases F.eq_empty_or_nonempty with hF | ⟨n₀, hn₀⟩
  · rw [hF, sum_empty]
    positivity
  have he : Squarefree e := (mem_filter.mp hn₀).2 ▸ squarefree_coprimePart k n₀
  have hcop : e.Coprime k := (mem_filter.mp hn₀).2 ▸ coprime_coprimePart k n₀
  have he0 : e ≠ 0 := he.ne_zero
  have hmem (n : ℕ) (hn : n ∈ F) : e ∣ n ∧ n ∈ Nat.factoredNumbers (e * k).primeFactors := by
    obtain ⟨hnI, hne⟩ := mem_filter.mp hn
    refine ⟨hne ▸ coprimePart_dvd k n, Nat.mem_factoredNumbers_of_primeFactors_subset
      (by have := (mem_Ico.mp hnI).1; omega) fun p hp ↦ ?_⟩
    rw [Nat.primeFactors_mul he0 hk, mem_union]
    by_cases hpk : p ∣ k
    · exact .inr (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpk, hk⟩)
    · exact .inl (hne ▸ (primeFactors_coprimePart k n).symm ▸ mem_filter.mpr ⟨hp, hpk⟩)
  have himage : ∑ n ∈ F, (n : ℝ)⁻¹ = (e : ℝ)⁻¹ * ∑ m ∈ F.image (· / e), (m : ℝ)⁻¹ := by
    rw [sum_image fun a ha b hb h ↦ (Nat.div_left_inj (hmem a ha).1 (hmem b hb).1).mp h,
      mul_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [← mul_inv, ← Nat.cast_mul, Nat.mul_div_cancel' (hmem n hn).1]
  have hsum : ∑ m ∈ F.image (· / e), (m : ℝ)⁻¹ ≤ (e * k : ℕ) / φ (e * k) := by
    rw [← TauCeti.Nat.prod_inv_one_sub_inv_eq_div_totient (mul_ne_zero he0 hk),
      ← filter_true_of_mem fun p hp ↦ Nat.prime_of_mem_primeFactors hp]
    classical
    refine sum_le_hasSum (f := fun m : Nat.factoredNumbers (e * k).primeFactors ↦ ((m : ℕ) : ℝ)⁻¹)
      ((F.image (· / e)).subtype fun m : ℕ ↦ m ∈ Nat.factoredNumbers (e * k).primeFactors)
      (fun _ _ ↦ by positivity) (TauCeti.hasSum_inv_factoredNumbers _) |>.trans_eq' ?_
    refine sum_subtype_of_mem (fun m : ℕ ↦ (m : ℝ)⁻¹) fun m hm ↦ ?_
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    exact Nat.mem_factoredNumbers_of_dvd (hmem n hn).2 (Nat.div_dvd_of_dvd (hmem n hn).1)
  have hφe : (φ e : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr he0.bot_lt).ne'
  have hφk : (φ k : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk)).ne'
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he0
  calc ∑ n ∈ F, (n : ℝ)⁻¹ ≤ (e : ℝ)⁻¹ * ((e * k : ℕ) / φ (e * k)) := by
        rw [himage]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = k / φ k * ((μ e : ℝ) ^ 2 / φ e) := by
        rw [Nat.totient_mul hcop, ← Int.cast_pow, moebius_sq_eq_one_of_squarefree he]
        push_cast
        field_simp

/-- For `k ≠ 0`, `∑_{1 ≤ n < N} 1 / n ≤ (k / φ(k)) ∑_{1 ≤ d < N, (d, k) = 1} μ(d)² / φ(d)`. -/
theorem sum_Ico_inv_le_mul_sum_moebius_sq_div_totient {k : ℕ} (hk : k ≠ 0) (N : ℕ) :
    ∑ n ∈ Ico 1 N, (n : ℝ)⁻¹ ≤
      k / φ k * ∑ d ∈ Ico 1 N with d.Coprime k, (μ d : ℝ) ^ 2 / φ d := by
  have hmaps (n : ℕ) (hn : n ∈ Ico 1 N) :
      coprimePart k n ∈ (Ico 1 N).filter (·.Coprime k) := by
    obtain ⟨h1, hN⟩ := mem_Ico.mp hn
    have hle := Nat.le_of_dvd h1 (coprimePart_dvd k n)
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (squarefree_coprimePart k n).ne_zero, by omega⟩, coprime_coprimePart k n⟩
  rw [mul_sum, ← sum_fiberwise_of_maps_to hmaps]
  exact sum_le_sum fun e _ ↦ sum_inv_filter_coprimePart_le hk N e

/-- For every natural number `k` and real `z ≥ 0`,
`∑_{1 ≤ d < z, (d, k) = 1} μ(d)² / φ(d) ≥ (φ(k) / k) log z`, with constant one uniformly
in `k`. -/
theorem totient_div_mul_log_le_sum_moebius_sq_div_totient (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    φ k / k * Real.log z ≤ ∑ d ∈ Ico 1 ⌈z⌉₊ with d.Coprime k, (μ d : ℝ) ^ 2 / φ d := by
  have hnonneg : 0 ≤ ∑ d ∈ Ico 1 ⌈z⌉₊ with d.Coprime k, (μ d : ℝ) ^ 2 / φ d :=
    sum_nonneg fun _ _ ↦ by positivity
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hnonneg
  rcases hz.eq_or_lt with rfl | hz
  · simp
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_one.mpr (Nat.ceil_pos.mpr hz)
  have hlog : Real.log z ≤ ∑ n ∈ Ico 1 ⌈z⌉₊, (n : ℝ)⁻¹ := by
    calc Real.log z ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
          Real.log_le_log hz (hN ▸ Nat.le_ceil z)
      _ ≤ harmonic N := log_add_one_le_harmonic N
      _ = _ := by
          rw [hN, Finset.Ico_add_one_right_eq_Icc]
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc φ k / k * Real.log z
      ≤ φ k / k * (k / φ k * ∑ d ∈ Ico 1 ⌈z⌉₊ with d.Coprime k, (μ d : ℝ) ^ 2 / φ d) :=
        mul_le_mul_of_nonneg_left
          (hlog.trans (sum_Ico_inv_le_mul_sum_moebius_sq_div_totient hk _)) (by positivity)
    _ = _ := by
        have hφk : (φ k : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk.bot_lt).ne'
        have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
        field_simp

end ArithmeticFunction
