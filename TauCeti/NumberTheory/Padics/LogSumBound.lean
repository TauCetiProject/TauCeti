/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-weighted logarithmic sums of p-adic valuations and geometric bounds

This file collects elementary bounds used to sum local congruence losses over finite sets of
primes with weights `Real.log l`: bounding `∑ l ∈ T, padicValNat l a * log l` by `log b` for
`a ≤ b`, bounding `∑ l ∈ T, (1 / 2) ^ l * log l` by `2`, and bounding the product of integers in
`Finset.Ioc (n - d) (n + d)` by `(n + d) ^ (2 * d)`.

## Main results

* `TauCeti.sum_padicValNat_mul_log_le`: for a finite set `T` of primes and `a ≤ b`,
  `∑ l ∈ T, (padicValNat l a : ℝ) * Real.log l ≤ Real.log b`.
* `TauCeti.sum_half_pow_mul_log_le`: for any finite set `T : Finset ℕ`,
  `∑ l ∈ T, (1 / 2 : ℝ) ^ l * Real.log l ≤ 2`.
* `TauCeti.prod_Ioc_sub_add_le_pow`: for `n d : ℕ`,
  `∏ k ∈ Finset.Ioc (n - d) (n + d), k ≤ (n + d) ^ (2 * d)`.

## Provenance

Adapted from `src/New/Congruences/FitTwistsExist.lean` (`New.Selmer.sum_padicValNat_mul_log_le`,
`New.Selmer.sum_half_pow_mul_log_le`, `New.Selmer.prod_Ioc_natB_le_pow`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Real

/-- Summed over a finite set `T` of primes `l` with weights `Real.log l`, the `l`-adic valuations
of a natural number `a` are at most `Real.log b` for every natural number `b ≥ a`. -/
theorem sum_padicValNat_mul_log_le (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime) {a b : ℕ}
    (hab : a ≤ b) :
    ∑ l ∈ T, (padicValNat l a : ℝ) * log l ≤ log b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [padicValNat, Real.log_natCast_nonneg b]
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
  have h_fac : ∑ l ∈ a.factorization.support, (a.factorization l : ℝ) * log l = log a := by
    have h_prod : (∏ l ∈ a.factorization.support, (l : ℝ) ^ a.factorization l) = a := by
      exact_mod_cast Nat.prod_factorization_pow_eq_self ha
    rw [← h_prod, Real.log_prod fun l hl ↦
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors
        (Nat.support_factorization a ▸ hl)).ne_zero)]
    exact sum_congr rfl fun l _ ↦ (Real.log_pow (l : ℝ) _).symm
  calc ∑ l ∈ T, (padicValNat l a : ℝ) * log l
      = ∑ l ∈ T, (a.factorization l : ℝ) * log l :=
        sum_congr rfl fun l hl ↦ by rw [Nat.factorization_def a (hT l hl), Nat.padicValNat_def]
    _ ≤ ∑ l ∈ T ∪ a.factorization.support, (a.factorization l : ℝ) * log l :=
        sum_le_sum_of_subset_of_nonneg subset_union_left fun l _ _ ↦
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg l)
    _ = ∑ l ∈ a.factorization.support, (a.factorization l : ℝ) * log l :=
        (sum_subset subset_union_right fun l _ hl ↦ by
          simp [Finsupp.notMem_support_iff.mp hl]).symm
    _ = log a := h_fac
    _ ≤ log b := Real.log_le_log ha_pos (Nat.cast_le.mpr hab)

/-- For any finite set `T : Finset ℕ`, `∑ l ∈ T, (1 / 2 : ℝ) ^ l * Real.log l ≤ 2`. -/
theorem sum_half_pow_mul_log_le (T : Finset ℕ) :
    ∑ l ∈ T, (1 / 2 : ℝ) ^ l * log l ≤ 2 :=
  calc ∑ l ∈ T, (1 / 2 : ℝ) ^ l * log l
      ≤ ∑ l ∈ T, (l : ℝ) * (1 / 2 : ℝ) ^ l :=
        sum_le_sum fun l _ ↦ by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg l)) (by positivity)
    _ ≤ 1 / 2 / (1 - 1 / 2) ^ 2 :=
        sum_le_hasSum T (fun l _ ↦ by positivity)
          (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num))
    _ = 2 := by norm_num

/-- The product of the natural numbers in `Finset.Ioc (n - d) (n + d)` is at most
`(n + d) ^ (2 * d)`. -/
theorem prod_Ioc_sub_add_le_pow (n d : ℕ) :
    ∏ k ∈ Finset.Ioc (n - d) (n + d), k ≤ (n + d) ^ (2 * d) := by
  have h_card : #(Finset.Ioc (n - d) (n + d)) ≤ 2 * d := by
    rw [Nat.card_Ioc]
    omega
  calc ∏ k ∈ Finset.Ioc (n - d) (n + d), k
      ≤ (n + d) ^ #(Finset.Ioc (n - d) (n + d)) :=
        prod_le_pow_card _ _ _ fun k hk ↦ (Finset.mem_Ioc.mp hk).right
    _ ≤ (n + d) ^ (2 * d) := by
        rcases eq_or_ne (n + d) 0 with h0 | hpos
        · have hd : d = 0 := by omega
          simp [hd]
        · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hpos) h_card

end TauCeti
