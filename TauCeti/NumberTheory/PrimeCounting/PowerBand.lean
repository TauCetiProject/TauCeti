/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic weight of primes with a power in a narrow band

For a fixed positive exponent, the smallest and largest bases in a power band control the
sum of reciprocal bases. Grouping by a witnessing exponent then bounds the sum of `log p / p`
without using a prime-counting theorem. This argument works for composite bases as well.

The band estimate is used to charge discarded primes in the loss estimate
`Formalism.RankGapBounds.WeightedMeanData.Data.LoP` in Levent Alpöge's
[published formalization](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
-/

public section

open Filter

namespace Finset

/-- The reciprocal sum over natural numbers `n ≥ P` whose `k`th powers lie in `[L, U]` is
bounded by the relative width `U / L - 1` and the weight of one endpoint. -/
theorem sum_inv_le_of_pow_mem_Icc (s : Finset ℕ) {P k : ℕ} {L U : ℝ}
    (hP : 0 < P) (hk : 0 < k) (hL : 0 < L) (hLU : L ≤ U)
    (hs : ∀ n ∈ s, P ≤ n ∧ (n : ℝ) ^ k ∈ Set.Icc L U) :
    ∑ n ∈ s, (n : ℝ)⁻¹ ≤ U / L - 1 + (P : ℝ)⁻¹ := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp only [sum_empty]
    have : 1 ≤ U / L := (le_div_iff₀ hL).2 (by simpa using hLU)
    positivity
  let a := s.min' h
  let b := s.max' h
  have ha := hs a (s.min'_mem h)
  have hb := hs b (s.max'_mem h)
  have hab : a ≤ b := s.min'_le b (s.max'_mem h)
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast hP.trans_le ha.1
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have hratio : (b : ℝ) / a ≤ U / L := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [div_le_div_iff₀ ha0 hL]
    calc
      (b : ℝ) * L ≤ b * (a : ℝ) ^ (j + 1) := mul_le_mul_of_nonneg_left ha.2.1 hb0
      _ ≤ (b : ℝ) ^ (j + 1) * a := by
        have hpow : (a : ℝ) ^ j ≤ (b : ℝ) ^ j := by gcongr
        simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right hpow (mul_nonneg hb0 ha0.le)
      _ ≤ U * a := mul_le_mul_of_nonneg_right hb.2.2 ha0.le
  have hcard : (s.card : ℝ) ≤ (b : ℝ) + 1 - a := by
    have hc := card_le_card (t := Icc a b) fun n hn ↦
      mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    rw [Nat.card_Icc] at hc
    have hc' : (s.card : ℝ) + a ≤ b + 1 := by
      exact_mod_cast (show s.card + a ≤ b + 1 by omega)
    linarith
  calc
    ∑ n ∈ s, (n : ℝ)⁻¹ ≤ s.card • (a : ℝ)⁻¹ :=
      sum_le_card_nsmul _ _ _ fun n hn ↦ inv_anti₀ ha0 (by exact_mod_cast s.min'_le n hn)
    _ = (s.card : ℝ) / a := by rw [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (b : ℝ) / a - 1 + (a : ℝ)⁻¹ := by
      refine (div_le_div_of_nonneg_right hcard ha0.le).trans_eq ?_
      field_simp
      ring
    _ ≤ U / L - 1 + (P : ℝ)⁻¹ := by
      gcongr
      exact ha.1

/-- Bound the logarithmic weight of a finite set of bases `n ≥ P` each having a positive
power in `[L, U]`. A base with several witnessing exponents is still counted only once. -/
theorem sum_log_div_le_of_exists_pow_mem_Icc (s : Finset ℕ) {P : ℕ} {L U : ℝ}
    (hP : 1 < P) (hL : 0 < L) (hLU : L ≤ U)
    (hs : ∀ n ∈ s, P ≤ n ∧ ∃ k : ℕ, 0 < k ∧ (n : ℝ) ^ k ∈ Set.Icc L U) :
    ∑ n ∈ s, Real.log n / n ≤ Real.log U ^ 2 / Real.log P * (U / L - 1 + (P : ℝ)⁻¹) := by
  classical
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hwidth : 0 ≤ U / L - 1 + (P : ℝ)⁻¹ := by
    have : 1 ≤ U / L := (le_div_iff₀ hL).2 (by simpa using hLU)
    positivity
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · rw [sum_empty]
    positivity
  have hn_le (n : ℕ) (hnP : P ≤ n) {k : ℕ} (hk : k ≠ 0) (h : (n : ℝ) ^ k ≤ U) :
      (n : ℝ) ≤ U := (le_self_pow₀ (by exact_mod_cast hP.le.trans hnP) hk).trans h
  obtain ⟨haP, j, hj, hjband⟩ := hs a ha
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg
    ((by exact_mod_cast hP.le.trans haP : (1 : ℝ) ≤ a).trans (hn_le a haP hj.ne' hjband.2))
  let K := ⌊Real.log U / Real.log P⌋₊
  have hex (n : ℕ) (hn : n ∈ s) : ∃ k ∈ Icc 1 K, (n : ℝ) ^ k ∈ Set.Icc L U := by
    obtain ⟨hnP, k, hk, hband⟩ := hs n hn
    refine ⟨k, mem_Icc.mpr ⟨hk, Nat.le_floor ?_⟩, hband⟩
    exact (le_div_iff₀ hlogP).2 <| Real.le_log_of_pow_le (by positivity)
      ((pow_le_pow_left₀ (Nat.cast_nonneg P) (by exact_mod_cast hnP) k).trans hband.2)
  choose! e he hband using hex
  have hfiber (k : ℕ) {n : ℕ} (hn : n ∈ s.filter (fun n ↦ e n = k)) :
      P ≤ n ∧ (n : ℝ) ^ k ∈ Set.Icc L U := by
    obtain ⟨hns, rfl⟩ := mem_filter.mp hn
    exact ⟨(hs n hns).1, hband n hns⟩
  rw [← sum_fiberwise_of_maps_to he (fun n ↦ Real.log n / n)]
  calc
    _ ≤ ∑ _k ∈ Icc 1 K, Real.log U * (U / L - 1 + (P : ℝ)⁻¹) := by
      refine sum_le_sum fun k hk ↦ ?_
      calc
        _ ≤ ∑ n ∈ s.filter (fun n ↦ e n = k), Real.log U * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn ↦ ?_
          rw [div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right (Real.log_le_log ?_ ?_) (by positivity)
          · exact_mod_cast (lt_trans Nat.zero_lt_one hP).trans_le (hfiber k hn).1
          · exact hn_le n (hfiber k hn).1 (by have := (mem_Icc.mp hk).1; omega)
              (hfiber k hn).2.2
        _ ≤ _ := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_inv_le_of_pow_mem_Icc _ (zero_lt_one.trans hP) (mem_Icc.mp hk).1 hL hLU
              (fun _ ↦ hfiber k)) hlogU
    _ = (K : ℝ) * (Real.log U * (U / L - 1 + (P : ℝ)⁻¹)) := by
      simp [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ _ := by
      calc
        _ ≤ (Real.log U / Real.log P) * (Real.log U * (U / L - 1 + (P : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hlogU hlogP.le))
            (mul_nonneg hlogU hwidth)
        _ = _ := by ring

end Finset

namespace TauCeti

/-- Uniform narrow-band estimate: if `log (2 * X) ≤ C * x ^ δ` for some fixed `δ < 1/2`,
a relative width at most `x⁻²` and a base cutoff at least `x²` give a logarithmic weight
of at most `c / x` for every `c > 0` at sufficiently large scales. The threshold is
independent of the band centre, its width, the cutoff, and the selected bases. -/
theorem eventually_sum_log_div_le_of_exists_pow_mem_Icc (C : ℝ) {δ c : ℝ}
    (hδ : δ < 1 / 2) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ (X ρ : ℝ) (P : ℕ) (s : Finset ℕ),
      0 ≤ X → ρ ≤ (x ^ 2)⁻¹ → x ^ 2 ≤ (P : ℝ) → Real.log (2 * X) ≤ C * x ^ δ →
      (∀ n ∈ s, P ≤ n ∧ ∃ k : ℕ, 0 < k ∧ (n : ℝ) ^ k ∈ Set.Icc ((1 - ρ) * X) ((1 + ρ) * X)) →
      ∑ n ∈ s, Real.log n / n ≤ c / x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_const_mul_rpow_le_rpow
    (a := 2 * δ - 2) (b := -1) (by linarith) (5 * C ^ 2 / Real.log 2 / c)] with x hx hscale
  intro X ρ P s hX hρx hPx hC hs
  have hx0 : 0 < x := by positivity
  obtain rfl | ⟨n, hn⟩ := s.eq_empty_or_nonempty
  · rw [Finset.sum_empty]
    positivity
  have hρhalf : ρ ≤ 1 / 2 := hρx.trans (inv_le_of_inv_le₀ (by norm_num) (by norm_num; nlinarith))
  have hP2 : (2 : ℝ) ≤ P := by nlinarith
  have hP : 1 < P := by exact_mod_cast (show (1 : ℝ) < P by linarith)
  obtain ⟨hnP, k, hk, hband⟩ := hs n hn
  have hU : 0 < (1 + ρ) * X := lt_of_lt_of_le (by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans hP).trans_le hnP
    positivity) hband.2
  have hX0 : 0 < X := lt_of_le_of_ne hX fun h ↦ by simp [← h] at hU
  have hLU : (1 - ρ) * X ≤ (1 + ρ) * X := hband.1.trans hband.2
  have hρ : 0 ≤ ρ := by nlinarith [(mul_le_mul_iff_of_pos_right hX0).mp hLU]
  have hL : 0 < (1 - ρ) * X := mul_pos (by linarith) hX0
  have hlog : Real.log ((1 + ρ) * X) ≤ C * x ^ δ :=
    (Real.log_le_log hU (show (1 + ρ) * X ≤ 2 * X by gcongr; linarith)).trans hC
  have hinv : (P : ℝ)⁻¹ ≤ (x ^ 2)⁻¹ := inv_anti₀ (by positivity) hPx
  have hwidth : ((1 + ρ) * X) / ((1 - ρ) * X) - 1 ≤ 4 * ρ := by
    rw [mul_div_mul_right _ _ hX0.ne', sub_le_iff_le_add, div_le_iff₀ (by linarith : 0 < 1 - ρ)]
    nlinarith [mul_nonneg hρ (show 0 ≤ 1 - 2 * ρ by linarith)]
  calc
    _ ≤ _ := s.sum_log_div_le_of_exists_pow_mem_Icc hP hL hLU hs
    _ ≤ (C * x ^ δ) ^ 2 / Real.log 2 * (5 * (x ^ 2)⁻¹) := by
      have hlogU : 0 ≤ Real.log ((1 + ρ) * X) := by
        apply Real.log_nonneg
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hP.le.trans hnP
        exact (one_le_pow₀ hn1).trans hband.2
      apply mul_le_mul
      · gcongr
      · linarith
      · have := (le_div_iff₀ hL).2 (show 1 * ((1 - ρ) * X) ≤ (1 + ρ) * X by nlinarith)
        positivity
      · exact div_nonneg (sq_nonneg _) hlog2.le
    _ = (5 * C ^ 2 / Real.log 2) * x ^ (2 * δ - 2) := by
      have hr : x ^ (2 * δ - 2) = (x ^ δ) ^ 2 * (x ^ 2)⁻¹ := by
        rw [sub_eq_add_neg, mul_comm 2 δ, Real.rpow_add hx0,
          ← Nat.cast_ofNat (R := ℝ) (n := 2), Real.rpow_mul_natCast hx0.le,
          Real.rpow_neg hx0.le, Real.rpow_natCast]
      rw [hr, mul_pow]
      ring
    _ ≤ c / x := by
      rw [Real.rpow_neg_one] at hscale
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hscale
      simpa only [div_eq_mul_inv, mul_comm] using hscale

end TauCeti
