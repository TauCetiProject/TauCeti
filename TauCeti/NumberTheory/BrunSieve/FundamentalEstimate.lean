/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BrunSieve.Basic
public import TauCeti.NumberTheory.SieveDimension.BoundingSieve
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Algebra.Order.BigOperators.Ring.Powerset
import TauCeti.Analysis.SpecialFunctions.Exp.Factorial

/-!
# Brun's fundamental estimate

When a `BoundingSieve` satisfies `BoundingSieve.HasProductDimension κ K` on
`s.prodPrimes.primeFactors` with `0 < κ`, `1 < K`, `1 < y`, and `9 * κ + 1 ≤ u`, evaluating the
combinatorial main-sum defect bound `BoundingSieve.brun_mainSum_defect_le` at parameter
`β = 9 * κ + 1` and prime threshold `z = y ^ (1 / u)` bounds each failure-length summand by a
geometric series with ratio `exp (10 / 9) / 9 < exp (-1)`. Summing the tail yields Kedlaya's
Theorem 12.2 (with the corrected `(1 - δ)` lower main-term factor): for
`V = ∏_{p ∣ P} (1 - ν(p))` and `δ = exp (9 * κ + 1 - u) * K ^ 10`,
`(1 - δ) * V * X - remainderMass s y ≤ s.siftedSum ≤ (1 + δ) * V * X + remainderMass s y`.

## Main results

* `BoundingSieve.brun_mainSum_bounds`: lower and upper bounds `(1 - δ) * V ≤ s.mainSum λ⁻ ≤ V` and
  `V ≤ s.mainSum λ⁺ ≤ (1 + δ) * V` for Brun's combinatorial weights at `β = 9 * κ + 1`.
* `BoundingSieve.brun_fundamental_estimate`: Brun's fundamental estimate with product dimension and
  strict remainder cutoff `y`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, Theorem 12.2 and §12.4.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
-/

public noncomputable section

open Finset Nat Real

namespace BoundingSieve

/-! ### Numerical and single-step estimates for `β = 9 * κ + 1` -/

private theorem brun_geom_ratio_bounds :
    let a : ℝ := Real.exp (10 / 9) / 9
    0 < a ∧ a < (Real.exp 1)⁻¹ ∧ (Real.exp 1)⁻¹ / (1 - a) ≤ 1 := by
  intro a
  have hexp_lt : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
  have hexp_gt : (2.71 : ℝ) < Real.exp 1 := (by norm_num : (2.71 : ℝ) < 2.7182818283).trans
    Real.exp_one_gt_d9
  have ha_pos : 0 < a := by positivity
  have h19 : Real.exp (19 / 9) < 9 := by
    refine lt_of_pow_lt_pow_left₀ 9 (by norm_num) ?_
    rw [← Real.exp_nat_mul, show ((9 : ℕ) : ℝ) * (19 / 9) = ((19 : ℕ) : ℝ) * 1 by norm_num,
      Real.exp_nat_mul]
    exact (pow_lt_pow_left₀ hexp_lt (Real.exp_nonneg 1) (by norm_num)).trans (by norm_num)
  have ha_lt_inv : a < (Real.exp 1)⁻¹ := by
    rw [lt_inv_comm₀ ha_pos (Real.exp_pos 1)]
    calc Real.exp 1 < 9 / Real.exp (10 / 9) := by
          rw [lt_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
          simpa [show (1 : ℝ) + 10 / 9 = 19 / 9 by norm_num] using h19
      _ = a⁻¹ := by simp [a]
  have h10 : Real.exp (10 / 9) < 3.1 := by
    refine lt_of_pow_lt_pow_left₀ 9 (by norm_num) ?_
    rw [← Real.exp_nat_mul, show ((9 : ℕ) : ℝ) * (10 / 9) = ((10 : ℕ) : ℝ) * 1 by norm_num,
      Real.exp_nat_mul]
    exact (pow_lt_pow_left₀ hexp_lt (Real.exp_nonneg 1) (by norm_num)).trans (by norm_num)
  have hsum : (Real.exp 1)⁻¹ + a < 1 :=
    calc (Real.exp 1)⁻¹ + a
        < (2.71 : ℝ)⁻¹ + 3.1 / 9 := add_lt_add (inv_strictAnti₀ (by norm_num) hexp_gt)
            (div_lt_div_of_pos_right h10 (by norm_num))
      _ < 1 := by norm_num
  exact ⟨ha_pos, ha_lt_inv, div_le_one_of_le₀ (by linarith [hsum]) (by linarith [hsum, ha_pos])⟩

private theorem euler_ratio_slice_le (s : BoundingSieve) {κ K z : ℝ} (n : ℕ)
    (hκ : 0 < κ) (hK : 1 < K) (hz2 : 2 < z) (hdim : s.HasProductDimension κ K) :
    let β := 9 * κ + 1
    let w := max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S := s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    (∏ p ∈ S, (1 - s.nu p)⁻¹) ≤ K * Real.exp ((n : ℝ) / 9) := by
  intro β w S
  have hβ1 : 1 < β := by dsimp [β]; linarith
  have hw2 : 2 ≤ w := le_max_left _ _
  have hr_pos : 0 < 1 - β⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hβ1)
  have hr_le1 : (1 - β⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ hr_pos.le (sub_le_self 1 (inv_nonneg.mpr (by linarith)))
  have hwz : w ≤ z := max_le hz2.le
    ((rpow_le_rpow_of_exponent_le (by linarith) hr_le1).trans_eq (rpow_one z))
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hr_log : (1 - β⁻¹) ^ n * Real.log z ≤ Real.log w := by
    have := Real.log_le_log (rpow_pos_of_pos (by linarith) _) (le_max_right 2 (z ^ ((1 - β⁻¹) ^ n)))
    rwa [Real.log_rpow (by linarith)] at this
  have hdiv : Real.log z / Real.log w ≤ Real.exp ((n : ℝ) * (1 / (9 * κ))) := by
    have h1 : Real.log z / Real.log w ≤ ((1 - β⁻¹)⁻¹) ^ n := by
      rw [inv_pow, div_le_iff₀ hlw, ← div_eq_inv_mul, le_div_iff₀' (pow_pos hr_pos n)]
      exact hr_log
    have hinv_eq : (1 - β⁻¹)⁻¹ = 1 + 1 / (9 * κ) := by dsimp [β]; field_simp; ring
    have hexp1 : 1 + 1 / (9 * κ) ≤ Real.exp (1 / (9 * κ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (1 / (9 * κ))
    exact h1.trans ((hinv_eq ▸ pow_le_pow_left₀ (by positivity) hexp1 n).trans_eq
      (Real.exp_nat_mul _ n).symm)
  calc ∏ p ∈ S, (1 - s.nu p)⁻¹
      ≤ K * (Real.log z / Real.log w) ^ κ := (s.hasProductDimension_def κ K).mp hdim w z hw2 hwz
    _ ≤ K * (Real.exp ((n : ℝ) * (1 / (9 * κ)))) ^ κ :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow (div_nonneg hlz.le hlw.le) hdiv hκ.le) (by linarith)
    _ = K * Real.exp ((n : ℝ) / 9) := by
        rw [← Real.exp_mul, show (n : ℝ) * (1 / (9 * κ)) * κ = (n : ℝ) / 9 by field_simp]

private theorem sum_nu_slice_pow_le (s : BoundingSieve) {κ K z : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hκ : 0 < κ) (hK : 1 < K) (hz2 : 2 < z) (hdim : s.HasProductDimension κ K) :
    let β := 9 * κ + 1
    let w := max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S := s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    (∑ p ∈ S, s.nu p) ^ n ≤ ((n : ℝ) / 9) ^ n * K ^ 9 := by
  intro β w S
  have hprod_pos : 0 < ∏ p ∈ S, (1 - s.nu p)⁻¹ := prod_pos fun p hp ↦ by
    have hp0 := (mem_filter.mp hp).1
    exact inv_pos.mpr (sub_pos.mpr (s.nu_lt_one_of_dvd_prodPrimes
      (Nat.dvd_of_mem_primeFactors hp0) (Nat.prime_of_mem_primeFactors hp0).ne_one))
  have hsum_nu : ∑ p ∈ S, s.nu p ≤ (n : ℝ) / 9 + Real.log K := by
    have hpt : ∀ p ∈ S, s.nu p ≤ Real.log ((1 - s.nu p)⁻¹) := fun p hp ↦ by
      have hp0 := (mem_filter.mp hp).1
      have hsub : 0 < 1 - s.nu p := sub_pos.mpr (s.nu_lt_one_of_dvd_prodPrimes
        (Nat.dvd_of_mem_primeFactors hp0) (Nat.prime_of_mem_primeFactors hp0).ne_one)
      have h1exp : 1 - s.nu p ≤ Real.exp (-s.nu p) := by linarith [Real.add_one_le_exp (-s.nu p)]
      have hle := Real.log_le_log hsub h1exp
      rw [Real.log_exp] at hle
      rw [Real.log_inv]; linarith
    have hlog_prod : ∑ p ∈ S, Real.log ((1 - s.nu p)⁻¹) = Real.log (∏ p ∈ S, (1 - s.nu p)⁻¹) := by
      rw [← Real.log_prod fun p hp ↦ ?_]
      have hp0 := (mem_filter.mp hp).1
      exact inv_ne_zero (sub_pos.mpr (s.nu_lt_one_of_dvd_prodPrimes
        (Nat.dvd_of_mem_primeFactors hp0) (Nat.prime_of_mem_primeFactors hp0).ne_one)).ne'
    have hlog_ub := Real.log_le_log hprod_pos (s.euler_ratio_slice_le n hκ hK hz2 hdim)
    rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, add_comm] at hlog_ub
    exact (sum_le_sum hpt).trans (hlog_prod.trans_le hlog_ub)
  have hsum_nn : 0 ≤ ∑ p ∈ S, s.nu p := sum_nonneg fun p hp ↦
    (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)).le
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbase_nn : 0 ≤ 1 + 9 * Real.log K / n :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hK.le)) hn0.le)
  calc (∑ p ∈ S, s.nu p) ^ n
      ≤ ((n : ℝ) / 9 + Real.log K) ^ n := pow_le_pow_left₀ hsum_nn hsum_nu n
    _ = ((n : ℝ) / 9) ^ n * (1 + 9 * Real.log K / n) ^ n := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ ((n : ℝ) / 9) ^ n * (Real.exp (9 * Real.log K / n)) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn
          (by simpa only [add_comm] using Real.add_one_le_exp (9 * Real.log K / n)) n)
          (by positivity)
    _ = ((n : ℝ) / 9) ^ n * K ^ 9 := by
        rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hn0.ne',
          show (9 : ℝ) * Real.log K = ((9 : ℕ) : ℝ) * Real.log K by norm_num,
          Real.exp_nat_mul, Real.exp_log (by linarith)]

private theorem slice_term_le (s : BoundingSieve) {κ K z : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hκ : 0 < κ) (hK : 1 < K) (hdim : s.HasProductDimension κ K) :
    let β := 9 * κ + 1
    let w := max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S := s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    (∏ p ∈ S, (1 - s.nu p)⁻¹) * (∑ B ∈ S.powersetCard n, ∏ p ∈ B, s.nu p) ≤
      K ^ 10 * ((Real.exp 1)⁻¹ * (Real.exp (10 / 9) / 9) ^ n) := by
  intro β w S
  by_cases hz2 : 2 < z
  · have hnu_nn : ∀ p ∈ S, 0 ≤ s.nu p := fun p hp ↦
      (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)).le
    have hsym : ∑ B ∈ S.powersetCard n, ∏ p ∈ B, s.nu p ≤
        (((n : ℝ) / 9) ^ n * K ^ 9) / n.factorial := by
      rw [le_div_iff₀' (Nat.cast_pos.mpr n.factorial_pos)]
      exact (factorial_mul_sum_powersetCard_prod_le_sum_pow hnu_nn n).trans
        (s.sum_nu_slice_pow_le hn hκ hK hz2 hdim)
    have hprod := s.euler_ratio_slice_le n hκ hK hz2 hdim
    have hexp_eq : (Real.exp 1) ^ n * Real.exp ((n : ℝ) / 9) = (Real.exp (10 / 9)) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    calc (∏ p ∈ S, (1 - s.nu p)⁻¹) * (∑ B ∈ S.powersetCard n, ∏ p ∈ B, s.nu p)
        ≤ (K * Real.exp ((n : ℝ) / 9)) * ((((n : ℝ) / 9) ^ n * K ^ 9) / n.factorial) :=
          mul_le_mul hprod hsym
            (sum_nonneg fun B hB ↦ prod_nonneg fun p hp ↦ hnu_nn p ((mem_powersetCard.mp hB).1 hp))
            (by positivity)
      _ = K ^ 10 * (((n : ℝ) / Real.exp 1) ^ n / n.factorial * (Real.exp (10 / 9) / 9) ^ n) := by
          have hexp_ne : (Real.exp 1) ^ n ≠ 0 := pow_ne_zero n (Real.exp_ne_zero 1)
          rw [div_pow, div_pow, div_pow, ← hexp_eq]
          field_simp [hexp_ne]
      _ ≤ K ^ 10 * ((Real.exp 1)⁻¹ * (Real.exp (10 / 9) / 9) ^ n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Real.div_exp_one_pow_div_factorial_le hn) (by positivity))
            (by positivity)
  · have hS : S = ∅ := filter_eq_empty_iff.mpr fun p _ h ↦
      not_lt_of_ge ((le_of_not_gt hz2).trans ((le_max_left 2 _).trans h.1)) h.2
    have hpow : S.powersetCard n = ∅ := powersetCard_eq_empty.mpr (by simp [hS]; omega)
    rw [hpow, sum_empty, mul_zero]
    positivity

private theorem brun_tail_sum_le (s : BoundingSieve) {κ K y u : ℝ}
    (hκ : 0 < κ) (hK : 1 < K) (hy : 1 < y) (hu : 9 * κ + 1 ≤ u)
    (hdim : s.HasProductDimension κ K) :
    let β := 9 * κ + 1
    let z := y ^ (1 / u)
    let w : ℕ → ℝ := fun n ↦ max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S : ℕ → Finset ℕ := fun n ↦
      s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w n ≤ (p : ℝ) ∧ (p : ℝ) < z)
    ∑ n ∈ (Icc 1 s.prodPrimes.primeFactors.card).filter (fun n : ℕ ↦ y < z ^ ((n : ℝ) + β)),
        (∏ p ∈ S n, (1 - s.nu p)⁻¹) * (∑ B ∈ (S n).powersetCard n, ∏ p ∈ B, s.nu p) ≤
      Real.exp (9 * κ + 1 - u) * K ^ 10 := by
  intro β z w S
  have hu0 : 0 < u := by linarith
  have hz1 : 1 < z := one_lt_rpow hy (by positivity)
  have hzu : z ^ u = y := by
    dsimp [z]; rw [← rpow_mul (by linarith), one_div_mul_cancel hu0.ne', rpow_one]
  set Nset := (Icc 1 s.prodPrimes.primeFactors.card).filter (fun n : ℕ ↦ y < z ^ ((n : ℝ) + β))
  set a : ℝ := Real.exp (10 / 9) / 9
  obtain ⟨ha_pos, ha_inv, hcoef⟩ := brun_geom_ratio_bounds
  have ha_lt1 : a < 1 := ha_inv.trans (inv_lt_one_of_one_lt₀ (by linarith [Real.exp_one_gt_d9]))
  let m : ℕ := ⌈u - β⌉₊
  have hsub : Nset ⊆ Ico m (s.prodPrimes.primeFactors.card + 1) := fun n hn ↦ by
    obtain ⟨hnIcc, hyz⟩ := mem_filter.mp hn
    have hlt_exp : u < (n : ℝ) + β := by
      by_contra! hle
      exact (not_lt_of_ge (hzu ▸ rpow_le_rpow_of_exponent_le hz1.le hle)) hyz
    exact mem_Ico.mpr ⟨Nat.ceil_le.mpr (by linarith), Nat.lt_succ_of_le (mem_Icc.mp hnIcc).2⟩
  have ham_le : a ^ m ≤ Real.exp (9 * κ + 1 - u) := by
    calc a ^ m ≤ ((Real.exp 1)⁻¹) ^ m := pow_le_pow_left₀ ha_pos.le ha_inv.le m
      _ = Real.exp (-(m : ℝ)) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, mul_neg_one]
      _ ≤ Real.exp (9 * κ + 1 - u) := by
          refine Real.exp_le_exp.mpr ?_
          have hm_ge : u - β ≤ (m : ℝ) := Nat.le_ceil (u - β)
          dsimp [β] at hm_ge; linarith
  calc ∑ n ∈ Nset, (∏ p ∈ S n, (1 - s.nu p)⁻¹) * (∑ B ∈ (S n).powersetCard n, ∏ p ∈ B, s.nu p)
      ≤ ∑ n ∈ Nset, K ^ 10 * ((Real.exp 1)⁻¹ * a ^ n) :=
        sum_le_sum fun n hn ↦ s.slice_term_le (mem_Icc.mp (mem_filter.mp hn).1).1 hκ hK hdim
    _ ≤ ∑ n ∈ Ico m (s.prodPrimes.primeFactors.card + 1), K ^ 10 * ((Real.exp 1)⁻¹ * a ^ n) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = K ^ 10 * ((Real.exp 1)⁻¹ * ∑ n ∈ Ico m (s.prodPrimes.primeFactors.card + 1), a ^ n) := by
        rw [← mul_sum, ← mul_sum]
    _ ≤ K ^ 10 * ((Real.exp 1)⁻¹ * (a ^ m / (1 - a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (geom_sum_Ico_le_of_lt_one ha_pos.le ha_lt1) (by positivity)) (by positivity)
    _ = K ^ 10 * (((Real.exp 1)⁻¹ / (1 - a)) * a ^ m) := by ring
    _ ≤ K ^ 10 * (1 * Real.exp (9 * κ + 1 - u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcoef ham_le (by positivity) zero_le_one)
          (by positivity)
    _ = Real.exp (9 * κ + 1 - u) * K ^ 10 := by ring

/-- **Brun main-sum bounds**: under `s.HasProductDimension κ K` with `0 < κ`, `1 < K`, `1 < y`,
`9 * κ + 1 ≤ u`, and all primes of `s.prodPrimes` strictly below `y ^ (1 / u)`, Brun's lower and
upper sieve weights at `β = 9 * κ + 1` satisfy `(1 - δ) * V ≤ s.mainSum λ⁻ ≤ V` and
`V ≤ s.mainSum λ⁺ ≤ (1 + δ) * V`, where `V = ∏ p ∈ P.primeFactors, (1 - s.nu p)` and
`δ = exp (9 * κ + 1 - u) * K ^ 10`. -/
theorem brun_mainSum_bounds (s : BoundingSieve) (κ K y u : ℝ)
    (hκ : 0 < κ) (hK : 1 < K) (hy : 1 < y) (hu : 9 * κ + 1 ≤ u)
    (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let δ := Real.exp (9 * κ + 1 - u) * K ^ 10
    (1 - δ) * V ≤ s.mainSum (TauCeti.brunWeights s.prodPrimes y (9 * κ + 1) 0) ∧
      s.mainSum (TauCeti.brunWeights s.prodPrimes y (9 * κ + 1) 0) ≤ V ∧
      V ≤ s.mainSum (TauCeti.brunWeights s.prodPrimes y (9 * κ + 1) 1) ∧
      s.mainSum (TauCeti.brunWeights s.prodPrimes y (9 * κ + 1) 1) ≤ (1 + δ) * V := by
  intro V δ
  let β := 9 * κ + 1
  let z := y ^ (1 / u)
  have hβ1 : 1 < β := by dsimp [β]; linarith
  have hu0 : 0 < u := by linarith
  have hz1 : 1 < z := one_lt_rpow hy (by positivity)
  have hzy : z ≤ y ^ (1 / β) :=
    rpow_le_rpow_of_exponent_le hy.le (one_div_le_one_div_of_le (by linarith) hu)
  have hV_nn : 0 ≤ V := prod_nonneg fun p hp ↦
    sub_nonneg.mpr (s.nu_lt_one_of_dvd_prodPrimes
      (Nat.dvd_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hp).ne_one).le
  have htail := s.brun_tail_sum_le hκ hK hy hu hdim
  have hd0 := (s.brun_mainSum_defect_le 0 hy hβ1 hz1 hzy hprimes).trans
    (mul_le_mul_of_nonneg_left htail hV_nn)
  have hd1 := (s.brun_mainSum_defect_le 1 hy hβ1 hz1 hzy hprimes).trans
    (mul_le_mul_of_nonneg_left htail hV_nn)
  norm_num at hd0 hd1
  exact ⟨by linarith, s.mainSum_brunWeights_zero_le y β,
    s.le_mainSum_brunWeights_one y β, by linarith⟩

/-- **Brun's fundamental estimate** with Euler-product sieve dimension and strict remainder cutoff
(Kedlaya, Chapter 12, Theorem 12.2, with the `(1 - δ)` lower main-term factor). -/
theorem brun_fundamental_estimate (s : BoundingSieve) (κ K y u : ℝ)
    (hX : 0 ≤ s.totalMass) (hκ : 0 < κ) (hK : 1 < K) (hy : 1 < y)
    (hu : 9 * κ + 1 ≤ u) (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let δ := Real.exp (9 * κ + 1 - u) * K ^ 10
    (1 - δ) * V * s.totalMass - s.remainderMass y ≤ s.siftedSum ∧
      s.siftedSum ≤ (1 + δ) * V * s.totalMass + s.remainderMass y := by
  intro V δ
  let β := 9 * κ + 1
  have hβ1 : 1 < β := by dsimp [β]; linarith
  have hpy : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y := fun p hp ↦
    (hprimes p hp).trans_le ((rpow_le_rpow_of_exponent_le hy.le
      (div_le_one_of_le₀ (by linarith) (by linarith))).trans_eq (rpow_one y))
  obtain ⟨hm_lo, _, _, hm_hi⟩ := s.brun_mainSum_bounds κ K y u hκ hK hy hu hdim hprimes
  let w0 := TauCeti.brunWeights s.prodPrimes y β 0
  let w1 := TauCeti.brunWeights s.prodPrimes y β 1
  have herr0 : s.errSum w0 ≤ s.remainderMass y := s.errSum_le_remainderMass w0 y
    (fun d _ ↦ TauCeti.abs_brunWeights_le_one s.prodPrimes y β 0 d)
    (fun _ _ hge ↦ by_contra fun hne ↦
      not_lt_of_ge hge (TauCeti.lt_of_brunWeights_ne_zero s.prodPrimes_squarefree hy hβ1 hpy hne))
  have herr1 : s.errSum w1 ≤ s.remainderMass y := s.errSum_le_remainderMass w1 y
    (fun d _ ↦ TauCeti.abs_brunWeights_le_one s.prodPrimes y β 1 d)
    (fun _ _ hge ↦ by_contra fun hne ↦
      not_lt_of_ge hge (TauCeti.lt_of_brunWeights_ne_zero s.prodPrimes_squarefree hy hβ1 hpy hne))
  have hsift_lo := s.totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd w0
    (fun _ hr ↦ TauCeti.sum_divisors_brunWeights_zero_le s.prodPrimes_squarefree hr y β)
  have hsift_hi := s.siftedSum_le_totalMass_mul_mainSum_add_errSum_of_dvd w1
    (fun _ hr ↦ TauCeti.le_sum_divisors_brunWeights_one s.prodPrimes_squarefree hr y β)
  exact ⟨by linarith [mul_le_mul_of_nonneg_right hm_lo hX, herr0, hsift_lo,
      mul_comm ((1 - δ) * V) s.totalMass],
    by linarith [mul_le_mul_of_nonneg_right hm_hi hX, herr1, hsift_hi,
      mul_comm ((1 + δ) * V) s.totalMass]⟩

end BoundingSieve
