/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Eulerian.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantitative bounds on Eulerian numbers

This file proves upper and lower bounds on the descent-indexed Eulerian numbers
`TauCeti.eulerianNumber n q`, following Appendix C (Lemmas C.1–C.5) of Lawrence–Sawin.

## Main results

* `TauCeti.eulerianNumber_le_pow`: `eulerianNumber n q ≤ (q + 1) ^ n`.
* `TauCeti.eulerianNumber_le_factorial`: `eulerianNumber n q ≤ n.factorial`.
* `TauCeti.pow_sub_mul_pow_le_eulerianNumber`:
  `((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ)` for `1 ≤ n`.
* `TauCeti.one_sub_exp_neg_one_mul_pow_le_eulerianNumber`:
  `(1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ eulerianNumber n q` when `2 ≤ n` and
  `(q : ℝ) + 1 < n / (Real.log (n + 1) + 1)`.
* `TauCeti.two_mul_eulerianNumber_lt_mul_sub_one`:
  `2 * eulerianNumber n (3 * r - 2) < eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1)`
  for `3 ≤ r ≤ n - 2`.
* `TauCeti.mul_eulerianNumber_two_lt_sq`:
  `27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2` for `11 ≤ n`.

## References

* B. Lawrence and W. Sawin, *The Shafarevich conjecture for hypersurfaces in abelian varieties*,
  Annals of Mathematics 202 (2025), Appendix C, Lemmas C.1–C.5, pp. 116–118.
-/

public section

open Finset

namespace TauCeti

/-- Upper power bound on Eulerian numbers: `A(n, q) ≤ (q + 1) ^ n`. -/
theorem eulerianNumber_le_pow (n q : ℕ) : eulerianNumber n q ≤ (q + 1) ^ n := by
  rw [pow_eq_sum_eulerianNumber_mul_choose n q]
  have hmem : q ∈ Finset.range (q + 1) := Finset.mem_range.mpr (Nat.lt_succ_self q)
  have hle := Finset.single_le_sum (f := fun j => eulerianNumber n j * (n + q - j).choose n)
    (fun _ _ => Nat.zero_le _) hmem
  simpa [Nat.add_sub_cancel] using hle

/-- Upper factorial bound on Eulerian numbers: `A(n, q) ≤ n!`. -/
theorem eulerianNumber_le_factorial (n q : ℕ) : eulerianNumber n q ≤ n.factorial := by
  rcases le_or_gt q n with hqn | hnq
  · rw [← sum_range_eulerianNumber n]
    exact Finset.single_le_sum (f := fun j => eulerianNumber n j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hqn))
  · rw [eulerianNumber_eq_zero_of_lt hnq]
    exact Nat.zero_le _

/-- Additive form of the lower bound in Lemma C.1:
`(q + 1) ^ n ≤ eulerianNumber n q + (n + 1) * q ^ n` for `1 ≤ n`. -/
theorem pow_le_eulerianNumber_add_mul_pow {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    (q + 1) ^ n ≤ eulerianNumber n q + (n + 1) * q ^ n := by
  cases q with
  | zero =>
    rw [zero_add, one_pow, eulerianNumber_zero_right, zero_pow (by omega), mul_zero, add_zero]
  | succ p =>
    rw [pow_eq_sum_eulerianNumber_mul_choose n (p + 1), Finset.sum_range_succ,
      show n + (p + 1) - (p + 1) = n by omega, Nat.choose_self, mul_one, add_comm]
    refine Nat.add_le_add_left ?_ _
    rw [pow_eq_sum_eulerianNumber_mul_choose n p, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjp : j ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hchoose : (n + (p + 1) - j).choose n ≤ (n + 1) * (n + p - j).choose n := by
      set m : ℕ := n + p - j
      have hm_eq : n + (p + 1) - j = m + 1 := by omega
      have hpos : 0 < p - j + 1 := Nat.succ_pos _
      rw [hm_eq]
      apply Nat.le_of_mul_le_mul_left _ hpos
      have hrel : (p - j + 1) * (m + 1).choose n = (m + 1) * m.choose n := by
        have hnm : n ≤ m := by omega
        have h1 : m - n + 1 = p - j + 1 := by omega
        have h2 : (m + 1) - (m - n + 1) = n := by omega
        have hsym1 : m.choose (m - n) = m.choose n := Nat.choose_symm hnm
        have hsym2 : (m + 1).choose (m - n + 1) = (m + 1).choose n := by
          rw [← Nat.choose_symm (by omega : m - n + 1 ≤ m + 1), h2]
        have hadd := Nat.add_one_mul_choose_eq m (m - n)
        rw [hsym1, hsym2, h1] at hadd
        linarith
      rw [hrel]
      have hmul : m + 1 ≤ (p - j + 1) * (n + 1) := by
        have : m + 1 = n + (p - j + 1) := by omega
        rw [this]
        nlinarith
      calc
        (m + 1) * m.choose n ≤ ((p - j + 1) * (n + 1)) * m.choose n :=
          Nat.mul_le_mul_right _ hmul
        _ = (p - j + 1) * ((n + 1) * m.choose n) := by ring
    calc
      eulerianNumber n j * (n + (p + 1) - j).choose n
          ≤ eulerianNumber n j * ((n + 1) * (n + p - j).choose n) :=
        Nat.mul_le_mul_left _ hchoose
      _ = (n + 1) * (eulerianNumber n j * (n + p - j).choose n) := by ring

/-- Lower power bound on Eulerian numbers in `ℤ` (Lawrence–Sawin, Lemma C.1):
`((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ)` for `1 ≤ n`. -/
theorem pow_sub_mul_pow_le_eulerianNumber {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    ((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ) :=
  sub_le_iff_le_add.mpr (by exact_mod_cast pow_le_eulerianNumber_add_mul_pow hn q)

/-- Real lower bound on Eulerian numbers with few descents (Lawrence–Sawin, Lemma C.3):
for `2 ≤ n` and `(q : ℝ) + 1 < n / (Real.log (n + 1) + 1)`,
`(1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ eulerianNumber n q`. -/
theorem one_sub_exp_neg_one_mul_pow_le_eulerianNumber {n q : ℕ} (hn : 2 ≤ n)
    (hq : (q : ℝ) + 1 < (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1)) :
    (1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ (eulerianNumber n q : ℝ) := by
  have hc1 : ((q : ℝ) + 1) ^ n ≤ (eulerianNumber n q : ℝ) + ((n : ℝ) + 1) * (q : ℝ) ^ n := by
    exact_mod_cast pow_le_eulerianNumber_add_mul_pow (by omega : 1 ≤ n) q
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [Nat.cast_zero, zero_add, one_pow, mul_one, eulerianNumber_zero_right,
      Nat.cast_one]
    linarith [Real.exp_pos (-1 : ℝ)]
  · have hq1pos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have hn1gt : (1 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
    have hlogpos : 0 < Real.log ((n : ℝ) + 1) + 1 := by
      have := Real.log_pos hn1gt
      linarith
    have hdiv : Real.log ((n : ℝ) + 1) + 1 < (n : ℝ) / ((q : ℝ) + 1) := by
      exact (lt_div_iff₀ hq1pos).mpr (by
        have := (lt_div_iff₀ hlogpos).mp hq
        nlinarith)
    have hadd : (q : ℝ) / ((q : ℝ) + 1) < Real.exp (-1 / ((q : ℝ) + 1)) := by
      have hne : (-1 / ((q : ℝ) + 1)) ≠ 0 := by positivity
      have hexp := Real.add_one_lt_exp hne
      have heq : -1 / ((q : ℝ) + 1) + 1 = (q : ℝ) / ((q : ℝ) + 1) := by
        field_simp
        ring
      rwa [heq] at hexp
    have hpow : ((q : ℝ) / ((q : ℝ) + 1)) ^ n <
        Real.exp (-((n : ℝ) / ((q : ℝ) + 1))) := by
      have hnonneg : 0 ≤ (q : ℝ) / ((q : ℝ) + 1) := by positivity
      have hn_pos : 0 < n := by omega
      calc
        ((q : ℝ) / ((q : ℝ) + 1)) ^ n < (Real.exp (-1 / ((q : ℝ) + 1))) ^ n :=
          pow_lt_pow_left₀ hadd hnonneg hn_pos.ne'
        _ = Real.exp ((n : ℝ) * (-1 / ((q : ℝ) + 1))) := by rw [← Real.exp_natCast_mul]
        _ = Real.exp (-((n : ℝ) / ((q : ℝ) + 1))) := by ring_nf
    have hexp_bound : Real.exp (-((n : ℝ) / ((q : ℝ) + 1))) <
        Real.exp (-1) / ((n : ℝ) + 1) := by
      have hlt : -((n : ℝ) / ((q : ℝ) + 1)) < -(Real.log ((n : ℝ) + 1) + 1) := by linarith
      calc
        Real.exp (-((n : ℝ) / ((q : ℝ) + 1))) < Real.exp (-(Real.log ((n : ℝ) + 1) + 1)) :=
          Real.exp_lt_exp.mpr hlt
        _ = Real.exp (-1) * Real.exp (-Real.log ((n : ℝ) + 1)) := by
          rw [← Real.exp_add]; ring_nf
        _ = Real.exp (-1) / ((n : ℝ) + 1) := by
          rw [Real.exp_neg (Real.log _), Real.exp_log (by positivity), div_eq_mul_inv]
    have hkey : ((n : ℝ) + 1) * (q : ℝ) ^ n < Real.exp (-1) * ((q : ℝ) + 1) ^ n := by
      have hrat : ((q : ℝ) / ((q : ℝ) + 1)) ^ n < Real.exp (-1) / ((n : ℝ) + 1) :=
        hpow.trans hexp_bound
      rw [div_pow, lt_div_iff₀ (by positivity)] at hrat
      calc
        ((n : ℝ) + 1) * (q : ℝ) ^ n
            = ((q : ℝ) ^ n / ((q : ℝ) + 1) ^ n * ((n : ℝ) + 1)) * ((q : ℝ) + 1) ^ n := by
          field_simp
        _ < Real.exp (-1) * ((q : ℝ) + 1) ^ n := by
          exact mul_lt_mul_of_pos_right hrat (by positivity)
    linarith

/-! ### Fast computable row table for finite base cases -/

private def nextEulerianRow (row : List ℕ) : List ℕ :=
  1 :: List.zipWith (fun k p => (k + 2) * p.1 + (row.length - 1 - k) * p.2)
    (List.range row.length) (List.zip (row.drop 1 ++ [0]) row)

private def eulerianRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => nextEulerianRow (eulerianRow n)

private lemma eulerianRow_length (n : ℕ) : (eulerianRow n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [eulerianRow, nextEulerianRow, List.length_cons, List.length_zipWith,
      List.length_range, List.length_zip, List.length_append, List.length_drop, ih]
    omega

private lemma eulerianRow_getD (n q : ℕ) :
    (eulerianRow n).getD q 0 = eulerianNumber n q := by
  induction n generalizing q with
  | zero =>
    cases q with
    | zero => simp [eulerianRow]
    | succ q => simp [eulerianRow]
  | succ n ih =>
    cases q with
    | zero => simp [eulerianRow, nextEulerianRow]
    | succ k =>
      simp only [eulerianRow, nextEulerianRow, List.getD_eq_getElem?_getD,
        List.getElem?_cons_succ]
      have hlen : (eulerianRow n).length = n + 1 := eulerianRow_length n
      rcases lt_or_ge k (n + 1) with hk | hk
      · have hlen_zip : (List.zipWith
            (fun j p => (j + 2) * p.1 + ((eulerianRow n).length - 1 - j) * p.2)
            (List.range (eulerianRow n).length)
            (List.zip ((eulerianRow n).drop 1 ++ [0]) (eulerianRow n))).length = n + 1 := by
          simp only [List.length_zipWith, List.length_range, List.length_zip, List.length_append,
            List.length_drop, List.length_singleton, hlen]
          omega
        have hk' : k < (List.zipWith _ _ _).length := hlen_zip ▸ hk
        rw [List.getElem?_eq_getElem hk', Option.getD_some, List.getElem_zipWith]
        simp only [List.getElem_range, List.getElem_zip, hlen, Nat.add_sub_cancel]
        have hdrop : ((eulerianRow n).drop 1 ++ [0])[k]'(by
            simp only [List.length_append, List.length_drop, List.length_singleton, hlen]
            omega) = eulerianNumber n (k + 1) := by
          rcases lt_or_ge (k + 1) (n + 1) with hk1 | hk1
          · have hlt_drop : k < ((eulerianRow n).drop 1).length := by simp [hlen]; omega
            rw [List.getElem_append_left hlt_drop, List.getElem_drop]
            have h1 := ih (1 + k)
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : 1 + k < (eulerianRow n).length),
              Option.getD_some] at h1
            simpa [add_comm 1 k] using h1
          · have heq : k = n := by omega
            have hlen_drop : ((eulerianRow n).drop 1).length = n := by simp [hlen]
            rw [List.getElem_append_right (by omega : ((eulerianRow n).drop 1).length ≤ k)]
            simp only [hlen_drop, List.getElem_singleton, heq]
            exact (eulerianNumber_eq_zero_of_lt (by omega)).symm
        have hcurr : (eulerianRow n)[k]'(hlen ▸ hk) = eulerianNumber n k := by
          have h0 := ih k
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hk),
            Option.getD_some] at h0
          exact h0
        rw [hdrop, hcurr, eulerianNumber_succ_succ]
      · have hlen_zip : (List.zipWith
            (fun j p => (j + 2) * p.1 + ((eulerianRow n).length - 1 - j) * p.2)
            (List.range (eulerianRow n).length)
            (List.zip ((eulerianRow n).drop 1 ++ [0]) (eulerianRow n))).length ≤ k := by
          simp only [List.length_zipWith, List.length_range, List.length_zip, List.length_append,
            List.length_drop, List.length_singleton, hlen]
          omega
        rw [List.getElem?_eq_none hlen_zip, Option.getD_none,
          eulerianNumber_eq_zero_of_le (by omega) (by omega)]

private lemma eulerianNumber_two_ge_66 {n : ℕ} (hn : 5 ≤ n) : 66 ≤ eulerianNumber n 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m _hm ih =>
    rw [eulerianNumber_succ_succ]
    calc
      66 ≤ 3 * 66 := by omega
      _ ≤ 3 * eulerianNumber m 2 := Nat.mul_le_mul_left 3 ih
      _ ≤ 3 * eulerianNumber m 2 + (m - 1) * eulerianNumber m 1 := Nat.le_add_right _ _

private lemma eulerianNumber_ge_66_of_three_le {n r : ℕ} (hr : 3 ≤ r) (hrn : r ≤ n - 2) :
    66 ≤ eulerianNumber n (r - 1) := by
  have hn : 5 ≤ n := by omega
  rcases le_or_gt (r - 1) (n / 2) with hle | hgt
  · exact (eulerianNumber_two_ge_66 hn).trans
      (eulerianNumber_monotoneOn n (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr hle) (by omega))
  · have hle' : (n - 1) / 2 ≤ r - 1 := by omega
    have hsym : eulerianNumber n (n - 3) = eulerianNumber n 2 := by
      rw [eulerianNumber_symm (by omega), show n - 1 - (n - 3) = 2 by omega]
    calc
      66 ≤ eulerianNumber n 2 := eulerianNumber_two_ge_66 hn
      _ = eulerianNumber n (n - 3) := hsym.symm
      _ ≤ eulerianNumber n (r - 1) :=
        eulerianNumber_antitoneOn n (Set.mem_Ici.mpr hle') (Set.mem_Ici.mpr (by omega)) (by omega)

private lemma one_sub_exp_neg_one_gt_five_eighths : (5 : ℝ) / 8 < 1 - Real.exp (-1) := by
  have hexp : (8 : ℝ) / 3 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hinv : Real.exp (-1) < 3 / 8 := by
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)).mpr (by norm_num at hexp ⊢; exact hexp)
  linarith

private lemma six_mul_factorial_le_pow {n : ℕ} (hn : 5 ≤ n) : 6 * n.factorial ≤ n ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m _hm ih =>
    calc
      6 * (m + 1).factorial = (m + 1) * (6 * m.factorial) := by
        rw [Nat.factorial_succ]; ring
      _ ≤ (m + 1) * m ^ m := Nat.mul_le_mul_left _ ih
      _ ≤ (m + 1) * (m + 1) ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ m) m)
      _ = (m + 1) ^ (m + 1) := (pow_succ' (m + 1) m).symm

private lemma pow_three_mul_27_64_lt {n : ℕ} (hn : 15 ≤ n) :
    27 * 64 * 3 ^ n < 25 * 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m _hm ih =>
    calc
      27 * 64 * 3 ^ (m + 1) = 3 * (27 * 64 * 3 ^ m) := by rw [pow_succ']; ring
      _ < 3 * (25 * 4 ^ m) := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ 4 * (25 * 4 ^ m) := Nat.mul_le_mul_right _ (by omega)
      _ = 25 * 4 ^ (m + 1) := by rw [pow_succ']; ring

/-- For `11 ≤ n`, `27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2`
(Lawrence–Sawin, Lemma C.5). -/
theorem mul_eulerianNumber_two_lt_sq {n : ℕ} (hn : 11 ≤ n) :
    27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2 := by
  rcases lt_or_ge n 15 with hlt | h15
  · have hcheck : ∀ m ∈ Finset.Icc 11 14,
        27 * (eulerianRow m).getD 2 0 < ((eulerianRow m).getD 1 0) ^ 2 := by
      decide
    have := hcheck n (Finset.mem_Icc.mpr ⟨hn, by omega⟩)
    simpa only [eulerianRow_getD] using this
  · have hlog : (1 : ℝ) + 1 < (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1) := by
      set y : ℝ := (n : ℝ) / 2 - 1
      have hy_nonneg : 0 ≤ y := by
        have : (15 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h15
        dsimp [y]; linarith
      have htay := Real.sum_le_exp_of_nonneg hy_nonneg 3
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at htay
      have hn_real : (15 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h15
      have hexp : (n : ℝ) + 1 < Real.exp y := by
        have hpoly : (n : ℝ) + 1 <
            y ^ 0 / (0).factorial + y ^ 1 / (1).factorial + y ^ 2 / (2).factorial := by
          dsimp [y]
          norm_num
          nlinarith
        exact hpoly.trans_le htay
      have hlt : Real.log ((n : ℝ) + 1) < y := (Real.log_lt_iff_lt_exp (by positivity)).mpr hexp
      have hn2 : Real.log ((n : ℝ) + 1) + 1 < (n : ℝ) / 2 := by dsimp [y] at hlt; linarith
      have hlogpos : 0 < Real.log ((n : ℝ) + 1) + 1 := by
        have : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
        linarith
      rw [lt_div_iff₀ hlogpos]
      linarith
    have hlow := one_sub_exp_neg_one_mul_pow_le_eulerianNumber (n := n) (q := 1) (by omega)
      (by simpa using hlog)
    norm_num at hlow
    have h58 := one_sub_exp_neg_one_gt_five_eighths
    have hpow2 : (5 : ℝ) / 8 * 2 ^ n < (eulerianNumber n 1 : ℝ) := by
      have hlt : (5 : ℝ) / 8 * 2 ^ n < (1 - Real.exp (-1)) * 2 ^ n :=
        mul_lt_mul_of_pos_right h58 (by positivity)
      exact hlt.trans_le hlow
    have hsq : (25 : ℝ) / 64 * 4 ^ n < (eulerianNumber n 1 : ℝ) ^ 2 := by
      have hsq' : ((5 : ℝ) / 8 * 2 ^ n) ^ 2 < (eulerianNumber n 1 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hpow2 (by positivity) (by norm_num)
      calc
        (25 : ℝ) / 64 * 4 ^ n = ((5 : ℝ) / 8 * 2 ^ n) ^ 2 := by
          rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 n, pow_mul]
          norm_num
        _ < (eulerianNumber n 1 : ℝ) ^ 2 := hsq'
    have hup : (eulerianNumber n 2 : ℝ) ≤ 3 ^ n := by
      exact_mod_cast eulerianNumber_le_pow n 2
    have hreal : (27 : ℝ) * (eulerianNumber n 2 : ℝ) < (eulerianNumber n 1 : ℝ) ^ 2 := by
      have hnat_real : (27 : ℝ) * 64 * 3 ^ n < 25 * 4 ^ n := by
        exact_mod_cast pow_three_mul_27_64_lt h15
      linarith
    exact_mod_cast hreal

private lemma sqrt_pred_succ_lt_div_log {n : ℕ} (hn : 21 ≤ n) :
    ((Nat.sqrt (n - 1) + 1 : ℕ) : ℝ) < (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1) := by
  set r₀ : ℕ := Nat.sqrt (n - 1) + 1
  have hr₀_ge : 5 ≤ r₀ := by
    have : 4 ≤ Nat.sqrt (n - 1) := Nat.le_sqrt.mpr (by omega)
    omega
  have hr₀_sq_le : (r₀ - 1) ^ 2 ≤ n - 1 := by
    have h := Nat.sqrt_le (n - 1)
    dsimp [r₀]
    simpa [Nat.pow_two] using h
  have hn_lt_sq : n ≤ r₀ ^ 2 := by
    have h := Nat.lt_succ_sqrt (n - 1)
    dsimp [r₀] at *
    rw [Nat.pow_two]
    omega
  have hlogpos : 0 < Real.log ((n : ℝ) + 1) + 1 := by
    have : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
    linarith
  have hexp : (n : ℝ) + 1 < Real.exp ((n : ℝ) / (r₀ : ℝ) - 1) := by
    set y : ℝ := (n : ℝ) / (r₀ : ℝ) - 1
    have hr₀_pos : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 0 < r₀)
    rcases lt_or_ge r₀ 8 with hr₀_lt | hr₀_ge8
    · have hr₀_cases : r₀ = 5 ∨ r₀ = 6 ∨ r₀ = 7 := by omega
      rcases hr₀_cases with h5 | h6 | h7
      · have hsq1 := hr₀_sq_le
        have hsq2 := hn_lt_sq
        rw [h5] at hsq1 hsq2
        norm_num at hsq1 hsq2
        have hn_range : 21 ≤ n ∧ n ≤ 25 := by omega
        rcases eq_or_lt_of_le hn_range.1 with rfl | hn22
        · have hy : y = 16 / 5 := by dsimp [y]; rw [h5]; norm_num
          have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 5) 7
          norm_num [Finset.sum_range_succ, Nat.factorial] at htay
          change (21 : ℝ) + 1 < Real.exp y
          rw [hy]
          linarith
        · have hy : 17 / 5 ≤ y := by
            have : (22 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn22
            dsimp [y]; rw [h5]; norm_num; linarith
          have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 5) 7
          have hexp_mono := Real.exp_le_exp.mpr hy
          norm_num [Finset.sum_range_succ, Nat.factorial] at htay
          have hn_le : (n : ℝ) + 1 ≤ 26 := by exact_mod_cast (by omega : n + 1 ≤ 26)
          linarith
      · have hsq1 := hr₀_sq_le
        have hsq2 := hn_lt_sq
        rw [h6] at hsq1 hsq2
        norm_num at hsq1 hsq2
        have hn_range : 26 ≤ n ∧ n ≤ 36 := by omega
        rcases eq_or_lt_of_le hn_range.1 with rfl | hn27
        · have hy : y = 10 / 3 := by dsimp [y]; rw [h6]; norm_num
          have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 3) 8
          norm_num [Finset.sum_range_succ, Nat.factorial] at htay
          change (26 : ℝ) + 1 < Real.exp y
          rw [hy]
          linarith
        · rcases lt_or_ge n 30 with hn30 | hn30
          · have hy : 7 / 2 ≤ y := by
              have : (27 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn27
              dsimp [y]; rw [h6]; norm_num; linarith
            have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 2) 7
            have hexp_mono := Real.exp_le_exp.mpr hy
            norm_num [Finset.sum_range_succ, Nat.factorial] at htay
            have hn_le : (n : ℝ) + 1 ≤ 30 := by exact_mod_cast (by omega : n + 1 ≤ 30)
            linarith
          · have hy : 4 ≤ y := by
              have : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn30
              dsimp [y]; rw [h6]; norm_num; linarith
            have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 7
            have hexp_mono := Real.exp_le_exp.mpr hy
            norm_num [Finset.sum_range_succ, Nat.factorial] at htay
            have hn_le : (n : ℝ) + 1 ≤ 37 := by exact_mod_cast (by omega : n + 1 ≤ 37)
            linarith
      · have hsq1 := hr₀_sq_le
        have hsq2 := hn_lt_sq
        rw [h7] at hsq1 hsq2
        norm_num at hsq1 hsq2
        have hn_range : 37 ≤ n ∧ n ≤ 49 := by omega
        have hy : 30 / 7 ≤ y := by
          have : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_range.1
          dsimp [y]; rw [h7]; norm_num; linarith
        have htay := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 30 / 7) 7
        have hexp_mono := Real.exp_le_exp.mpr hy
        norm_num [Finset.sum_range_succ, Nat.factorial] at htay
        have hn_le : (n : ℝ) + 1 ≤ 50 := by exact_mod_cast (by omega : n + 1 ≤ 50)
        linarith
    · have hy_lower : (r₀ : ℝ) - 3 ≤ y := by
        have hsq_nat : (r₀ - 1) ^ 2 + 1 ≤ n := by omega
        have hsq : ((r₀ : ℝ) - 1) ^ 2 + 1 ≤ (n : ℝ) := by
          have hr1 : ((r₀ - 1 : ℕ) : ℝ) = (r₀ : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ r₀), Nat.cast_one]
          have hsq' : ((r₀ - 1 : ℕ) : ℝ) ^ 2 + 1 ≤ (n : ℝ) := by exact_mod_cast hsq_nat
          rwa [hr1] at hsq'
        dsimp [y]
        rw [le_sub_iff_add_le, le_div_iff₀ hr₀_pos]
        nlinarith
      have hy5 : (5 : ℝ) ≤ y := by
        have : (8 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀_ge8
        linarith
      have htay := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ y) 5
      have hpoly : (n : ℝ) + 1 <
          ∑ k ∈ Finset.range 5, y ^ k / (k.factorial : ℝ) := by
        have hn_upper : (n : ℝ) + 1 ≤ (r₀ : ℝ) ^ 2 + 1 := by
          exact_mod_cast (by omega : n + 1 ≤ r₀ ^ 2 + 1)
        have hbound : (r₀ : ℝ) ^ 2 + 1 ≤ (y + 3) ^ 2 + 1 := by nlinarith
        set t : ℝ := y - 5
        have hy_eq : y = t + 5 := by dsimp [t]; ring
        have hstrict : (y + 3) ^ 2 + 1 < ∑ k ∈ Finset.range 5, y ^ k / (k.factorial : ℝ) := by
          simp only [Finset.sum_range_succ, Nat.factorial]
          rw [hy_eq]
          norm_num
          nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
        linarith
      exact hpoly.trans_le htay
  have hlog_lt : Real.log ((n : ℝ) + 1) < (n : ℝ) / (r₀ : ℝ) - 1 :=
    (Real.log_lt_iff_lt_exp (by positivity)).mpr hexp
  have hr₀_pos : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 0 < r₀)
  rw [lt_div_iff₀ hlogpos]
  have hmul : (r₀ : ℝ) * (Real.log ((n : ℝ) + 1) + 1) < (r₀ : ℝ) * ((n : ℝ) / (r₀ : ℝ)) := by
    exact mul_lt_mul_of_pos_left (by linarith) hr₀_pos
  rwa [mul_div_cancel₀ _ hr₀_pos.ne'] at hmul

private lemma two_mul_66_64_mul_pow_eight_lt {n : ℕ} (hn : 21 ≤ n) :
    2 * 66 * 64 * 8 ^ n < 65 * 25 * 9 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m _hm ih =>
    calc
      2 * 66 * 64 * 8 ^ (m + 1) = 8 * (2 * 66 * 64 * 8 ^ m) := by rw [pow_succ']; ring
      _ < 8 * (65 * 25 * 9 ^ m) := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ 9 * (65 * 25 * 9 ^ m) := Nat.mul_le_mul_right _ (by omega)
      _ = 65 * 25 * 9 ^ (m + 1) := by rw [pow_succ']; ring

/-- For `3 ≤ r ≤ n - 2`, `2 * A(n, 3 * r - 2) < A(n, r - 1) * (A(n, r - 1) - 1)`
(Lawrence–Sawin, Lemma C.4). -/
theorem two_mul_eulerianNumber_lt_mul_sub_one {n r : ℕ} (hr : 3 ≤ r) (hrn : r ≤ n - 2) :
    2 * eulerianNumber n (3 * r - 2) <
      eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) := by
  have hn5 : 5 ≤ n := by omega
  have h66 : 66 ≤ eulerianNumber n (r - 1) := eulerianNumber_ge_66_of_three_le hr hrn
  rcases le_or_gt n (3 * r - 2) with hzero | hlt
  · rw [eulerianNumber_eq_zero_of_le (by omega) hzero, mul_zero]
    exact Nat.mul_pos (by omega) (by omega)
  · rcases lt_or_ge n 21 with hn20 | hn21
    · have hcheck : ∀ m ∈ Finset.Icc 5 20, ∀ s ∈ Finset.Icc 3 (m - 2),
          2 * (eulerianRow m).getD (3 * s - 2) 0 <
            (eulerianRow m).getD (s - 1) 0 * ((eulerianRow m).getD (s - 1) 0 - 1) := by
        decide
      have := hcheck n (Finset.mem_Icc.mpr ⟨hn5, by omega⟩) r (Finset.mem_Icc.mpr ⟨hr, hrn⟩)
      simpa only [eulerianRow_getD] using this
    · have h58 := one_sub_exp_neg_one_gt_five_eighths
      have hprod : (65 : ℝ) * 64 * (eulerianNumber n (r - 1) : ℝ) ^ 2 ≤
          66 * 64 * ((eulerianNumber n (r - 1) : ℝ) * ((eulerianNumber n (r - 1) : ℝ) - 1)) := by
        have h66r : (66 : ℝ) ≤ (eulerianNumber n (r - 1) : ℝ) := by exact_mod_cast h66
        nlinarith
      have hlhs : (eulerianNumber n (r - 1) : ℝ) * ((eulerianNumber n (r - 1) : ℝ) - 1) =
          ((eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) : ℕ) : ℝ) := by
        have hpos : 1 ≤ eulerianNumber n (r - 1) := by omega
        rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]
      rcases lt_or_ge (r : ℝ) ((n : ℝ) / (Real.log ((n : ℝ) + 1) + 1)) with hsmall | hlarge
      · have hlow := one_sub_exp_neg_one_mul_pow_le_eulerianNumber (n := n) (q := r - 1)
          (by omega)
          (by
            rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one, sub_add_cancel]
            exact hsmall)
        have hlow' : (5 : ℝ) / 8 * (r : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) := by
          have hr_eq : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]; ring
          rw [hr_eq] at hlow
          have : (5 : ℝ) / 8 * (r : ℝ) ^ n ≤ (1 - Real.exp (-1)) * (r : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right h58.le (by positivity)
          exact this.trans hlow
        have hsq : (25 : ℝ) / 64 * ((r : ℝ) ^ 2) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := by
          calc
            (25 : ℝ) / 64 * ((r : ℝ) ^ 2) ^ n = ((5 : ℝ) / 8 * (r : ℝ) ^ n) ^ 2 := by
              rw [mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]; norm_num
            _ ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hlow' 2
        have hup : (eulerianNumber n (3 * r - 2) : ℝ) ≤ (3 * (r : ℝ) - 1) ^ n := by
          have hup_nat : (eulerianNumber n (3 * r - 2) : ℝ) ≤
              (((3 * r - 2 : ℕ) : ℝ) + 1) ^ n := by
            exact_mod_cast eulerianNumber_le_pow n (3 * r - 2)
          have hr_eq : ((3 * r - 2 : ℕ) : ℝ) + 1 = 3 * (r : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 2 ≤ 3 * r)]; push_cast; ring
          exact hup_nat.trans_eq (by rw [hr_eq])
        have hstep : 9 * (3 * (r : ℝ) - 1) ≤ 8 * (r : ℝ) ^ 2 := by
          have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
          nlinarith
        have hup2 : 9 ^ n * (eulerianNumber n (3 * r - 2) : ℝ) ≤ 8 ^ n * ((r : ℝ) ^ 2) ^ n := by
          calc
            9 ^ n * (eulerianNumber n (3 * r - 2) : ℝ)
                ≤ 9 ^ n * (3 * (r : ℝ) - 1) ^ n := mul_le_mul_of_nonneg_left hup (by positivity)
            _ = (9 * (3 * (r : ℝ) - 1)) ^ n := (mul_pow _ _ _).symm
            _ ≤ (8 * (r : ℝ) ^ 2) ^ n := pow_le_pow_left₀ (by
              have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
              nlinarith) hstep n
            _ = 8 ^ n * ((r : ℝ) ^ 2) ^ n := mul_pow _ _ _
        have hnat_r : (2 : ℝ) * 66 * 64 * 8 ^ n < 65 * 25 * 9 ^ n := by
          exact_mod_cast two_mul_66_64_mul_pow_eight_lt hn21
        have hreal : (2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ) <
            (eulerianNumber n (r - 1) : ℝ) * ((eulerianNumber n (r - 1) : ℝ) - 1) := by
          have hB : (65 : ℝ) * 25 * 9 ^ n * ((r : ℝ) ^ 2) ^ n ≤
              66 * 64 * 9 ^ n * ((eulerianNumber n (r - 1) : ℝ) *
                ((eulerianNumber n (r - 1) : ℝ) - 1)) := by
            have : (65 : ℝ) * 25 * ((r : ℝ) ^ 2) ^ n ≤
                66 * 64 * ((eulerianNumber n (r - 1) : ℝ) *
                  ((eulerianNumber n (r - 1) : ℝ) - 1)) := by linarith
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) n]
          have hr2_pos : 0 < ((r : ℝ) ^ 2) ^ n := by
            have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
            positivity
          have hAB : 66 * 64 * 9 ^ n * ((2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ)) <
              66 * 64 * 9 ^ n * ((eulerianNumber n (r - 1) : ℝ) *
                ((eulerianNumber n (r - 1) : ℝ) - 1)) := by
            have hA : 66 * 64 * 9 ^ n * ((2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ)) ≤
                2 * 66 * 64 * 8 ^ n * ((r : ℝ) ^ 2) ^ n := by nlinarith
            have hmul : (2 : ℝ) * 66 * 64 * 8 ^ n * ((r : ℝ) ^ 2) ^ n <
                65 * 25 * 9 ^ n * ((r : ℝ) ^ 2) ^ n :=
              mul_lt_mul_of_pos_right hnat_r hr2_pos
            exact (hA.trans_lt hmul).trans_le hB
          exact lt_of_mul_lt_mul_left hAB (by positivity)
        rw [hlhs] at hreal
        exact_mod_cast hreal
      · set r₀ : ℕ := Nat.sqrt (n - 1) + 1
        have hr₀_lt := sqrt_pred_succ_lt_div_log hn21
        have hr₀_lt_r : (r₀ : ℝ) < (r : ℝ) := hr₀_lt.trans_le hlarge
        have hr₀_le_r : r₀ ≤ r := by exact_mod_cast hr₀_lt_r.le
        have hr_half : r - 1 ≤ n / 2 := by omega
        have hr₀_half : r₀ - 1 ≤ n / 2 := by omega
        have hmono : eulerianNumber n (r₀ - 1) ≤ eulerianNumber n (r - 1) :=
          eulerianNumber_monotoneOn n (Set.mem_Iic.mpr hr₀_half) (Set.mem_Iic.mpr hr_half)
            (by omega)
        have hlow := one_sub_exp_neg_one_mul_pow_le_eulerianNumber (n := n) (q := r₀ - 1)
          (by omega)
          (by
            have hr₀_ge1 : 1 ≤ r₀ := Nat.succ_pos _
            rw [Nat.cast_sub hr₀_ge1, Nat.cast_one, sub_add_cancel]
            dsimp [r₀]
            exact hr₀_lt)
        have hlow' : (5 : ℝ) / 8 * (r₀ : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) := by
          have hr₀_eq : ((r₀ - 1 : ℕ) : ℝ) + 1 = (r₀ : ℝ) := by
            rw [Nat.cast_sub (Nat.succ_pos _ : 1 ≤ r₀), Nat.cast_one]; ring
          rw [hr₀_eq] at hlow
          have h1 : (5 : ℝ) / 8 * (r₀ : ℝ) ^ n ≤ (1 - Real.exp (-1)) * (r₀ : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right h58.le (by positivity)
          have h2 : (eulerianNumber n (r₀ - 1) : ℝ) ≤ (eulerianNumber n (r - 1) : ℝ) := by
            exact_mod_cast hmono
          exact (h1.trans hlow).trans h2
        have hn_sq : (n : ℝ) ≤ (r₀ : ℝ) ^ 2 := by
          have hnat_sq : n ≤ r₀ ^ 2 := by
            have hlt_sqrt := Nat.lt_succ_sqrt (n - 1)
            dsimp [r₀]
            rw [Nat.pow_two]
            rw [Nat.succ_eq_add_one] at hlt_sqrt
            omega
          exact_mod_cast hnat_sq
        have hsq : (25 : ℝ) / 64 * (n : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := by
          calc
            (25 : ℝ) / 64 * (n : ℝ) ^ n ≤ (25 : ℝ) / 64 * ((r₀ : ℝ) ^ 2) ^ n :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn_sq n) (by norm_num)
            _ = ((5 : ℝ) / 8 * (r₀ : ℝ) ^ n) ^ 2 := by
              rw [mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]; norm_num
            _ ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hlow' 2
        have hfact_nat : 2 * 66 * 64 * n.factorial < 65 * 25 * n ^ n := by
          have h6 := six_mul_factorial_le_pow hn5
          have hpow_pos : 0 < n ^ n := Nat.pow_pos (by omega)
          calc
            2 * 66 * 64 * n.factorial = 1408 * (6 * n.factorial) := by ring
            _ ≤ 1408 * n ^ n := Nat.mul_le_mul_left 1408 h6
            _ < 1625 * n ^ n := Nat.mul_lt_mul_of_pos_right (by omega) hpow_pos
        have hup : eulerianNumber n (3 * r - 2) ≤ n.factorial := eulerianNumber_le_factorial n _
        have hreal : (2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ) <
            (eulerianNumber n (r - 1) : ℝ) * ((eulerianNumber n (r - 1) : ℝ) - 1) := by
          have h1 : (66 : ℝ) * 64 * (2 * (eulerianNumber n (3 * r - 2) : ℝ)) ≤
              2 * 66 * 64 * (n.factorial : ℝ) := by exact_mod_cast (by nlinarith)
          have h2 : (2 : ℝ) * 66 * 64 * (n.factorial : ℝ) < 65 * 25 * (n : ℝ) ^ n := by
            exact_mod_cast hfact_nat
          linarith
        rw [hlhs] at hreal
        exact_mod_cast hreal

end TauCeti
