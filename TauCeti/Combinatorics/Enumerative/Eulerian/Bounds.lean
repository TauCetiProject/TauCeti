/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Eulerian.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Basic
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
  `((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ)`.
* `TauCeti.one_sub_exp_neg_one_mul_pow_le_eulerianNumber`:
  `(1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ eulerianNumber n q` when
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
  simpa [eulerianNumber_def, Fintype.card_perm, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (fun σ => σ.descentCount = q)

/-- Additive form of the lower bound in Lemma C.1:
`(q + 1) ^ n ≤ eulerianNumber n q + (n + 1) * q ^ n`. -/
theorem pow_le_eulerianNumber_add_mul_pow (n q : ℕ) :
    (q + 1) ^ n ≤ eulerianNumber n q + (n + 1) * q ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases q <;> simp
  cases q with
  | zero =>
    rw [zero_add, one_pow, eulerianNumber_zero_right, zero_pow hn.ne', mul_zero, add_zero]
  | succ p =>
    have hsub : n + (p + 1) - (p + 1) = n := by omega
    rw [pow_eq_sum_eulerianNumber_mul_choose n (p + 1), Finset.sum_range_succ,
      hsub, Nat.choose_self, mul_one, add_comm]
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
        have hsub' : m + 1 - n = p - j + 1 := by omega
        simpa [hsub', Nat.mul_comm] using (Nat.choose_mul_succ_eq m n).symm
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
`((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ)`. -/
theorem pow_sub_mul_pow_le_eulerianNumber (n q : ℕ) :
    ((q : ℤ) + 1) ^ n - ((n : ℤ) + 1) * (q : ℤ) ^ n ≤ (eulerianNumber n q : ℤ) :=
  sub_le_iff_le_add.mpr (by exact_mod_cast pow_le_eulerianNumber_add_mul_pow n q)

/-- Real lower bound on Eulerian numbers with few descents (Lawrence–Sawin, Lemma C.3):
for `(q : ℝ) + 1 < n / (Real.log (n + 1) + 1)`,
`(1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ eulerianNumber n q`. -/
theorem one_sub_exp_neg_one_mul_pow_le_eulerianNumber {n q : ℕ}
    (hq : (q : ℝ) + 1 < (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1)) :
    (1 - Real.exp (-1)) * ((q : ℝ) + 1) ^ n ≤ (eulerianNumber n q : ℝ) := by
  have hc1 : ((q : ℝ) + 1) ^ n ≤ (eulerianNumber n q : ℝ) + ((n : ℝ) + 1) * (q : ℝ) ^ n := by
    exact_mod_cast pow_le_eulerianNumber_add_mul_pow n q
  have hkey := mul_pow_lt_exp_neg_one_mul_pow (Nat.cast_nonneg q) hq
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

private lemma nextEulerianRow_getD_succ (row : List ℕ) (k : ℕ) :
    (nextEulerianRow row).getD (k + 1) 0 =
      if k < row.length then
        (k + 2) * row.getD (k + 1) 0 + (row.length - 1 - k) * row.getD k 0
      else 0 := by
  simp only [nextEulerianRow, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  have hlen_zip : (List.zipWith
      (fun j p => (j + 2) * p.1 + (row.length - 1 - j) * p.2)
      (List.range row.length) (List.zip (row.drop 1 ++ [0]) row)).length = row.length := by
    simp only [List.length_zipWith, List.length_range, List.length_zip, List.length_append,
      List.length_drop, List.length_singleton]
    omega
  split_ifs with hk
  · have hk' : k < (List.zipWith _ _ _).length := hlen_zip ▸ hk
    rw [List.getElem?_eq_getElem hk', Option.getD_some, List.getElem_zipWith]
    simp only [List.getElem_range, List.getElem_zip]
    have hdrop : (row.drop 1 ++ [0])[k]'(by
        simp only [List.length_append, List.length_drop, List.length_singleton]; omega) =
        (row[k + 1]?).getD 0 := by
      rcases lt_or_ge (k + 1) row.length with hk1 | hk1
      · have hlt_drop : k < (row.drop 1).length := by simp; omega
        rw [List.getElem_append_left hlt_drop, List.getElem_drop,
          List.getElem?_eq_getElem hk1, Option.getD_some]
        congr 1; omega
      · have hlen_drop : (row.drop 1).length = row.length - 1 := List.length_drop
        rw [List.getElem_append_right (by omega : (row.drop 1).length ≤ k)]
        simp [List.getElem?_eq_none hk1]
    rw [hdrop, List.getElem?_eq_getElem hk, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [hlen_zip]; exact Nat.le_of_not_lt hk), Option.getD_none]

private lemma eulerianRow_getD (n q : ℕ) :
    (eulerianRow n).getD q 0 = eulerianNumber n q := by
  induction n generalizing q with
  | zero => cases q <;> simp [eulerianRow]
  | succ n ih =>
    cases q with
    | zero => simp [eulerianRow, nextEulerianRow]
    | succ k =>
      rw [eulerianRow, nextEulerianRow_getD_succ, eulerianRow_length]
      split_ifs with hk
      · rw [ih (k + 1), ih k, Nat.add_sub_cancel, eulerianNumber_succ_succ]
      · exact (eulerianNumber_eq_zero_of_le (by omega) (by omega)).symm

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
      have hsub : n - 1 - (n - 3) = 2 := by omega
      rw [eulerianNumber_symm (by omega), hsub]
    calc
      66 ≤ eulerianNumber n 2 := eulerianNumber_two_ge_66 hn
      _ = eulerianNumber n (n - 3) := hsym.symm
      _ ≤ eulerianNumber n (r - 1) :=
        eulerianNumber_antitoneOn n (Set.mem_Ici.mpr hle') (Set.mem_Ici.mpr (by omega)) (by omega)

/-- For `11 ≤ n`, `27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2`
(Lawrence–Sawin, Lemma C.5). -/
theorem mul_eulerianNumber_two_lt_sq {n : ℕ} (hn : 11 ≤ n) :
    27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2 := by
  have h : 27 * n ≤ eulerianNumber n 1 ∧ 27 * eulerianNumber n 2 < eulerianNumber n 1 ^ 2 := by
    induction n, hn using Nat.le_induction with
    | base =>
      rw [← eulerianRow_getD, ← eulerianRow_getD]
      decide
    | succ m _hm ih =>
      rcases ih with ⟨ha, hb⟩
      have ha_succ : eulerianNumber (m + 1) 1 = 2 * eulerianNumber m 1 + m := by
        rw [eulerianNumber_succ_succ, eulerianNumber_zero_right, mul_one, Nat.sub_zero]
      have hb_succ : eulerianNumber (m + 1) 2 =
          3 * eulerianNumber m 2 + (m - 1) * eulerianNumber m 1 := by
        rw [eulerianNumber_succ_succ]
      refine ⟨?_, ?_⟩
      · rw [ha_succ]
        omega
      · rw [ha_succ, hb_succ]
        have h1 : 27 * (m - 1) * eulerianNumber m 1 ≤ eulerianNumber m 1 ^ 2 := by
          calc
            27 * (m - 1) * eulerianNumber m 1 ≤ 27 * m * eulerianNumber m 1 := by
              gcongr; omega
            _ ≤ eulerianNumber m 1 * eulerianNumber m 1 := Nat.mul_le_mul_right _ ha
            _ = eulerianNumber m 1 ^ 2 := (sq _).symm
        nlinarith
  exact h.2

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

private lemma mul_sq_le_sixtySix_mul_sub_one {n r : ℕ} (h66 : 66 ≤ eulerianNumber n (r - 1)) :
    (65 : ℝ) * 64 * (eulerianNumber n (r - 1) : ℝ) ^ 2 ≤
      66 * 64 * ((eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) : ℕ) : ℝ) := by
  have h66r : (66 : ℝ) ≤ (eulerianNumber n (r - 1) : ℝ) := by exact_mod_cast h66
  have hpos : 1 ≤ eulerianNumber n (r - 1) := by omega
  rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]
  nlinarith

private lemma two_mul_eulerianNumber_lt_of_small_r {n r : ℕ} (hn : 21 ≤ n) (hr : 3 ≤ r)
    (h66 : 66 ≤ eulerianNumber n (r - 1))
    (hsmall : (r : ℝ) < (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1)) :
    2 * eulerianNumber n (3 * r - 2) <
      eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) := by
  have hlow := one_sub_exp_neg_one_mul_pow_le_eulerianNumber (n := n) (q := r - 1)
    (by rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one, sub_add_cancel]; exact hsmall)
  have hlow' : (5 : ℝ) / 8 * (r : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) := by
    have hr_eq : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]; ring
    rw [hr_eq] at hlow
    exact (mul_le_mul_of_nonneg_right five_eighths_lt_one_sub_exp_neg_one.le (by positivity)).trans
      hlow
  have hsq : (25 : ℝ) / 64 * ((r : ℝ) ^ 2) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := by
    calc
      (25 : ℝ) / 64 * ((r : ℝ) ^ 2) ^ n = ((5 : ℝ) / 8 * (r : ℝ) ^ n) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]; norm_num
      _ ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hlow' 2
  have hup : (eulerianNumber n (3 * r - 2) : ℝ) ≤ (3 * (r : ℝ) - 1) ^ n := by
    have hup_nat : (eulerianNumber n (3 * r - 2) : ℝ) ≤ (((3 * r - 2 : ℕ) : ℝ) + 1) ^ n := by
      exact_mod_cast eulerianNumber_le_pow n (3 * r - 2)
    have hr_eq : ((3 * r - 2 : ℕ) : ℝ) + 1 = 3 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 3 * r)]; push_cast; ring
    exact hup_nat.trans_eq (by rw [hr_eq])
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hup2 : 9 ^ n * (eulerianNumber n (3 * r - 2) : ℝ) ≤ 8 ^ n * ((r : ℝ) ^ 2) ^ n := by
    calc
      9 ^ n * (eulerianNumber n (3 * r - 2) : ℝ)
          ≤ 9 ^ n * (3 * (r : ℝ) - 1) ^ n := mul_le_mul_of_nonneg_left hup (by positivity)
      _ = (9 * (3 * (r : ℝ) - 1)) ^ n := (mul_pow _ _ _).symm
      _ ≤ (8 * (r : ℝ) ^ 2) ^ n := pow_le_pow_left₀ (by nlinarith) (by nlinarith) n
      _ = 8 ^ n * ((r : ℝ) ^ 2) ^ n := mul_pow _ _ _
  have hnat_r : (2 : ℝ) * 66 * 64 * 8 ^ n < 65 * 25 * 9 ^ n := by
    exact_mod_cast two_mul_66_64_mul_pow_eight_lt hn
  have hprod := mul_sq_le_sixtySix_mul_sub_one h66
  have hA : 66 * 64 * 9 ^ n * ((2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ)) ≤
      2 * 66 * 64 * 8 ^ n * ((r : ℝ) ^ 2) ^ n := by nlinarith
  have hmul : (2 : ℝ) * 66 * 64 * 8 ^ n * ((r : ℝ) ^ 2) ^ n <
      65 * 25 * 9 ^ n * ((r : ℝ) ^ 2) ^ n := mul_lt_mul_of_pos_right hnat_r (by positivity)
  have hB : (65 : ℝ) * 25 * 9 ^ n * ((r : ℝ) ^ 2) ^ n ≤ 66 * 64 * 9 ^ n *
      ((eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) : ℕ) : ℝ) := by
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) n]
  exact_mod_cast lt_of_mul_lt_mul_left ((hA.trans_lt hmul).trans_le hB) (by positivity)

private lemma two_mul_eulerianNumber_lt_of_large_r {n r : ℕ} (hn : 21 ≤ n) (hlt : 3 * r - 2 < n)
    (h66 : 66 ≤ eulerianNumber n (r - 1))
    (hlarge : (n : ℝ) / (Real.log ((n : ℝ) + 1) + 1) ≤ (r : ℝ)) :
    2 * eulerianNumber n (3 * r - 2) <
      eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) := by
  set r₀ : ℕ := Nat.sqrt (n - 1) + 1
  have hr₀_lt := natSqrt_pred_add_one_lt_div_log hn
  have hr₀_le_r : r₀ ≤ r := by exact_mod_cast (hr₀_lt.trans_le hlarge).le
  have hmono : eulerianNumber n (r₀ - 1) ≤ eulerianNumber n (r - 1) :=
    eulerianNumber_monotoneOn n (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega))
      (by omega)
  have hlow := one_sub_exp_neg_one_mul_pow_le_eulerianNumber (n := n) (q := r₀ - 1)
    (by rw [Nat.cast_sub (Nat.succ_pos _), Nat.cast_one, sub_add_cancel]; exact hr₀_lt)
  have hlow' : (5 : ℝ) / 8 * (r₀ : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) := by
    have hr₀_eq : ((r₀ - 1 : ℕ) : ℝ) + 1 = (r₀ : ℝ) := by
      rw [Nat.cast_sub (Nat.succ_pos _), Nat.cast_one]; ring
    rw [hr₀_eq] at hlow
    have h1 := mul_le_mul_of_nonneg_right five_eighths_lt_one_sub_exp_neg_one.le
      (by positivity : 0 ≤ (r₀ : ℝ) ^ n)
    exact (h1.trans hlow).trans (by exact_mod_cast hmono)
  have hn_sq : (n : ℝ) ≤ (r₀ : ℝ) ^ 2 := by
    have hlt_sqrt := Nat.lt_succ_sqrt (n - 1)
    exact_mod_cast (by dsimp [r₀]; rw [Nat.pow_two]; rw [Nat.succ_eq_add_one] at hlt_sqrt; omega :
      n ≤ r₀ ^ 2)
  have hsq : (25 : ℝ) / 64 * (n : ℝ) ^ n ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := by
    calc
      (25 : ℝ) / 64 * (n : ℝ) ^ n ≤ (25 : ℝ) / 64 * ((r₀ : ℝ) ^ 2) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn_sq n) (by norm_num)
      _ = ((5 : ℝ) / 8 * (r₀ : ℝ) ^ n) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]; norm_num
      _ ≤ (eulerianNumber n (r - 1) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hlow' 2
  have hfact_nat : 2 * 66 * 64 * n.factorial < 65 * 25 * n ^ n := by
    have h6 := Nat.six_mul_factorial_le_pow (by omega : 4 ≤ n)
    calc
      2 * 66 * 64 * n.factorial = 1408 * (6 * n.factorial) := by ring
      _ ≤ 1408 * n ^ n := Nat.mul_le_mul_left 1408 h6
      _ < 1625 * n ^ n := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
  have hup : eulerianNumber n (3 * r - 2) ≤ n.factorial := eulerianNumber_le_factorial n _
  have hprod := mul_sq_le_sixtySix_mul_sub_one h66
  have h1 : (66 : ℝ) * 64 * (2 * (eulerianNumber n (3 * r - 2) : ℝ)) ≤
      2 * 66 * 64 * (n.factorial : ℝ) := by exact_mod_cast (by nlinarith)
  have h2 : (2 : ℝ) * 66 * 64 * (n.factorial : ℝ) < 65 * 25 * (n : ℝ) ^ n := by
    exact_mod_cast hfact_nat
  exact_mod_cast (by linarith : (2 : ℝ) * (eulerianNumber n (3 * r - 2) : ℝ) <
    ((eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) : ℕ) : ℝ))

/-- For `3 ≤ r ≤ n - 2`, `2 * A(n, 3 * r - 2) < A(n, r - 1) * (A(n, r - 1) - 1)`
(Lawrence–Sawin, Lemma C.4). -/
theorem two_mul_eulerianNumber_lt_mul_sub_one {n r : ℕ} (hr : 3 ≤ r) (hrn : r ≤ n - 2) :
    2 * eulerianNumber n (3 * r - 2) <
      eulerianNumber n (r - 1) * (eulerianNumber n (r - 1) - 1) := by
  have hn5 : 5 ≤ n := by omega
  have h66 : 66 ≤ eulerianNumber n (r - 1) := eulerianNumber_ge_66_of_three_le hr hrn
  -- First handle the vanishing range `n ≤ 3 * r - 2`.
  rcases le_or_gt n (3 * r - 2) with hzero | hlt
  · rw [eulerianNumber_eq_zero_of_le (by omega) hzero, mul_zero]
    exact Nat.mul_pos (by omega) (by omega)
  -- For `5 ≤ n ≤ 20`, verify directly via the computable row table `eulerianRow`.
  · rcases lt_or_ge n 21 with hn20 | hn21
    · have hcheck : ∀ m ∈ Finset.Icc 5 20, ∀ s ∈ Finset.Icc 3 (m - 2),
          2 * (eulerianRow m).getD (3 * s - 2) 0 <
            (eulerianRow m).getD (s - 1) 0 * ((eulerianRow m).getD (s - 1) 0 - 1) := by
        decide
      have := hcheck n (Finset.mem_Icc.mpr ⟨hn5, by omega⟩) r (Finset.mem_Icc.mpr ⟨hr, hrn⟩)
      simpa only [eulerianRow_getD] using this
    -- For `n ≥ 21`, split at `r = n / (log (n + 1) + 1)`: small `r` bounds
    -- `A(n, 3r - 2) ≤ (3r - 1)^n`, while large `r` uses `r₀ = ⌊√(n - 1)⌋ + 1` and `n!`.
    · rcases lt_or_ge (r : ℝ) ((n : ℝ) / (Real.log ((n : ℝ) + 1) + 1)) with hsmall | hlarge
      · exact two_mul_eulerianNumber_lt_of_small_r hn21 hr h66 hsmall
      · exact two_mul_eulerianNumber_lt_of_large_r hn21 hlt h66 hlarge

end TauCeti
