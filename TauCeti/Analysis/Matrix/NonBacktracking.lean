/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.LinearAlgebra.Matrix.NonBacktracking
import TauCeti.Analysis.Matrix.EntrywiseOpNorm
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Operator norms of non-backtracking walk matrices

Let `H` be a Hermitian matrix whose entries have norm at most `b ≤ 1` and whose rows have squared
norms at most `d`. The non-backtracking recursion `Matrix.nonbacktrackingPow_add_three` expresses
the walk matrix of length `k + 3` through those of lengths `k + 2` and `k + 1`, up to the
correction `Matrix.nonbacktrackingMul G H k` for the walks that traverse their first edge three
times, where `G i w = H i w * (H w i * H i w)` is `H i w` weighted by `|H i w|²`. This file shows
that all such corrections are small when the entries are: their Euclidean operator norms are at
most `b * d` times `1` plus the norms of the walk matrices of length at most `k`. In particular,
for entries of norm at most `1`, the walk matrices of length `k` have operator norm at most
`(‖H‖ + 2 * d + 2) ^ k`.

For a sample covariance matrix `Y * Yᴴ`, where the entries of the `p × n` matrix `Y` are of
order `n^(-1/2)`, the Hermitian dilation of `Y` has `b → 0` while `d` stays bounded. These bounds
are the deterministic input that makes the corrections of the non-backtracking recursion
negligible in Bai and Yin's analysis of the smallest eigenvalue.

## Main results

* `Matrix.IsHermitian.l2_opNorm_nonbacktrackingMul_le`: the correction terms, for the weights
  `H i w * (H w i * H i w) ^ r` with `r ≠ 0`, have operator norm at most
  `b * d * (1 + ∑ j ≤ k, ‖nonbacktrackingPow H j‖)`.
* `Matrix.IsHermitian.l2_opNorm_nonbacktrackingPow_le`: for entries of norm at most `1`, the walk
  matrix of length `k` has operator norm at most `(‖H‖ + 2 * d + 2) ^ k`.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Finset
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜] {H : Matrix ι ι 𝕜} {b d : ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- The entries of the weights `H i j * (H j i * H i j) ^ r` of a Hermitian `H` have norm
`‖H i j‖ ^ (2 * r + 1)`. -/
private theorem IsHermitian.norm_mul_pow_apply (hH : H.IsHermitian) (r : ℕ) (i j : ι) :
    ‖H i j * (H j i * H i j) ^ r‖ = ‖H i j‖ ^ (2 * r + 1) := by
  rw [norm_mul, norm_pow, norm_mul, ← hH.apply i j, norm_star]
  ring

/-- For `r ≠ 0` and `s ≠ 0`, the power `x ^ (2 * r + s)` of `0 ≤ x ≤ b ≤ 1` is at most
`b * x ^ 2`. -/
private theorem pow_le_mul_sq {x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hb : b ≤ 1) {r : ℕ} (hr : r ≠ 0)
    {s : ℕ} (hs : s ≠ 0) : x ^ (2 * r + s) ≤ b * x ^ 2 := by
  have hx1 : x ≤ 1 := hxb.trans hb
  calc x ^ (2 * r + s) = x ^ (2 * r + s - 3) * x * x ^ 2 := by
        rw [mul_assoc, ← pow_succ', ← pow_add]
        congr 1
        omega
    _ ≤ 1 * b * x ^ 2 := by
        gcongr
        exact pow_le_one₀ hx hx1
    _ = b * x ^ 2 := by ring

/-- The weights `H i j * (H j i * H i j) ^ r` with `r ≠ 0` have operator norm at most `b * d`, by
the Schur test. -/
private theorem IsHermitian.l2_opNorm_of_mul_pow_le (hH : H.IsHermitian) (hb₀ : 0 ≤ b)
    (hb : b ≤ 1) (hd : 0 ≤ d) (hentry : ∀ i j, ‖H i j‖ ≤ b) (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ d)
    {r : ℕ} (hr : r ≠ 0) : ‖(of fun i j ↦ H i j * (H j i * H i j) ^ r : Matrix ι ι 𝕜)‖ ≤ b * d := by
  have hsum (i : ι) : ∑ j, ‖H i j‖ ^ (2 * r + 1) ≤ b * d :=
    (sum_le_sum fun j _ ↦ pow_le_mul_sq (norm_nonneg _) (hentry i j) hb hr one_ne_zero).trans
      (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hrow i) hb₀)
  refine (l2_opNorm_le_sqrt_mul_of_row_col_sum_le _ (r := b * d) (c := b * d) (fun i ↦ ?_)
    fun j ↦ ?_).trans_eq (Real.sqrt_mul_self (mul_nonneg hb₀ hd))
  · simpa only [of_apply, hH.norm_mul_pow_apply] using hsum i
  · simp only [of_apply, hH.norm_mul_pow_apply]
    refine le_of_eq_of_le (sum_congr rfl fun i _ ↦ ?_) (hsum j)
    rw [← hH.apply i j, norm_star]

/-- The diagonal weights of the steps going back and forth, for the weights
`H i j * (H j i * H i j) ^ r` with `r ≠ 0`, have operator norm at most `b * d`. -/
private theorem IsHermitian.l2_opNorm_diagonal_sum_mul_pow_le (hH : H.IsHermitian) (hb₀ : 0 ≤ b)
    (hb : b ≤ 1) (hd : 0 ≤ d) (hentry : ∀ i j, ‖H i j‖ ≤ b) (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ d)
    {r : ℕ} (hr : r ≠ 0) :
    ‖(diagonal fun i ↦
        ∑ w, (of fun i j ↦ H i j * (H j i * H i j) ^ r : Matrix ι ι 𝕜) i w * H w i)‖ ≤ b * d := by
  rw [l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb₀ hd)).mpr fun i ↦ ?_
  calc _ ≤ ∑ w, ‖H i w * (H w i * H i w) ^ r * H w i‖ := norm_sum_le _ _
    _ = ∑ w, ‖H i w‖ ^ (2 * r + 2) := by
        refine sum_congr rfl fun w _ ↦ ?_
        rw [norm_mul, hH.norm_mul_pow_apply, ← hH.apply i w, norm_star]
        ring
    _ ≤ ∑ w, b * ‖H i w‖ ^ 2 :=
        sum_le_sum fun w _ ↦ pow_le_mul_sq (norm_nonneg _) (hentry i w) hb hr two_ne_zero
    _ ≤ b * d := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hrow i) hb₀

/-- **The corrections of the non-backtracking recursion are small.** Let `H` be Hermitian with
entries of norm at most `b`, where `0 ≤ b ≤ 1`, and rows of squared norm at most `d ≥ 0`. For
`r ≠ 0`, a first step weighted by `H i w * (H w i * H i w) ^ r` followed by a non-backtracking walk
of length `k` gives a matrix of operator norm at most
`b * d * (1 + ∑ j ≤ k, ‖nonbacktrackingPow H j‖)`. The case `r = 1` is the correction in
`Matrix.nonbacktrackingPow_add_three`. -/
theorem IsHermitian.l2_opNorm_nonbacktrackingMul_le (hH : H.IsHermitian) (hb₀ : 0 ≤ b)
    (hb : b ≤ 1) (hd : 0 ≤ d) (hentry : ∀ i j, ‖H i j‖ ≤ b) (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ d)
    {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    ‖nonbacktrackingMul (of fun i j ↦ H i j * (H j i * H i j) ^ r) H k‖ ≤
      b * d * (1 + ∑ j ∈ range (k + 1), ‖nonbacktrackingPow H j‖) := by
  have hbd : 0 ≤ b * d := mul_nonneg hb₀ hd
  have hS (m : ℕ) : 0 ≤ ∑ j ∈ range m, ‖nonbacktrackingPow H j‖ :=
    sum_nonneg fun _ _ ↦ norm_nonneg _
  induction k using Nat.strong_induction_on generalizing r with
  | _ k ih =>
  have hG := hH.l2_opNorm_of_mul_pow_le hb₀ hb hd hentry hrow hr
  have hD := hH.l2_opNorm_diagonal_sum_mul_pow_le hb₀ hb hd hentry hrow hr
  match k with
  | 0 =>
    rw [nonbacktrackingMul_zero]
    nlinarith [hS 1]
  | 1 =>
    rw [nonbacktrackingMul_one, sum_range_succ, sum_range_one, nonbacktrackingPow_one]
    calc _ ≤ ‖(of fun i j ↦ H i j * (H j i * H i j) ^ r : Matrix ι ι 𝕜)‖ * ‖H‖ + b * d :=
          (norm_sub_le _ _).trans (add_le_add (l2_opNorm_mul _ _) hD)
      _ ≤ b * d * ‖H‖ + b * d := by gcongr
      _ ≤ _ := by nlinarith [norm_nonneg (nonbacktrackingPow H 0), norm_nonneg H]
  | k + 2 =>
    -- The weights of the walks traversing the first edge three times are those for `r + 1`.
    have hG' : (of fun i w ↦ (of fun i j ↦ H i j * (H j i * H i j) ^ r : Matrix ι ι 𝕜) i w *
        (H w i * H i w)) = of fun i j ↦ H i j * (H j i * H i j) ^ (r + 1) := by
      ext i j
      simp [pow_succ, mul_assoc]
    rw [nonbacktrackingMul_add_two, hG']
    have ih' := ih k (by omega) (r := r + 1) (by omega)
    rw [sum_range_succ, sum_range_succ]
    calc _ ≤ ‖(of fun i j ↦ H i j * (H j i * H i j) ^ r : Matrix ι ι 𝕜)‖ *
          ‖nonbacktrackingPow H (k + 2)‖ + b * d * ‖nonbacktrackingPow H (k + 1)‖ +
          b * d * (1 + ∑ j ∈ range (k + 1), ‖nonbacktrackingPow H j‖) :=
          (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            (l2_opNorm_mul _ _) ((l2_opNorm_mul _ _).trans (by gcongr)))) ih')
      _ ≤ b * d * ‖nonbacktrackingPow H (k + 2)‖ + b * d * ‖nonbacktrackingPow H (k + 1)‖ +
          b * d * (1 + ∑ j ∈ range (k + 1), ‖nonbacktrackingPow H j‖) := by gcongr
      _ = _ := by ring

/-- `1 + ∑ j < k + 1, a ^ j ≤ a ^ (k + 1)` for `a ≥ 2`. -/
private theorem one_add_sum_range_pow_le {a : ℝ} (ha : 2 ≤ a) (k : ℕ) :
    1 + ∑ j ∈ range (k + 1), a ^ j ≤ a ^ (k + 1) := by
  induction k with
  | zero =>
    norm_num
    linarith
  | succ k ih =>
    rw [sum_range_succ, ← add_assoc, pow_succ a (k + 1)]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ a) (k + 1)]

/-- **A crude norm bound for non-backtracking walk matrices.** Let `H` be Hermitian with entries of
norm at most `1` and rows of squared norm at most `d ≥ 0`. Then the non-backtracking walk matrix
of length `k` has operator norm at most `(‖H‖ + 2 * d + 2) ^ k`. -/
theorem IsHermitian.l2_opNorm_nonbacktrackingPow_le (hH : H.IsHermitian) (hd : 0 ≤ d)
    (hentry : ∀ i j, ‖H i j‖ ≤ 1) (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ d) (k : ℕ) :
    ‖nonbacktrackingPow H k‖ ≤ (‖H‖ + 2 * d + 2) ^ k := by
  set a := ‖H‖ + 2 * d + 2
  have ha : 2 ≤ a := by have := norm_nonneg H; simp only [a]; linarith
  have hD : ‖(diagonal fun i ↦ ∑ w, H i w * H w i)‖ ≤ d := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hd).mpr fun i ↦ (norm_sum_le _ _).trans ?_
    refine le_of_eq_of_le (sum_congr rfl fun w _ ↦ ?_) (hrow i)
    rw [norm_mul, ← hH.apply i w, norm_star, sq]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  match k with
  | 0 => simpa using l2_opNorm_one_le
  | 1 => simpa [a] using (by linarith [norm_nonneg H] : ‖H‖ ≤ a)
  | 2 =>
    rw [nonbacktrackingPow_two]
    calc _ ≤ ‖H‖ * ‖H‖ + d := (norm_sub_le _ _).trans (add_le_add (l2_opNorm_mul _ _) hD)
      _ ≤ a ^ 2 := by nlinarith [norm_nonneg H]
  | k + 3 =>
    have hE := hH.l2_opNorm_nonbacktrackingMul_le zero_le_one le_rfl hd hentry hrow one_ne_zero k
    have hsum : 1 + ∑ j ∈ range (k + 1), ‖nonbacktrackingPow H j‖ ≤ a ^ (k + 1) := by
      refine le_trans ?_ (one_add_sum_range_pow_le ha k)
      gcongr with j hj
      exact ih j (by have := mem_range.mp hj; omega)
    have h2 := ih (k + 2) (by omega)
    have h1 := ih (k + 1) (by omega)
    have hak : 0 ≤ a ^ (k + 1) := pow_nonneg (by linarith) _
    simp only [pow_one] at hE
    rw [nonbacktrackingPow_add_three]
    calc _ ≤ ‖H‖ * ‖nonbacktrackingPow H (k + 2)‖ + d * ‖nonbacktrackingPow H (k + 1)‖ +
          1 * d * (1 + ∑ j ∈ range (k + 1), ‖nonbacktrackingPow H j‖) :=
          (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            (l2_opNorm_mul _ _) ((l2_opNorm_mul _ _).trans (by gcongr)))) hE)
      _ ≤ ‖H‖ * a ^ (k + 2) + d * a ^ (k + 1) + 1 * d * a ^ (k + 1) :=
          add_le_add (add_le_add (by gcongr) (by gcongr)) (mul_le_mul_of_nonneg_left hsum
            (by linarith))
      _ ≤ a ^ (k + 3) := by
        -- `a ^ 2 ≥ ‖H‖ * a + 2 * d`, since `a = ‖H‖ + 2 * d + 2 ≥ 2`.
        have key : 0 ≤ (a * a - ‖H‖ * a - 2 * d) * a ^ (k + 1) :=
          mul_nonneg (by simp only [a]; nlinarith [norm_nonneg H]) hak
        have hpow : a ^ (k + 3) = a * (a * a ^ (k + 1)) := by ring
        have hpow' : a ^ (k + 2) = a * a ^ (k + 1) := by ring
        rw [hpow, hpow']
        nlinarith [key]

end Matrix
