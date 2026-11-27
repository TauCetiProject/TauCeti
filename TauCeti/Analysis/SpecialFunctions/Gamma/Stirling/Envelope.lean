/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series

import TauCeti.Analysis.SpecialFunctions.Integrals.Periodic.Bernoulli
import TauCeti.NumberTheory.Bernoulli.Values

/-!
# Alzer's complete monotonicity and enveloping bounds for Stirling's series

This file derives Alzer's complete monotonicity and enveloping theorems on `(0, ∞)` from the
periodic Bernoulli remainder representation in
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series`.

On the positive real axis `(0, ∞)`, the periodic Bernoulli factor
`(-1)^{n+1} (B_{2n} - B_{2n}({u}))` is nonnegative everywhere and strictly positive on `(0, 1)`.
Consequently every signed real Stirling remainder `(-1)^{n+1} r_n(x)` has strictly alternating
derivatives of all orders, establishing Alzer's complete monotonicity theorem: the functions
`F_m = r_{2m+1}` and `G_m = -r_{2m+2}` are strictly completely monotone on `(0, ∞)`. Specializing
to order `k = 0` yields the two-sided enveloping brackets for `log Γ(x)` and the strict enveloping
bound `|r_n(x)| < |T_n(x)|`.

Digamma and polygamma brackets are in
`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Polygamma.lean`, and Stieltjes' complex sector
bounds are in `TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Sector.lean`.

## Main declarations

* `TauCeti.signed_iteratedDeriv_realStirlingSeriesRemainder`: signed integral representation of
  `iteratedDeriv k (realStirlingSeriesRemainder n) x` on `(0, ∞)`.
* `TauCeti.neg_one_pow_mul_iteratedDeriv_signed_realStirlingSeriesRemainder_pos`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos`: strict sign
  alternation for all orders `k : ℕ`.
* `TauCeti.isCompletelyMonotoneOnIoi_realStirlingSeriesRemainder_odd`,
  `TauCeti.isCompletelyMonotoneOnIoi_neg_realStirlingSeriesRemainder_even`: Alzer's complete
  monotonicity of `F_m = r_{2m+1}` and `G_m = -r_{2m+2}` on `(0, ∞)`.
* `TauCeti.sum_stirlingTerm_lt_log_Gamma_sub`, `TauCeti.log_Gamma_sub_lt_sum_stirlingTerm`,
  `TauCeti.abs_realStirlingSeriesRemainder_lt_abs_stirlingTerm`,
  `TauCeti.neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos`,
  `TauCeti.neg_one_pow_succ_mul_stirlingTerm_pos`: enveloping inequalities and strict term signs
  on `(0, ∞)`.

## References

* H. Alzer, *On some inequalities for the gamma and psi functions*, Math. Comp. 66 (1997),
  373–389, Theorem 8.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4, eq. (8.4.06).
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped ContDiff Nat

namespace TauCeti

/-! ### Alzer's complete monotonicity and enveloping theorem on `(0, ∞)` -/

/-- Signed real integral representation for every iterated derivative of
`realStirlingSeriesRemainder n` on `(0, ∞)` for `n ≥ 1`. -/
theorem signed_iteratedDeriv_realStirlingSeriesRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingSeriesRemainder n) x =
      (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k) := by
  rw [iteratedDeriv_realStirlingSeriesRemainder hn k hx]
  have hint_mul :
      (-1 : ℝ) ^ (n + 1) *
        ∫ u in Ioi (0 : ℝ),
          ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) / (u + x) ^ (2 * n + k) =
      ∫ u in Ioi (0 : ℝ),
        (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + x) ^ (2 * n + k) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ by ring
  rw [← hint_mul]
  calc
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) *
        ((-1 : ℝ) ^ k * (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
          ∫ u in Ioi (0 : ℝ),
            ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
              (u + x) ^ (2 * n + k))
        = (-1 : ℝ) ^ k * (-1 : ℝ) ^ k *
            ((((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
              ((-1 : ℝ) ^ (n + 1) *
                ∫ u in Ioi (0 : ℝ),
                  ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
                    (u + x) ^ (2 * n + k))) := by ring
    _ = _ := by rw [← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-- For every `n ≥ 1`, `k : ℕ`, and `x > 0`, the signed real Stirling remainder
`t ↦ (-1)^{n+1} r_n(t)` has strictly alternating `k`-th derivative:
`0 < (-1)^k * ((-1)^{n+1} r_n)^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_signed_realStirlingSeriesRemainder_pos {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k *
      iteratedDeriv k (fun t ↦ (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n t) x := by
  rw [iteratedDeriv_const_mul_field ((-1 : ℝ) ^ (n + 1)) (realStirlingSeriesRemainder n),
    ← mul_assoc, signed_iteratedDeriv_realStirlingSeriesRemainder hn k hx]
  exact mul_pos (by positivity)
    (integral_signed_bernoulli_sub_div_pow_pos hn (by omega : 2 ≤ 2 * n + k) hx)

/-- **Alzer's theorem (odd remainders)**: for every `m, k : ℕ` and `x > 0`,
`0 < (-1)^k * r_{2m+1}^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos (m k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k * iteratedDeriv k (realStirlingSeriesRemainder (2 * m + 1)) x := by
  have h := neg_one_pow_mul_iteratedDeriv_signed_realStirlingSeriesRemainder_pos
    (n := 2 * m + 1) (by omega) k hx
  have hidx : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  have hpow : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
    rw [hidx, pow_mul, neg_one_sq, one_pow]
  simpa only [hpow, one_mul] using h

/-- **Alzer's theorem (negated even remainders)**: for every `m, k : ℕ` and `x > 0`,
`0 < (-1)^k * (-r_{2m+2})^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos (m k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k * iteratedDeriv k (fun t ↦ -realStirlingSeriesRemainder (2 * m + 2) t) x := by
  have h := neg_one_pow_mul_iteratedDeriv_signed_realStirlingSeriesRemainder_pos
    (n := 2 * m + 2) (by omega) k hx
  have hpow : (-1 : ℝ) ^ (2 * m + 2 + 1) = -1 := Odd.neg_one_pow ⟨m + 1, by omega⟩
  simpa only [hpow, neg_one_mul] using h

/-- For every `m : ℕ`, the odd-order real Stirling remainder
`F_m = realStirlingSeriesRemainder (2m + 1)` is completely monotone on `(0, ∞)`
(Alzer 1997, Theorem 8). -/
theorem isCompletelyMonotoneOnIoi_realStirlingSeriesRemainder_odd (m : ℕ) :
    IsCompletelyMonotoneOnIoi (realStirlingSeriesRemainder (2 * m + 1)) :=
  ⟨contDiffOn_realStirlingSeriesRemainder (2 * m + 1),
    fun k _ hx ↦ (neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos m k hx).le⟩

/-- For every `m : ℕ`, the negated even-order real Stirling remainder
`G_m = -realStirlingSeriesRemainder (2m + 2)` is completely monotone on `(0, ∞)`
(Alzer 1997, Theorem 8). -/
theorem isCompletelyMonotoneOnIoi_neg_realStirlingSeriesRemainder_even (m : ℕ) :
    IsCompletelyMonotoneOnIoi (fun t ↦ -realStirlingSeriesRemainder (2 * m + 2) t) :=
  ⟨(contDiffOn_realStirlingSeriesRemainder (2 * m + 2)).neg,
    fun k _ hx ↦ (neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos m k hx).le⟩

/-- For `n ≥ 1` and `x > 0`, `realStirlingSeriesRemainder n x` has strict sign `(-1)^{n+1}`. -/
theorem neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n x := by
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
    neg_one_pow_mul_iteratedDeriv_signed_realStirlingSeriesRemainder_pos hn 0 hx

/-- For `n ≥ 1` and `x > 0`, `stirlingTerm n x` has strict sign `(-1)^{n+1}`:
`0 < (-1)^(n+1) * stirlingTerm n x`. -/
theorem neg_one_pow_succ_mul_stirlingTerm_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := by
  have hden : 0 < (2 * (n : ℝ)) * (2 * (n : ℝ) - 1) * x ^ (2 * n - 1) := by
    have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < 2 * n))
    positivity
  have hB : 0 < (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by
    exact_mod_cast neg_one_pow_mul_bernoulli_two_mul_pos (by omega : n ≠ 0)
  rw [stirlingTerm_def, mul_div_assoc']
  exact div_pos hB hden

/-- Even-length partial sums of Stirling's series strictly underestimate `log Γ(x)` minus the
leading Stirling terms for every `m : ℕ` and `x > 0`. -/
theorem sum_stirlingTerm_lt_log_Gamma_sub (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Finset.Icc 1 (2 * m), stirlingTerm i x <
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos m 0 hx
  simp only [pow_zero, one_mul, iteratedDeriv_zero, realStirlingSeriesRemainder_def,
    Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Odd-length partial sums of Stirling's series strictly overestimate `log Γ(x)` minus the
leading Stirling terms for every `m : ℕ` and `x > 0`. -/
theorem log_Gamma_sub_lt_sum_stirlingTerm (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) <
      ∑ i ∈ Finset.Icc 1 (2 * m + 1), stirlingTerm i x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos m 0 hx
  have hidx : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  simp only [pow_zero, one_mul, iteratedDeriv_zero, realStirlingSeriesRemainder_def, hidx,
    Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Enveloping bound on `(0, ∞)`: for every `n ≥ 1` and `x > 0`, the Stirling remainder is strictly
smaller in absolute value than the first omitted term: `|r_n(x)| < |T_n(x)|`. -/
theorem abs_realStirlingSeriesRemainder_lt_abs_stirlingTerm {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : 0 < x) :
    |realStirlingSeriesRemainder n x| < |stirlingTerm n x| := by
  have h1 := neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos hn hx
  have h2 := neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos (n := n + 1) (by omega) hx
  rw [realStirlingSeriesRemainder_succ, pow_succ] at h2
  have hlt : (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n x <
      (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := by linarith
  have habs_r : |realStirlingSeriesRemainder n x| =
      (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n x := by
    simpa [abs_mul] using abs_of_pos h1
  have habs_T : |stirlingTerm n x| = (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := by
    simpa [abs_mul] using abs_of_pos (neg_one_pow_succ_mul_stirlingTerm_pos hn hx)
  rwa [habs_r, habs_T]

end TauCeti
