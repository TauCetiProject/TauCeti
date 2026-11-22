/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series

import TauCeti.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicBernoulli
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.NumberTheory.ZetaValues

/-!
# Alzer's complete monotonicity, polygamma brackets, and Stieltjes' sector bound

This file derives the real-axis enveloping properties of Stirling's series and Stieltjes' sharp
slit-plane sector bound from the periodic Bernoulli remainder representation in
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series`.

On the positive real axis `(0, ∞)`, the periodic Bernoulli factor
`(-1)^{n+1} (B_{2n} - B_{2n}({u}))` is nonnegative everywhere and strictly positive on `(0, 1)`.
Consequently every signed real Stirling remainder `(-1)^{n+1} r_n(x)` has strictly alternating
derivatives of all orders, establishing Alzer's complete monotonicity theorem: the functions
`F_m = r_{2m+1}` and `G_m = -r_{2m+2}` are strictly completely monotone on `(0, ∞)`. Specializing
to orders `k = 0`, `k = 1`, and `k ≥ 2` yields:

* the two-sided enveloping brackets for `log Γ(x)` and the strict bound `|r_n(x)| < |T_n(x)|`;
* the arbitrary-order and leading digamma brackets
  `log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)`;
* Alzer's polygamma brackets `S_k(2n; x) < (-1)^{k+1} ψ^{(k)}(x) < S_k(2n + 1; x)` for all `k ≥ 1`.

Combining the constant-sign remainder integral with the half-angle inequality
`cos (arg z / 2) * (‖z‖ + u) ≤ ‖u + z‖` compares the slit-plane remainder directly to its real-axis
value at `‖z‖`, giving Stieltjes' sharp sector bound
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2 * n)`, its `n = 1` specialization in Ramaré's sector
form `‖r₁(z)‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`, the sharp `1 / 12` derivative bounds for
`r₁^{(k)}(z)` on the slit plane and on closed sectors, and the resulting `1 / 12` sector bound for
`log ‖Γ s‖`.

## Main declarations

* `TauCeti.isCompletelyMonotoneOnIoi_realStirlingSeriesRemainder_odd`,
  `TauCeti.isCompletelyMonotoneOnIoi_neg_realStirlingSeriesRemainder_even`: Alzer's complete
  monotonicity of `F_m = r_{2m+1}` and `G_m = -r_{2m+2}` on `(0, ∞)`.
* `TauCeti.sum_stirlingTerm_lt_log_Gamma_sub`, `TauCeti.log_Gamma_sub_lt_sum_stirlingTerm`,
  `TauCeti.stirling_lt_log_Gamma`, `TauCeti.abs_realStirlingSeriesRemainder_lt_abs_stirlingTerm`,
  `TauCeti.neg_one_pow_succ_mul_stirlingTerm_pos`: enveloping inequalities and strict term signs
  on `(0, ∞)`.
* `TauCeti.digamma_lt_log_sub_inv_two_mul`, `TauCeti.log_sub_inv_two_mul_sub_lt_digamma`,
  `TauCeti.digamma_lt_log_sub_inv_two_mul_sub_sum`,
  `TauCeti.log_sub_inv_two_mul_sub_sum_lt_digamma`: digamma brackets on `(0, ∞)`.
* `TauCeti.polygammaStirlingSum`,
  `TauCeti.polygammaStirlingSum_lt_neg_one_pow_mul_iteratedDeriv_digamma`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_digamma_lt_polygammaStirlingSum`: Alzer's polygamma
  brackets on `(0, ∞)`.
* `TauCeti.norm_stirlingSeriesRemainder_lt`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_lt`,
  `TauCeti.norm_stirlingSeriesRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_stirlingRemainder_lt_of_abs_arg_le`,
  `TauCeti.abs_log_norm_Gamma_sub_stirling_lt`: Stieltjes' sharp slit-plane and closed-sector
  bounds and the `1 / 12` bound for `log ‖Γ s‖`.

## References

* H. Alzer, *On some inequalities for the gamma and psi functions*, Math. Comp. 66 (1997),
  373–389, Theorems 8 and 9.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4, eq. (8.4.06).
* O. Ramaré, *Excursions in Multiplicative Number Theory*, §20.2.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped ContDiff Nat

namespace TauCeti

private theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← mul_pow]
  norm_num

private theorem neg_one_pow_succ_mul_self (k : ℕ) : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
  rw [pow_succ, mul_right_comm, ← mul_pow]
  norm_num

/-! ### Alzer's complete monotonicity and enveloping theorem on `(0, ∞)` -/

private theorem integrableOn_signed_bernoulli_sub_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k) (Ioi 0) := by
  have h := (Complex.reCLM.integrable_comp
    (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n hk
      (Complex.ofReal_mem_slitPlane.mpr hx))).const_mul ((-1 : ℝ) ^ (n + 1))
  refine h.congr (Eventually.of_forall fun u ↦ ?_)
  have heq : (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
      ((u : ℂ) + (x : ℂ)) ^ k =
      ((((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k : ℝ) : ℂ) := by push_cast; rfl
  simp only [Complex.reCLM_apply, heq, Complex.ofReal_re]
  ring

private theorem signed_iteratedDeriv_realStirlingSeriesRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
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
  linear_combination ((((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) * (-1 : ℝ) ^ (n + 1) *
    ∫ u in Ioi (0 : ℝ), ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
      (u + x) ^ (2 * n + k)) * (neg_one_pow_mul_self k)

private theorem integral_signed_bernoulli_sub_div_pow_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    0 < ∫ u in Ioi (0 : ℝ),
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k := by
  let f : ℝ → ℝ := fun u ↦
    (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
      (u + x) ^ k
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := mem_Ioi.mp hu
    exact div_nonneg (neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u)
      (by positivity)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn
    (integrableOn_signed_bernoulli_sub_div_pow_Ioi n hk hx)]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support f ∩ Ioi (0 : ℝ) := fun u hu ↦ by
    have hnum : 0 < (-1 : ℝ) ^ (n + 1) *
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
      rw [Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩]
      exact neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos (by omega : n ≠ 0) hu
    have hu0 : 0 < u := hu.1
    exact ⟨(div_pos hnum (by positivity)).ne', hu.1⟩
  exact lt_of_lt_of_le (by rw [Real.volume_Ioo]; norm_num) (measure_mono hsub)

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
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
    positivity
  have hB : 0 < (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by
    exact_mod_cast neg_one_pow_succ_mul_bernoulli_even_pos (by omega : n ≠ 0)
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

/-- Leading Stirling lower bound on the positive real axis: for all `x > 0`,
`(x - 1/2) log x - x + log (2π) / 2 < log (Γ x)`. -/
theorem stirling_lt_log_Gamma {x : ℝ} (hx : 0 < x) :
    (x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2 < Real.log (Real.Gamma x) := by
  have h := sum_stirlingTerm_lt_log_Gamma_sub 0 hx
  simp only [Nat.mul_zero, Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty] at h
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

/-! ### Digamma brackets on `(0, ∞)` -/

/-- First derivative of `realStirlingSeriesRemainder n` on `(0, ∞)`:
`r_n'(x) = ψ(x) - log x + 1 / (2x) + ∑_{j=1}^{n-1} B_{2j} / (2j x^{2j})`. -/
theorem deriv_realStirlingSeriesRemainder (n : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv (realStirlingSeriesRemainder n) x =
      Real.digamma x - Real.log x + 1 / (2 * x) +
        ∑ j ∈ Finset.Ico 1 n, (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) := by
  have hlogG : HasDerivAt (fun t ↦ Real.log (Real.Gamma t)) (Real.digamma x) x :=
    Real.hasDerivAt_log_Gamma fun m ↦ by linarith
  have hmain : HasDerivAt
      (fun t ↦ (t - 1 / 2) * Real.log t - t + Real.log (2 * π) / 2)
      (Real.log x - 1 / (2 * x)) x := by
    refine (((((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).mul (Real.hasDerivAt_log hx.ne')).sub
      (hasDerivAt_id x)).add_const (Real.log (2 * π) / 2)).congr_deriv ?_
    simp only [id_eq]; field_simp; ring
  have hterm : ∀ j ∈ Finset.Ico 1 n,
      HasDerivAt (fun t : ℝ ↦ stirlingTerm j t)
        (-((bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)))) x := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have h2j1 : (2 * (j : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    let c : ℝ := (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * (2 * j - 1 : ℝ))
    have hd := HasDerivAt.const_div_pow (hasDerivAt_id x) hx.ne' c (2 * j - 1)
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
    · simp only [stirlingTerm_def, c, id_eq, div_eq_mul_inv, mul_inv]; ring
    · have hpow : x ^ (2 * j - 1 + 1) = x ^ (2 * j) := by congr 1; omega
      have hc : ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; push_cast; rfl
      rw [id_eq, hpow, hc]
      dsimp only [c]
      field_simp
  have htot : HasDerivAt (realStirlingSeriesRemainder n) _ x :=
    ((hlogG.sub hmain).sub (HasDerivAt.fun_sum hterm)).congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ by simp only [realStirlingSeriesRemainder_def, Pi.sub_apply])
  rw [htot.deriv, Finset.sum_neg_distrib]; ring

/-- Arbitrary-order upper digamma bracket on `(0, ∞)`: for every `m : ℕ` and `x > 0`,
`ψ(x) < log x - 1 / (2x) - ∑_{j=1}^{2m} B_{2j} / (2j x^{2j})`. -/
theorem digamma_lt_log_sub_inv_two_mul_sub_sum (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.digamma x <
      Real.log x - 1 / (2 * x) -
        ∑ j ∈ Finset.Icc 1 (2 * m), (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos m 1 hx
  rw [pow_one, iteratedDeriv_one, deriv_realStirlingSeriesRemainder (2 * m + 1) hx,
    Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Arbitrary-order lower digamma bracket on `(0, ∞)`: for every `m : ℕ` and `x > 0`,
`log x - 1 / (2x) - ∑_{j=1}^{2m+1} B_{2j} / (2j x^{2j}) < ψ(x)`. -/
theorem log_sub_inv_two_mul_sub_sum_lt_digamma (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) -
        ∑ j ∈ Finset.Icc 1 (2 * m + 1), (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) <
      Real.digamma x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos m 1 hx
  have hidx : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [pow_one, iteratedDeriv_one, deriv.fun_neg, deriv_realStirlingSeriesRemainder (2 * m + 2) hx,
    hidx, Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Leading upper digamma bound on `(0, ∞)`: `ψ(x) < log x - 1 / (2x)`. -/
theorem digamma_lt_log_sub_inv_two_mul {x : ℝ} (hx : 0 < x) :
    Real.digamma x < Real.log x - 1 / (2 * x) := by
  have h := digamma_lt_log_sub_inv_two_mul_sub_sum 0 hx
  simp only [Nat.mul_zero, Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty, sub_zero] at h
  exact h

/-- Leading lower digamma bound on `(0, ∞)`: `log x - 1 / (2x) - 1 / (12x²) < ψ(x)`. -/
theorem log_sub_inv_two_mul_sub_lt_digamma {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) < Real.digamma x := by
  have h := log_sub_inv_two_mul_sub_sum_lt_digamma 0 hx
  simp only [Nat.mul_zero, zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.mul_one,
    bernoulli_two, Rat.cast_inv, Rat.cast_ofNat, Nat.cast_one] at h
  have hdiv : (6 : ℝ)⁻¹ / (2 * 1 * x ^ 2) = 1 / (12 * x ^ 2) := by ring
  linarith

/-! ### Alzer's polygamma brackets on `(0, ∞)` -/

/-- The order-`p` Stirling partial sum for the `k`-th polygamma function `(-1)^{k+1} ψ^{(k)}(x)`:
`S_k(p; x) = (k - 1)! / x^k + k! / (2 x^{k+1}) +`
`∑_{i=1}^p B_{2i} (∏_{j=1}^{k-1} (2i + j)) / x^{2i+k}`. -/
noncomputable def polygammaStirlingSum (k p : ℕ) (x : ℝ) : ℝ :=
  ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) +
    ∑ i ∈ Finset.Icc 1 p,
      (bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) / x ^ (2 * i + k)

/-- Unfolding formula for `TauCeti.polygammaStirlingSum`. -/
theorem polygammaStirlingSum_def (k p : ℕ) (x : ℝ) :
    polygammaStirlingSum k p x =
      ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) +
        ∑ i ∈ Finset.Icc 1 p,
          (bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) /
            x ^ (2 * i + k) :=
  (rfl)

/-- At `p = 0`, `polygammaStirlingSum k 0 x` reduces to the two leading terms. -/
@[simp]
theorem polygammaStirlingSum_zero (k : ℕ) (x : ℝ) :
    polygammaStirlingSum k 0 x = ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) := by
  simp [polygammaStirlingSum_def]

/-- Recurrence adding the `(p + 1)`-th Bernoulli term to `polygammaStirlingSum k p x`. -/
theorem polygammaStirlingSum_succ (k p : ℕ) (x : ℝ) :
    polygammaStirlingSum k (p + 1) x = polygammaStirlingSum k p x +
      (bernoulli (2 * (p + 1)) : ℝ) *
        (∏ j ∈ Finset.Ico 1 k, ((2 * (p + 1) + j : ℕ) : ℝ)) / x ^ (2 * (p + 1) + k) := by
  simp only [polygammaStirlingSum_def, Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]
  ring

private theorem iteratedDeriv_bernoulli_div_two_mul_pow {i k : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k *
        ((bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) /
          x ^ (2 * i + k)) := by
  have heq : (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) =
      fun t : ℝ ↦ ((bernoulli (2 * i) : ℝ) / (2 * i : ℝ)) / t ^ (2 * i) := by
    ext t; simp only [div_eq_mul_inv, mul_inv]; ring
  rw [heq, TauCeti.iteratedDeriv_const_div_pow]
  have hsplit : Finset.range k = insert 0 (Finset.Ico 1 k) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hsplit, Finset.prod_insert (by simp)]
  simp only [add_zero, Nat.cast_mul, Nat.cast_ofNat]
  have : (2 : ℝ) * i ≠ 0 := by positivity
  field_simp

/-- Relation between `iteratedDeriv (k + 1) (realStirlingSeriesRemainder n)` and the `k`-th
polygamma function `iteratedDeriv k Real.digamma` on `(0, ∞)` for `k ≥ 1`. -/
theorem iteratedDeriv_succ_realStirlingSeriesRemainder (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv (k + 1) (realStirlingSeriesRemainder n) x =
      iteratedDeriv k Real.digamma x + (-1 : ℝ) ^ k * polygammaStirlingSum k (n - 1) x := by
  have hev : deriv (realStirlingSeriesRemainder n) =ᶠ[𝓝 x]
      fun t : ℝ ↦ (Real.digamma t - Real.log t + 1 / (2 * t)) +
        ∑ i ∈ Finset.Ico 1 n, (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact deriv_realStirlingSeriesRemainder n ht
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have hcd_psi : ContDiffAt ℝ k Real.digamma x :=
    (contDiffOn_digamma_Ioi.contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  have hcd_log : ContDiffAt ℝ k Real.log x :=
    (contDiffAt_id.log hx.ne').of_le (by exact_mod_cast le_top)
  have hcd_half : ContDiffAt ℝ k (fun t : ℝ ↦ 1 / (2 * t)) x :=
    contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) (by positivity)
  have hcd_term : ∀ i ∈ Finset.Ico 1 n,
      ContDiffAt ℝ k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact contDiffAt_const.div (contDiffAt_const.mul (contDiffAt_id.pow (2 * i)))
      (mul_ne_zero (by positivity) (pow_ne_zero _ hx.ne'))
  have hcd_sum : ContDiffAt ℝ k
      (fun t : ℝ ↦ ∑ i ∈ Finset.Ico 1 n, (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i)))
      x :=
    ContDiffAt.sum hcd_term
  have hhalf : iteratedDeriv k (fun t : ℝ ↦ 1 / (2 * t)) x =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (2 * x ^ (k + 1))) := by
    have heq : (fun t : ℝ ↦ 1 / (2 * t)) = fun t : ℝ ↦ (2⁻¹ : ℝ) / t := by
      ext t; simp [div_eq_mul_inv, mul_comm]
    rw [heq, TauCeti.iteratedDeriv_const_div]
    simp only [div_eq_mul_inv, mul_inv]; ring
  rw [iteratedDeriv_fun_add ((hcd_psi.sub hcd_log).add hcd_half) hcd_sum,
    iteratedDeriv_fun_add (hcd_psi.sub hcd_log) hcd_half,
    iteratedDeriv_fun_sub hcd_psi hcd_log,
    iteratedDeriv_fun_sum hcd_term,
    Real.iteratedDeriv_log hk x,
    hhalf]
  have hsum_eq :
      ∑ i ∈ Finset.Ico 1 n,
        iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k * ∑ i ∈ Finset.Icc 1 (n - 1),
        (bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) /
          x ^ (2 * i + k) := by
    have hIco : Finset.Ico 1 n = Finset.Icc 1 (n - 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.mul_sum, hIco]
    exact Finset.sum_congr rfl fun i hi ↦
      iteratedDeriv_bernoulli_div_two_mul_pow (Finset.mem_Icc.mp hi).1 hk hx
  rw [hsum_eq, polygammaStirlingSum_def]
  have hsign : -((-1 : ℝ) ^ (k - 1)) = (-1 : ℝ) ^ k := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk_eq, pow_succ]
    ring
  linear_combination (((k - 1)! : ℝ) / x ^ k) * hsign

/-- **Alzer's lower polygamma bracket** (Alzer 1997, Theorem 9): for every `k ≥ 1`, `n : ℕ`, and
`x > 0`, `S_k(2n; x) < (-1)^{k+1} ψ^{(k)}(x)`. -/
theorem polygammaStirlingSum_lt_neg_one_pow_mul_iteratedDeriv_digamma {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    polygammaStirlingSum k (2 * n) x < (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos n (k + 1) hx
  rw [iteratedDeriv_succ_realStirlingSeriesRemainder (2 * n + 1) hk hx] at h
  simp only [Nat.add_sub_cancel, mul_add] at h
  rw [← mul_assoc, neg_one_pow_succ_mul_self k] at h
  linarith

/-- **Alzer's upper polygamma bracket** (Alzer 1997, Theorem 9): for every `k ≥ 1`, `n : ℕ`, and
`x > 0`, `(-1)^{k+1} ψ^{(k)}(x) < S_k(2n + 1; x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_digamma_lt_polygammaStirlingSum {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x < polygammaStirlingSum k (2 * n + 1) x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos n (k + 1) hx
  have hidx : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  rw [iteratedDeriv_fun_neg, iteratedDeriv_succ_realStirlingSeriesRemainder (2 * n + 2) hk hx] at h
  simp only [hidx, mul_neg, mul_add] at h
  rw [← mul_assoc, neg_one_pow_succ_mul_self k] at h
  linarith

/-! ### Stieltjes' sharp sector bound on the slit plane -/

/-- Comparison of the slit-plane derivative `‖r_n^{(k)}(z)‖` to its positive real-axis value at
`‖z‖`: for `n ≥ 1`, `k : ℕ`, and `z ∈ slitPlane`,
`‖r_n^{(k)}(z)‖ ≤ ((-1)^k (-1)^{n+1} r_n^{(k)}(‖z‖)) / cos (arg z / 2) ^ (2n + k)`. -/
theorem norm_iteratedDeriv_stirlingSeriesRemainder_le_real {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k (stirlingSeriesRemainder n) z‖ ≤
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingSeriesRemainder n) ‖z‖) /
        Real.cos (z.arg / 2) ^ (2 * n + k) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  rw [iteratedDeriv_stirlingSeriesRemainder hn k hz,
    signed_iteratedDeriv_realStirlingSeriesRemainder hn k hz_pos,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_eq_mul_inv, mul_comm _ (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n (by omega : 2 ≤ 2 * n + k) hz).norm
    ((integrableOn_signed_bernoulli_sub_div_pow_Ioi n
      (by omega : 2 ≤ 2 * n + k) hz_pos).const_mul _)
    measurableSet_Ioi fun u hu ↦ ?_)
  have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
  have hnn := neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u
  have habs : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| =
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
    simpa [abs_mul] using abs_of_nonneg hnn
  have hsec : Real.cos (z.arg / 2) * (u + ‖z‖) ≤ ‖(u : ℂ) + z‖ := by
    simpa [add_comm] using Complex.cos_half_arg_mul_norm_add_le_norm_add_ofReal z u
  have hpow : Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k) ≤
      ‖(u : ℂ) + z‖ ^ (2 * n + k) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsec (2 * n + k)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, habs]
  calc (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        ‖(u : ℂ) + z‖ ^ (2 * n + k)
      ≤ (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k)) :=
        div_le_div_of_nonneg_left hnn (by positivity) hpow
    _ = (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
          ((-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + ‖z‖) ^ (2 * n + k)) := by
        simp only [div_eq_mul_inv, mul_inv]; ring

/-- **Stieltjes' sharp sector bound** on the slit plane: for every `n ≥ 1` and `z ∈ slitPlane`,
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2n)`. -/
theorem norm_stirlingSeriesRemainder_lt {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingSeriesRemainder n z‖ < ‖stirlingTerm n z‖ / Real.cos (z.arg / 2) ^ (2 * n) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  have hle := norm_iteratedDeriv_stirlingSeriesRemainder_le_real hn 0 hz
  simp only [iteratedDeriv_zero, pow_zero, one_mul, add_zero] at hle
  have habs_r : (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n ‖z‖ =
      |realStirlingSeriesRemainder n ‖z‖| := by
    simpa [abs_mul] using
      (abs_of_pos (neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos hn hz_pos)).symm
  rw [habs_r] at hle
  have hlt := abs_realStirlingSeriesRemainder_lt_abs_stirlingTerm hn hz_pos
  rw [← norm_stirlingTerm_eq_abs_norm n z] at hlt
  exact lt_of_le_of_lt hle (div_lt_div_of_pos_right hlt (pow_pos hcos_pos _))

/-- Sharp `1 / 12` half-angle bound for all derivatives of `TauCeti.stirlingRemainder` on the
slit plane: for every `k : ℕ` and `z ∈ slitPlane`,
`‖iteratedDeriv k stirlingRemainder z‖ < k! / (12 * cos (arg z / 2) ^ (k + 2) * ‖z‖ ^ (k + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_lt (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k stirlingRemainder z‖ <
      (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  have hle := norm_iteratedDeriv_stirlingSeriesRemainder_le_real le_rfl k hz
  have hpow : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
  have hidx : 2 * 1 + k = k + 2 := by omega
  rw [hpow, mul_one, hidx] at hle
  have hfun : stirlingSeriesRemainder 1 = stirlingRemainder :=
    funext stirlingSeriesRemainder_one_eq_stirlingRemainder
  rw [hfun] at hle
  -- Since `G₀ = -r₂` is strictly completely monotone,
  -- `(-1)^k r₁^{(k)}(‖z‖) < (-1)^k T₁^{(k)}(‖z‖)`.
  have hG := neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos 0 k hz_pos
  have heq_r2 : (fun t : ℝ ↦ -realStirlingSeriesRemainder 2 t) =
      fun t : ℝ ↦ (12⁻¹ : ℝ) / t - realStirlingSeriesRemainder 1 t := by
    ext t; rw [realStirlingSeriesRemainder_succ, stirlingTerm_one]
    simp only [div_eq_mul_inv, mul_inv]; ring
  simp only [Nat.mul_zero, zero_add] at hG
  have hT1_cd : ContDiffAt ℝ k (fun t : ℝ ↦ (12⁻¹ : ℝ) / t) ‖z‖ :=
    contDiffAt_const.div contDiffAt_id hz_pos.ne'
  rw [heq_r2, iteratedDeriv_fun_sub hT1_cd
    (((contDiffOn_realStirlingSeriesRemainder 1).contDiffAt (isOpen_Ioi.mem_nhds hz_pos)).of_le
      (by exact_mod_cast le_top))] at hG
  have hT1_deriv : iteratedDeriv k (fun t : ℝ ↦ (12⁻¹ : ℝ) / t) ‖z‖ =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) := by
    rw [TauCeti.iteratedDeriv_const_div]
    simp only [div_eq_mul_inv, mul_inv]; ring
  rw [hT1_deriv, mul_sub, ← mul_assoc, neg_one_pow_mul_self k, one_mul] at hG
  calc ‖iteratedDeriv k stirlingRemainder z‖
      ≤ ((-1 : ℝ) ^ k * iteratedDeriv k (realStirlingSeriesRemainder 1) ‖z‖) /
          Real.cos (z.arg / 2) ^ (k + 2) := hle
    _ < ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) / Real.cos (z.arg / 2) ^ (k + 2) :=
        div_lt_div_of_pos_right (by linarith) (pow_pos hcos_pos _)
    _ = (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
        simp only [div_eq_mul_inv, mul_inv]; ring

/-- Uniform sector form of Stieltjes' bound: for `0 < δ`, `|arg z| ≤ π - δ`, `z ≠ 0`, and
`n ≥ 1`, `‖r_n(z)‖ < ‖T_n(z)‖ / sin (δ / 2) ^ (2n)`. -/
theorem norm_stirlingSeriesRemainder_lt_of_abs_arg_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingSeriesRemainder n z‖ < ‖stirlingTerm n z‖ / Real.sin (δ / 2) ^ (2 * n) := by
  have hslit : z ∈ slitPlane := Complex.mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_le : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) :=
    Complex.sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz
  exact lt_of_lt_of_le (norm_stirlingSeriesRemainder_lt hn hslit)
    (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hsin_pos _)
      (pow_le_pow_left₀ hsin_pos.le hsin_le _))

/-- Sharp `1 / 12` closed-sector bound for all derivatives of `TauCeti.stirlingRemainder`:
for `0 < δ`, nonzero `z` with `|arg z| ≤ π - δ`, and every `k : ℕ`,
`‖iteratedDeriv k stirlingRemainder z‖ < k! / (12 * sin (δ / 2) ^ (k + 2) * ‖z‖ ^ (k + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le (k : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖iteratedDeriv k stirlingRemainder z‖ <
      (k ! : ℝ) / (12 * Real.sin (δ / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
  have hslit : z ∈ slitPlane := Complex.mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_le : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) :=
    Complex.sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz
  have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  exact lt_of_lt_of_le (norm_iteratedDeriv_stirlingRemainder_lt k hslit) (by gcongr)

/-- Ramaré's sector form of Stieltjes' `n = 1` bound for `TauCeti.stirlingRemainder`:
for `0 < δ`, `|arg z| ≤ π - δ`, and `z ≠ 0`,
`‖stirlingRemainder z‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_lt_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ < 1 / (12 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using
    norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le 0 hδ hz hz0

/-- Sharp `1 / 12` closed-sector Stirling bound for `log ‖Γ s‖`: for `0 < δ` and nonzero `s`
with `|arg s| ≤ π - δ`,
`|log ‖Γ s‖ - ((re s - 1/2) log ‖s‖ - im s · arg s - re s + log (2π) / 2)| <
1 / (12 * sin (δ / 2) ^ 2 * ‖s‖)`. -/
theorem abs_log_norm_Gamma_sub_stirling_lt {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    |Real.log ‖Complex.Gamma s‖ - ((s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re +
      Real.log (2 * π) / 2)| < 1 / (12 * Real.sin (δ / 2) ^ 2 * ‖s‖) := by
  rw [← stirlingRemainder_re (Complex.mem_slitPlane_of_abs_arg_le hδ hs hs0)]
  exact (abs_re_le_norm _).trans_lt (norm_stirlingRemainder_lt_of_abs_arg_le hδ hs hs0)

end TauCeti
