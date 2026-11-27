/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Envelope

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Digamma and polygamma brackets from Stirling's series

This file specializes Alzer's complete monotonicity theorem on `(0, ∞)`
(`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Envelope.lean`) to orders `k = 1` and `k ≥ 2`,
establishing:

* the arbitrary-order and leading digamma brackets
  `log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)`;
* Alzer's polygamma brackets `S_k(2n; x) < (-1)^{k+1} ψ^{(k)}(x) < S_k(2n + 1; x)` for all
  `k ≥ 1`.

## Main declarations

* `TauCeti.deriv_realStirlingSeriesRemainder`: derivative of `realStirlingSeriesRemainder n` on
  `(0, ∞)`.
* `TauCeti.digamma_lt_log_sub_inv_two_mul`, `TauCeti.log_sub_inv_two_mul_sub_lt_digamma`,
  `TauCeti.digamma_lt_log_sub_inv_two_mul_sub_sum`,
  `TauCeti.log_sub_inv_two_mul_sub_sum_lt_digamma`: digamma brackets on `(0, ∞)`.
* `TauCeti.polygammaStirlingSum`,
  `TauCeti.iteratedDeriv_succ_realStirlingSeriesRemainder`,
  `TauCeti.polygammaStirlingSum_lt_neg_one_pow_mul_iteratedDeriv_digamma`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_digamma_lt_polygammaStirlingSum`: Alzer's polygamma
  brackets on `(0, ∞)`.

## References

* H. Alzer, *On some inequalities for the gamma and psi functions*, Math. Comp. 66 (1997),
  373–389, Theorem 9.
-/

public section

open Real Filter Set Topology
open scoped Nat

namespace TauCeti

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
    have h2j1 : (2 * (j : ℝ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : 2 * j ≠ 1))
    let c : ℝ := (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * (2 * j - 1 : ℝ))
    have hd := HasDerivAt.const_div_pow (hasDerivAt_id x) hx.ne' c (2 * j - 1)
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
    · simp only [stirlingTerm_def, c, id_eq, div_eq_mul_inv, mul_inv]; ring
    · have hpow : x ^ (2 * j - 1 + 1) = x ^ (2 * j) := by congr 1; omega
      rw [id_eq, hpow, Nat.cast_sub (by omega : 1 ≤ 2 * j)]
      push_cast
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
`∑_{i=1}^p B_{2i} ((2i + 1).ascFactorial (k - 1)) / x^{2i+k}`. -/
noncomputable def polygammaStirlingSum (k p : ℕ) (x : ℝ) : ℝ :=
  ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) +
    ∑ i ∈ Finset.Icc 1 p,
      (bernoulli (2 * i) : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) / x ^ (2 * i + k)

/-- Unfolding formula for `TauCeti.polygammaStirlingSum`. -/
theorem polygammaStirlingSum_def (k p : ℕ) (x : ℝ) :
    polygammaStirlingSum k p x =
      ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) +
        ∑ i ∈ Finset.Icc 1 p,
          (bernoulli (2 * i) : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) /
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
        (((2 * (p + 1) + 1).ascFactorial (k - 1) : ℕ) : ℝ) / x ^ (2 * (p + 1) + k) := by
  simp only [polygammaStirlingSum_def, Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]
  ring

private theorem iteratedDeriv_bernoulli_div_two_mul_pow {i k : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k)
    (x : ℝ) :
    iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k *
        ((bernoulli (2 * i) : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) /
          x ^ (2 * i + k)) := by
  have heq : (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) =
      fun t : ℝ ↦ ((bernoulli (2 * i) : ℝ) / (2 * i : ℝ)) / t ^ (2 * i) := by
    ext t; simp only [div_eq_mul_inv, mul_inv]; ring
  have hidx : 1 + (k - 1) = k := Nat.add_sub_cancel' hk
  have hasc : (((2 * i).ascFactorial k : ℕ) : ℝ) =
      (2 * (i : ℝ)) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) := by
    have h := Nat.ascFactorial_mul_ascFactorial (2 * i) 1 (k - 1)
    rw [hidx, Nat.ascFactorial_succ, Nat.ascFactorial_zero, add_zero, mul_one] at h
    exact_mod_cast h.symm
  rw [heq, TauCeti.iteratedDeriv_const_div_pow, hasc]
  have hi0 : (2 : ℝ) * i ≠ 0 := by positivity
  calc (-1 : ℝ) ^ k * (2 * (i : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ)) *
        ((bernoulli (2 * i) : ℝ) / (2 * (i : ℝ))) / x ^ (2 * i + k)
      = (-1 : ℝ) ^ k *
          (((2 * (i : ℝ)) * ((bernoulli (2 * i) : ℝ) / (2 * (i : ℝ)))) *
            (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ)) / x ^ (2 * i + k) := by ring
    _ = (-1 : ℝ) ^ k *
          ((bernoulli (2 * i) : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) /
            x ^ (2 * i + k)) := by
        rw [mul_div_cancel₀ _ hi0]; ring

private theorem iteratedDeriv_inv_two_mul (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ ↦ 1 / (2 * t)) x =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (2 * x ^ (k + 1))) := by
  have heq : (fun t : ℝ ↦ 1 / (2 * t)) = fun t : ℝ ↦ (2⁻¹ : ℝ) / t := by
    ext t; simp [div_eq_mul_inv, mul_comm]
  rw [heq, TauCeti.iteratedDeriv_const_div]
  simp only [div_eq_mul_inv, mul_inv]; ring

/-- Relation between `iteratedDeriv (k + 1) (realStirlingSeriesRemainder n)` and the `k`-th
polygamma function `iteratedDeriv k Real.digamma` on `(0, ∞)` for `k ≥ 1`. -/
theorem iteratedDeriv_succ_realStirlingSeriesRemainder (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv (k + 1) (realStirlingSeriesRemainder n) x =
      iteratedDeriv k Real.digamma x + (-1 : ℝ) ^ k * polygammaStirlingSum k (n - 1) x := by
  -- 1. Identify `deriv (realStirlingSeriesRemainder n)` on a neighborhood of `x`
  have hev : deriv (realStirlingSeriesRemainder n) =ᶠ[𝓝 x]
      fun t : ℝ ↦ (Real.digamma t - Real.log t + 1 / (2 * t)) +
        ∑ i ∈ Finset.Ico 1 n, (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact deriv_realStirlingSeriesRemainder n ht
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  -- 2. Smoothness side conditions for term-by-term `k`-th differentiation at `x > 0`
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
  -- 3. Differentiate term by term and match `polygammaStirlingSum k (n - 1) x`
  rw [iteratedDeriv_fun_add ((hcd_psi.sub hcd_log).add hcd_half) hcd_sum,
    iteratedDeriv_fun_add (hcd_psi.sub hcd_log) hcd_half,
    iteratedDeriv_fun_sub hcd_psi hcd_log,
    iteratedDeriv_fun_sum hcd_term,
    Real.iteratedDeriv_log hk x,
    iteratedDeriv_inv_two_mul k x]
  have hsum_eq :
      ∑ i ∈ Finset.Ico 1 n,
        iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k * ∑ i ∈ Finset.Icc 1 (n - 1),
        (bernoulli (2 * i) : ℝ) * (((2 * i + 1).ascFactorial (k - 1) : ℕ) : ℝ) /
          x ^ (2 * i + k) := by
    have hIco : Finset.Ico 1 n = Finset.Icc 1 (n - 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.mul_sum, hIco]
    exact Finset.sum_congr rfl fun i hi ↦
      iteratedDeriv_bernoulli_div_two_mul_pow (Finset.mem_Icc.mp hi).1 hk x
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
  rw [← mul_assoc, ← pow_add, Odd.neg_one_pow (n := k + 1 + k) ⟨k, by omega⟩] at h
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
  rw [← mul_assoc, ← pow_add, Odd.neg_one_pow (n := k + 1 + k) ⟨k, by omega⟩] at h
  linarith

end TauCeti
