/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.RingTheory.Binomial

/-!
# Convergence of multichoose power series and the binomial error

This file determines the exact unconditional summability domain of the power series with
generalized multichoose coefficients and positive real parameter.  The result applies to both real
and complex arguments.  These results supply the analytic criterion used to determine the exact
integrability domain of the negative-binomial probability-generating function.

It also bounds the error `(1 + t) ^ a - ∑_{k<K} (a choose k) t ^ k` of the real binomial series
after `K` terms by `C |t| ^ K` on every compact interval inside `(-1, ∞)`, for every real
exponent `a`. Its derivative is `a` times the error for the exponent `a - 1` with one term fewer,
so the bound follows from the mean value theorem by induction on `K`.

## Main declarations

* `TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one` — the multichoose binomial
  series on the open unit interval.
* `TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one` — the complex-valued
  multichoose binomial series on the open unit disk.
* `TauCeti.summable_multichoose_mul_geometric_iff_norm_lt_one` — exact summability of
  `∑ n, multichoose r n * q ^ n` for `0 < r`.
* `TauCeti.binomialError` — the error `(1 + t) ^ a - ∑_{k<K} (a choose k) t ^ k` of the
  binomial series after `K` terms; `TauCeti.binomialError_def` unfolds it and
  `TauCeti.binomialError_succ_zero` records that it vanishes at `0` once a term is subtracted.
* `TauCeti.hasDerivAt_binomialError` — the derivative of the error after `K + 1` terms is `a`
  times the error for the exponent `a - 1` after `K` terms.
* `TauCeti.exists_abs_binomialError_le` — the error after `K` terms is `O(|t| ^ K)` on every
  interval `[l, u]` with `-1 < l`.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

/-- The generalized multichoose power series sums to `(1 - x)⁻ʳ` when `|x| < 1`. -/
theorem hasSum_multichoose_mul_geometric_of_abs_lt_one {r x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.multichoose r n * x ^ n) (1 / (1 - x) ^ r) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one,
      Real.norm_eq_abs]
  simpa [Ring.multichoose_eq, mul_comm] using
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum_sub hmem

/-- The generalized multichoose power series sums to `(1 - z)⁻ʳ` throughout the complex open
unit disk. -/
theorem hasSum_multichoose_mul_geometric_complex_of_norm_lt_one {r z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.multichoose r n * z ^ n) (1 / (1 - z) ^ r) := by
  have hmem : z ∈ Metric.eball (0 : ℂ) 1 := by
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [Ring.multichoose_eq, mul_comm] using
    (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero r).hasSum_sub hmem

/-- For positive real `r`, the generalized multichoose power series is unconditionally summable
at a real or complex argument `q` exactly when `q` lies in the open unit ball. -/
@[simp]
theorem summable_multichoose_mul_geometric_iff_norm_lt_one
    {𝕂 : Type*} [RCLike 𝕂] {r : ℝ} {q : 𝕂} (hr : 0 < r) :
    Summable (fun n : ℕ => ((Ring.multichoose r n : ℝ) : 𝕂) * q ^ n) ↔ ‖q‖ < 1 := by
  have hcoeff_pos (n : ℕ) : 0 < Ring.multichoose r n := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    exact pos_of_mul_pos_right (h ▸ ascPochhammer_pos n r hr) (by positivity)
  -- At the boundary point `1` the coefficients themselves are not summable: their sum would
  -- bound `(1 - x)⁻ʳ` on `[0, 1)`, which tends to infinity as `x → 1⁻`.
  have hnot : ¬ Summable (fun n : ℕ => Ring.multichoose r n) := by
    intro hs
    have hsub : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
      simpa using (continuous_sub_left (1 : ℝ)).continuousWithinAt.tendsto_nhdsWithin
        (s := Iio 1) (t := Ioi 0) (x := 1) fun x hx => sub_pos.2 hx
    have htop : Tendsto (fun x : ℝ => 1 / (1 - x) ^ r) (𝓝[<] 1) atTop := by
      refine ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 hr)).comp hsub).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [Real.rpow_neg (sub_nonneg.2 (le_of_lt hx))]
    obtain ⟨x, hlt, hx⟩ := ((htop.eventually_gt_atTop (∑' n, Ring.multichoose r n)).and
      (Ioo_mem_nhdsLT zero_lt_one)).exists
    refine hlt.not_ge (hasSum_le (fun n => ?_) (hasSum_multichoose_mul_geometric_of_abs_lt_one
      (abs_lt.2 ⟨by linarith [hx.1], hx.2⟩)) hs.hasSum)
    exact mul_le_of_le_one_right (hcoeff_pos n).le (pow_le_one₀ hx.1.le hx.2.le)
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos (hcoeff_pos _)]
  refine ⟨fun hs => not_le.1 fun hq => hnot (hs.of_nonneg_of_le (fun n => (hcoeff_pos n).le)
    fun n => le_mul_of_one_le_right (hcoeff_pos n).le (one_le_pow₀ hq)), fun hq => ?_⟩
  exact (hasSum_multichoose_mul_geometric_of_abs_lt_one (by simpa using hq)).summable

/-! ### The error of the real binomial series -/

/-- The error `(1 + t) ^ a - ∑_{k<K} (a choose k) t ^ k` of the binomial series after `K`
terms. -/
noncomputable def binomialError (a : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  (1 + t) ^ a - ∑ k ∈ Finset.range K, Ring.choose a k * t ^ k

/-- The defining formula of the binomial error. -/
theorem binomialError_def (a : ℝ) (K : ℕ) (t : ℝ) :
    binomialError a K t = (1 + t) ^ a - ∑ k ∈ Finset.range K, Ring.choose a k * t ^ k :=
  (rfl)

/-- After at least one term, the binomial error vanishes at `0`. -/
@[simp]
theorem binomialError_succ_zero (a : ℝ) (K : ℕ) : binomialError a (K + 1) 0 = 0 := by
  simp [binomialError_def, Finset.sum_range_succ']

/-- The derivative of the binomial error is `a` times the error for the exponent `a - 1`, with one
term fewer. -/
theorem hasDerivAt_binomialError (a : ℝ) (K : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (binomialError a (K + 1)) (a * binomialError (a - 1) K t) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (1 + t) ^ a) (a * (1 + t) ^ (a - 1)) t := by
    simpa using ((hasDerivAt_id' t).const_add 1).rpow_const (p := a)
      (Or.inl (ne_of_gt (by linarith : (0 : ℝ) < 1 + t)))
  have h2 : HasDerivAt (fun t : ℝ ↦ ∑ k ∈ Finset.range (K + 1), Ring.choose a k * t ^ k)
      (∑ k ∈ Finset.range K, a * Ring.choose (a - 1) k * t ^ k) t := by
    have hsum : (fun t : ℝ ↦ ∑ k ∈ Finset.range (K + 1), Ring.choose a k * t ^ k) =
        fun t ↦ ∑ k ∈ Finset.range K, Ring.choose a (k + 1) * t ^ (k + 1) + 1 := by
      funext t
      rw [Finset.sum_range_succ']
      simp
    rw [hsum]
    refine (HasDerivAt.fun_sum fun k _ ↦ ?_).add_const 1
    convert ((hasDerivAt_pow (k + 1) t).const_mul (Ring.choose a (k + 1))) using 1
    rw [← Ring.succ_nsmul_choose_succ, nsmul_eq_mul]
    push_cast
    ring
  refine (h1.sub h2).congr_deriv ?_
  rw [binomialError_def, mul_sub, Finset.mul_sum]
  simp [mul_assoc]

/-- On every interval `[l, u]` with `-1 < l`, the binomial error after `K` terms is
`O(|t| ^ K)`. -/
theorem exists_abs_binomialError_le (a : ℝ) (K : ℕ) {l u : ℝ} (hl : -1 < l) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc l u, |binomialError a K t| ≤ C * |t| ^ K := by
  induction K generalizing a l u with
  | zero =>
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := l) (b := u)).exists_bound_of_continuousOn
      (f := binomialError a 0) (by
        refine ContinuousOn.sub ?_ continuousOn_const
        exact (continuousOn_const.add continuousOn_id).rpow_const fun t ht ↦ Or.inl
          (ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)))
    refine ⟨max C 0, le_max_right _ _, fun t ht ↦ ?_⟩
    rw [pow_zero, mul_one, ← Real.norm_eq_abs]
    exact (hC t ht).trans (le_max_left _ _)
  | succ K ih =>
    -- The error vanishes at `0` and its derivative is `O(|t| ^ K)` between `0` and `t`.
    obtain ⟨C, hC0, hC⟩ := ih (a - 1) (l := min l 0) (u := max u 0) (lt_min hl (by norm_num))
    refine ⟨|a| * C, by positivity, fun t ht ↦ ?_⟩
    have hsub : uIcc 0 t ⊆ Icc (min l 0) (max u 0) :=
      uIcc_subset_Icc ⟨min_le_right _ _, le_max_right _ _⟩
        ⟨min_le_of_left_le ht.1, le_max_of_le_left ht.2⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := binomialError a (K + 1)) (C := |a| * C * |t| ^ K)
      (fun τ hτ ↦ (hasDerivAt_binomialError a K
        ((lt_min hl (by norm_num)).trans_le (hsub hτ).1)).hasDerivWithinAt)
      (fun τ hτ ↦ by
        rw [Real.norm_eq_abs, abs_mul, mul_assoc]
        gcongr
        refine (hC τ (hsub hτ)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
        exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using abs_sub_left_of_mem_uIcc hτ) K)
      (convex_uIcc 0 t) left_mem_uIcc right_mem_uIcc
    rw [binomialError_succ_zero, sub_zero, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs] at hmvt
    rw [pow_succ]
    linarith

end TauCeti

end
