/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Series and parameter regularity of regularized hypergeometric functions

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` and its
Gaussian specialization `Complex.regularizedGaussHGFun a b c` as the sums of their power series.
This file records those series as `HasSum` statements, establishes joint holomorphy of
`regularizedGaussHGFun` in `(a, b, c, z)` on `{p | ‖z‖ < 1}`, and develops the function
`₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))`, the case `a = 0`, `b = {b}`, which underlies the Bessel
functions.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
Because `1 / Γ` vanishes at the poles of `Γ`, neither these statements nor the joint holomorphy of
`regularizedGaussHGFun` in `c` needs a pole-avoidance hypothesis on the lower parameter.

## Main results

* `Complex.hasSum_regularizedHGFun` — the power series of `regularizedHGFun a b` converges to it
  everywhere when `a.card ≤ b.card`, absolutely by `Complex.summable_norm_regularizedHGFun`.
* `Complex.hasSum_deriv_regularizedHGFun` — the termwise differentiated series converges to the
  derivative.
* `Complex.hasSum_regularizedGaussHGFun` — the Gaussian series converges to
  `regularizedGaussHGFun a b c z` throughout the open unit disk `‖z‖ < 1`.
* `Complex.analyticOnNhd_regularizedGaussHGFun` — `regularizedGaussHGFun a b c z` is jointly
  holomorphic in `(a, b, c, z)` on `{p | ‖z‖ < 1}`.
* `Complex.regularizedHGFunCoeff_one_singleton` — the coefficients `1 / Γ(b + n)` of the Kummer
  function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments.
* `Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re` — joint continuity in `(b, y)`.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re` — the derivative in `y`.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology

namespace Complex

/-- The coefficients of `₀F₁(; b; z)` are `1 / (n! Γ(b + n))`. -/
@[simp]
theorem regularizedHGFunCoeff_zero_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff 0 {b} n = (n ! * Gamma (b + n))⁻¹ := by
  simp [regularizedHGFunCoeff]

/-- At zero argument and a real parameter, the real part of `₀F₁(; b; 0)` is `1 / Γ(b)`,
including the poles of `Γ`, where its inverse vanishes. -/
theorem regularizedHGFun_zero_singleton_ofReal_zero_re (b : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} 0).re = (Real.Gamma b)⁻¹ := by
  have h : regularizedHGFun 0 {(b : ℂ)} 0 = (((Real.Gamma b)⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_inv, ← Gamma_ofReal]
    simp
  rw [h, ofReal_re]

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges to `regularizedHGFun a b z` at every `z`. -/
theorem hasSum_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have := (regularizedHGFunSeries a b).hasSum (x := z)
    (by simp [radius_regularizedHGFunSeries_eq_top h])
  simpa [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    mul_comm] using this

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges absolutely at every `z`. -/
theorem summable_norm_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ := by
  have := (regularizedHGFunSeries a b).summable_norm_apply (x := z)
    (by simp [radius_regularizedHGFunSeries_eq_top h])
  simpa [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this

/-- When there are at most as many upper as lower parameters, the derivative of
`regularizedHGFun a b` is the sum of its termwise differentiated power series. -/
theorem hasSum_deriv_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * regularizedHGFunCoeff a b (n + 1) * z ^ n)
      (deriv (regularizedHGFun a b) z) := by
  set R : ℝ := ‖z‖ + 1
  have hfun : regularizedHGFun a b = fun w => ∑' n, regularizedHGFunCoeff a b n * w ^ n :=
    funext fun w => (hasSum_regularizedHGFun h w).tsum_eq.symm
  have hd := hasSum_deriv_of_summable_norm (summable_norm_regularizedHGFun h (R : ℂ))
    (F := fun n w => regularizedHGFunCoeff a b n * w ^ n) (U := Metric.ball 0 R)
    (fun n => ((differentiable_pow n).const_mul _).differentiableOn) Metric.isOpen_ball
    (fun n w hw => ?_) (z := z) (by simp [R])
  · rw [hfun]
    convert (hasSum_nat_add_iff' 1).mpr hd using 1
    · ext n
      simp only [deriv_const_mul_field', deriv_pow_field, add_tsub_cancel_right]
      push_cast
      ring
    · simp
  · rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    gcongr

/-- The coefficients of the Kummer function `𝐌(1, b, z) = ₁F₁(1; b; z) / Γ(b)` are
`1 / Γ(b + n)`. -/
@[simp]
theorem regularizedHGFunCoeff_one_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {b} n = (Gamma (b + n))⁻¹ := by
  simpa [regularizedHGFunCoeff] using div_mul_cancel_left₀ (Nat.cast_ne_zero.2 n.factorial_ne_zero)
    (Gamma (b + n))

/-- The complex-valued `₀F₁` series at real parameters and arguments sums to its regularized
hypergeometric value. -/
theorem hasSum_ofReal_regularizedHGFun_zero_singleton (b y : ℝ) :
    HasSum (fun n : ℕ => ((y ^ n / (n ! * Real.Gamma (b + n)) : ℝ) : ℂ))
      (regularizedHGFun 0 {(b : ℂ)} y) := by
  convert hasSum_regularizedHGFun (a := 0) (b := {(b : ℂ)}) (by simp) (y : ℂ) with n
  push_cast [← Gamma_ofReal, regularizedHGFunCoeff_zero_singleton]
  ring

/-- At real arguments, `₀F₁(; b; y)` is real. -/
@[simp]
theorem regularizedHGFun_zero_singleton_ofReal_im (b y : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} y).im = 0 := by
  refine (hasSum_im (hasSum_ofReal_regularizedHGFun_zero_singleton b y)).unique ?_
  simpa only [ofReal_im] using hasSum_zero

/-- At real arguments, `₀F₁(; b; y)` is the sum of the real series `∑ yⁿ / (n! Γ(b + n))`. -/
theorem hasSum_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n ! * Real.Gamma (b + n)))
      (regularizedHGFun 0 {(b : ℂ)} y).re := by
  simpa only [ofReal_re] using hasSum_re (hasSum_ofReal_regularizedHGFun_zero_singleton b y)

/-- The real part of `₀F₁(; b; y)` is jointly continuous in the real parameter `b` and the real
argument `y`. -/
theorem continuous_regularizedHGFun_zero_singleton_ofReal_re :
    Continuous fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re := by
  have heq : (fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re) =
      fun p => ∑' n : ℕ, p.2 ^ n * ((n ! : ℝ)⁻¹ * (Real.Gamma (p.1 + n))⁻¹) := by
    ext p
    simp_rw [← mul_inv, ← div_eq_mul_inv]
    exact (hasSum_regularizedHGFun_zero_singleton_ofReal_re p.1 p.2).tsum_eq.symm
  rw [heq, continuous_iff_continuousAt]
  rintro ⟨b₀, y₀⟩
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le (b₀ - 1)
  set R := |y₀| + 1
  have hmem : (b₀, y₀) ∈ Ioi (b₀ - 1) ×ˢ Ioo (-R) R :=
    ⟨by simp, by constructor <;> linarith [neg_abs_le y₀, le_abs_self y₀]⟩
  refine (continuousOn_tsum (u := fun n => C * (R ^ n / n !)) (fun n => ?_)
    ((Real.summable_pow_div_factorial R).mul_left C) (fun n p hp => ?_)).continuousAt
    ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  · exact (continuous_snd.pow n).mul (continuous_const.mul
      (Real.continuous_inv_Gamma.comp (continuous_fst.add continuous_const))) |>.continuousOn
  · obtain ⟨hb, hy⟩ := hp
    have hy' : |p.2| ≤ R := (abs_lt.2 hy).le
    have hG := hC (p.1 + n) (by simp only [mem_Ioi] at hb; linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_inv, Nat.abs_cast]
    calc |p.2| ^ n * ((n ! : ℝ)⁻¹ * |(Real.Gamma (p.1 + n))⁻¹|)
        ≤ R ^ n * ((n ! : ℝ)⁻¹ * C) := by gcongr
      _ = C * (R ^ n / n !) := by ring

/-- The derivative of `₀F₁(; b; y)` in a real argument `y` is `₀F₁(; b + 1; y)`. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasDerivAt (fun y : ℝ => (regularizedHGFun 0 {(b : ℂ)} y).re)
      (regularizedHGFun 0 {(b : ℂ) + 1} y).re y := by
  have heq : (fun y : ℝ => (regularizedHGFun 0 {(b : ℂ)} y).re) =
      fun y => ∑' n : ℕ, y ^ n / (n ! * Real.Gamma (b + n)) :=
    funext fun y => (hasSum_regularizedHGFun_zero_singleton_ofReal_re b y).tsum_eq.symm
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le b
  set R := |y| + 1
  have hu : Summable fun n : ℕ => C * (n * R ^ (n - 1) / n !) := by
    refine (summable_nat_add_iff 1).1 ?_
    convert (Real.summable_pow_div_factorial R).mul_left C using 2 with n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hd := hasDerivAt_tsum_of_isPreconnected (y₀ := 0) (y := y) hu isOpen_Ioo
    isPreconnected_Ioo (t := Ioo (-R) R)
    (g := fun n y => y ^ n / (n ! * Real.Gamma (b + n)))
    (g' := fun n y => n * y ^ (n - 1) / (n ! * Real.Gamma (b + n)))
    (fun n y _ => (hasDerivAt_pow n y).div_const _) (fun n z hz => ?_)
    ⟨by linarith [abs_nonneg y], by linarith [abs_nonneg y]⟩
    (hasSum_regularizedHGFun_zero_singleton_ofReal_re b 0).summable
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  · rw [heq]
    convert hd using 1
    refine (HasSum.tsum_eq ?_).symm
    rw [← hasSum_nat_add_iff' 1]
    convert hasSum_regularizedHGFun_zero_singleton_ofReal_re (b + 1) y using 1
    · ext n
      have hadd : b + (n + 1 : ℝ) = b + 1 + n := by ring
      rw [Nat.factorial_succ]
      push_cast
      rw [hadd]
      field_simp
    · simp
  · have hz' : |z| ≤ R := (abs_lt.2 hz).le
    have hG := hC (b + n) (by linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, div_eq_mul_inv, mul_inv, abs_mul, abs_mul, abs_mul, abs_pow, abs_inv,
      Nat.abs_cast, Nat.abs_cast]
    calc (n : ℝ) * |z| ^ (n - 1) * ((n ! : ℝ)⁻¹ * |(Real.Gamma (b + n))⁻¹|)
        ≤ n * R ^ (n - 1) * ((n ! : ℝ)⁻¹ * C) := by gcongr
      _ = C * (n * R ^ (n - 1) / n !) := by ring

/-- On the open unit disk `‖z‖ < 1`, the Gaussian hypergeometric power series converges to
`regularizedGaussHGFun a b c z` for all complex parameters `a`, `b`, `c`. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / (n ! * Gamma (c + n))) * z ^ n)
      (regularizedGaussHGFun a b c z) := by
  have hmem : ENNReal.ofReal ‖z‖ < (regularizedGaussHGFunSeries a b c).radius :=
    (ENNReal.ofReal_lt_one.2 hz).trans_le (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have h := (regularizedGaussHGFunSeries a b c).hasSum (x := z)
    (by simpa [edist_zero_right, ofReal_norm] using hmem)
  rw [regularizedGaussHGFun]
  convert h using 1
  ext n
  have hc := coeff_regularizedGaussHGFunSeries (a := a) (b := b) (c := c) (n := n)
  simp only [regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hc ⊢
  rw [← hc]
  simp [FormalMultilinearSeries.coeff_ofScalars, mul_comm]

/-- On the open unit disk `‖z‖ < 1`, the Gaussian hypergeometric power series converges absolutely
for all complex parameters `a`, `b`, `c`. -/
theorem summable_norm_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ‖((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / (n ! * Gamma (c + n))) *
        z ^ n‖ := by
  have hmem : ENNReal.ofReal ‖z‖ < (regularizedGaussHGFunSeries a b c).radius :=
    (ENNReal.ofReal_lt_one.2 hz).trans_le (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have h := (regularizedGaussHGFunSeries a b c).summable_norm_apply (x := z)
    (by simpa [edist_zero_right, ofReal_norm] using hmem)
  convert h using 1
  ext n
  have hc := coeff_regularizedGaussHGFunSeries (a := a) (b := b) (c := c) (n := n)
  simp only [regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hc ⊢
  rw [← hc]
  simp [FormalMultilinearSeries.coeff_ofScalars, mul_comm]

private theorem norm_ascPochhammer_eval_le_factorial {w : ℂ} {M : ℕ} (hw : ‖w‖ ≤ M) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval w‖ ≤ ((M + n)! : ℝ) := by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, Polynomial.eval_one, norm_one, add_zero]
    exact_mod_cast Nat.factorial_pos M
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul]
    have hwn : ‖w + n‖ ≤ (M + n + 1 : ℝ) := by
      calc ‖w + n‖ ≤ ‖w‖ + ‖(n : ℂ)‖ := norm_add_le _ _
        _ ≤ M + n + 1 := by rw [Complex.norm_natCast]; linarith
    calc ‖(ascPochhammer ℂ n).eval w‖ * ‖w + n‖
        ≤ ((M + n)! : ℝ) * (M + n + 1) := mul_le_mul ih hwn (norm_nonneg _) (by positivity)
      _ = ((M + (n + 1))! : ℝ) := by
        rw [← add_assoc, Nat.factorial_succ]
        push_cast
        ring

private theorem norm_inv_Gamma_add_nat_le {c : ℂ} {N₀ : ℕ} {C : ℝ}
    (hc : 1 ≤ (c + N₀).re) (hcC : ‖(Gamma (c + N₀))⁻¹‖ ≤ C) (m : ℕ) :
    ‖(Gamma (c + ((N₀ + m : ℕ) : ℂ)))⁻¹‖ ≤ C / (m ! : ℝ) := by
  have _hC : 0 ≤ C := (norm_nonneg _).trans hcC
  induction m with
  | zero => simpa using hcC
  | succ m ih =>
    set s : ℂ := c + ((N₀ + m : ℕ) : ℂ)
    have hs_re : (m + 1 : ℝ) ≤ s.re := by
      simp only [s, add_re, natCast_re] at hc ⊢
      push_cast
      linarith
    have hs_ne : s ≠ 0 := fun h => by
      simp only [h, zero_re] at hs_re
      linarith [m.cast_nonneg (α := ℝ)]
    have hs_norm : (m + 1 : ℝ) ≤ ‖s‖ := hs_re.trans (re_le_norm s)
    have hstep : c + ((N₀ + (m + 1) : ℕ) : ℂ) = s + 1 := by
      simp only [s]
      push_cast
      ring
    rw [hstep, Gamma_add_one s hs_ne, mul_inv, norm_mul, norm_inv]
    calc ‖s‖⁻¹ * ‖(Gamma s)⁻¹‖
        ≤ (m + 1 : ℝ)⁻¹ * (C / (m ! : ℝ)) :=
          mul_le_mul (inv_anti₀ (by positivity) hs_norm) ih (norm_nonneg _) (by positivity)
      _ = C / ((m + 1)! : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp

private theorem norm_regularizedGaussTerm_shift_le {M N₀ : ℕ} {C r : ℝ} (hC : 0 ≤ C) (_hr : 0 ≤ r)
    {a b c z : ℂ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : 1 ≤ (c + N₀).re)
    (hcC : ‖(Gamma (c + N₀))⁻¹‖ ≤ C) (hz : ‖z‖ ≤ r) (m : ℕ) :
    ‖((ascPochhammer ℂ (N₀ + m)).eval a * (ascPochhammer ℂ (N₀ + m)).eval b /
        ((N₀ + m)! * Gamma (c + ((N₀ + m : ℕ) : ℂ)))) * z ^ (N₀ + m)‖ ≤
      C * (((M + N₀ + m : ℕ) : ℝ) ^ (2 * (M + N₀)) * r ^ (N₀ + m)) := by
  generalize hK : M + N₀ = K
  have hfac : ((m + K)! : ℝ) ≤ (m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K := by
    have hnat : (m + K)! ≤ m ! * (m + K) ^ K := by
      rw [← Nat.factorial_mul_ascFactorial m K]
      exact Nat.mul_le_mul_left (m !) (Nat.ascFactorial_le_pow_add m K)
    simpa [add_comm m K] using (Nat.cast_le (α := ℝ)).2 hnat
  have ha' : ‖(ascPochhammer ℂ (N₀ + m)).eval a‖ ≤ (m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K := by
    refine (norm_ascPochhammer_eval_le_factorial ha (N₀ + m)).trans ?_
    have hidx : M + (N₀ + m) = m + K := by omega
    rwa [hidx]
  have hb' : ‖(ascPochhammer ℂ (N₀ + m)).eval b‖ ≤ (m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K := by
    refine (norm_ascPochhammer_eval_le_factorial hb (N₀ + m)).trans ?_
    have hidx : M + (N₀ + m) = m + K := by omega
    rwa [hidx]
  have hNm : (m ! : ℝ) ≤ ((N₀ + m)! : ℝ) :=
    (Nat.cast_le (α := ℝ)).2 (Nat.factorial_le (Nat.le_add_left m N₀))
  have hm_pos : (0 : ℝ) < m ! := Nat.cast_pos.2 m.factorial_pos
  have hG := norm_inv_Gamma_add_nat_le hc hcC m
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv,
    Complex.norm_natCast, norm_pow]
  calc ‖(ascPochhammer ℂ (N₀ + m)).eval a‖ * ‖(ascPochhammer ℂ (N₀ + m)).eval b‖ *
        (((N₀ + m)! : ℝ)⁻¹ * ‖(Gamma (c + ((N₀ + m : ℕ) : ℂ)))⁻¹‖) * ‖z‖ ^ (N₀ + m)
      ≤ ((m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K) * ((m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K) *
          ((m ! : ℝ)⁻¹ * (C / (m ! : ℝ))) * r ^ (N₀ + m) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul ha' hb' (norm_nonneg _) (by positivity))
          (mul_le_mul (inv_anti₀ hm_pos hNm) hG (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)) (pow_le_pow_left₀ (norm_nonneg _) hz _)
          (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = C * (((K + m : ℕ) : ℝ) ^ (2 * K) * r ^ (N₀ + m)) := by
      have hpow : ((K + m : ℕ) : ℝ) ^ K * ((K + m : ℕ) : ℝ) ^ K =
          ((K + m : ℕ) : ℝ) ^ (2 * K) := by rw [two_mul, pow_add]
      have hcancel : (m ! : ℝ) * (m ! : ℝ) * ((m ! : ℝ)⁻¹ * (C / (m ! : ℝ))) = C := by
        field_simp [hm_pos.ne']
      generalize ((K + m : ℕ) : ℝ) ^ K = pk at hpow ⊢
      generalize ((K + m : ℕ) : ℝ) ^ (2 * K) = p2k at hpow ⊢
      calc (m ! : ℝ) * pk * ((m ! : ℝ) * pk) * ((m ! : ℝ)⁻¹ * (C / (m ! : ℝ))) * r ^ (N₀ + m)
          = ((m ! : ℝ) * (m ! : ℝ) * ((m ! : ℝ)⁻¹ * (C / (m ! : ℝ)))) *
              ((pk * pk) * r ^ (N₀ + m)) := by ring
        _ = C * (p2k * r ^ (N₀ + m)) := by rw [hcancel, hpow]

private theorem summable_gauss_majorant (C : ℝ) (K N₀ : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun m : ℕ => C * (((K + m : ℕ) : ℝ) ^ (2 * K) * r ^ (N₀ + m)) := by
  generalize 2 * K = L
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ L * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one L (by rw [Real.norm_of_nonneg hr0.le]; exact hr1)
  have hpow : Summable fun m : ℕ => ((m + K : ℕ) : ℝ) ^ L * r ^ (m + K) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ L * r ^ n) K).2 hbase
  refine (hpow.mul_left (C * (r ^ N₀ / r ^ K))).congr fun m => ?_
  have hrK : r ^ K ≠ 0 := pow_ne_zero K hr0.ne'
  rw [add_comm m K]
  generalize ((K + m : ℕ) : ℝ) ^ L = pL
  calc C * (r ^ N₀ / r ^ K) * (pL * r ^ (K + m))
      = C * (pL * ((r ^ N₀ / r ^ K * r ^ K) * r ^ m)) := by
        rw [pow_add]
        ring
    _ = C * (pL * r ^ (N₀ + m)) := by
      rw [div_mul_cancel₀ _ hrK, ← pow_add]

private theorem differentiable_eval_ascPochhammer (n : ℕ) :
    Differentiable ℂ fun z : ℂ => (ascPochhammer ℂ n).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [ascPochhammer_succ_eval]
    exact ih.mul (differentiable_id.add_const (n : ℂ))

private def regularizedGaussTerm (n : ℕ) (v : Fin 4 → ℂ) : ℂ :=
  ((ascPochhammer ℂ n).eval (v 0) * (ascPochhammer ℂ n).eval (v 1) /
    (n ! * Gamma (v 2 + n))) * v 3 ^ n

private theorem differentiable_regularizedGaussTerm (n : ℕ) :
    Differentiable ℂ (regularizedGaussTerm n) := by
  have h0 : Differentiable ℂ (fun v : Fin 4 → ℂ => (ascPochhammer ℂ n).eval (v 0)) :=
    (differentiable_eval_ascPochhammer n).comp (differentiable_apply 0)
  have h1 : Differentiable ℂ (fun v : Fin 4 → ℂ => (ascPochhammer ℂ n).eval (v 1)) :=
    (differentiable_eval_ascPochhammer n).comp (differentiable_apply 1)
  have h2 : Differentiable ℂ (fun v : Fin 4 → ℂ => (Gamma (v 2 + n))⁻¹) := fun v =>
    DifferentiableAt.comp (g := fun s => (Gamma s)⁻¹) v (differentiable_one_div_Gamma _)
      ((differentiableAt_apply 2 v).add_const (n : ℂ))
  have heq : regularizedGaussTerm n =
      fun v => (ascPochhammer ℂ n).eval (v 0) * (ascPochhammer ℂ n).eval (v 1) *
        ((n ! : ℂ)⁻¹ * (Gamma (v 2 + n))⁻¹) * v 3 ^ n := by
    ext v
    dsimp [regularizedGaussTerm]
    rw [div_eq_mul_inv, mul_inv]
  rw [heq]
  exact ((h0.mul h1).mul (h2.const_mul _)).mul ((differentiable_apply 3).pow n)

private theorem norm_regularizedGaussTerm_shift_le_on_box {v₀ v : Fin 4 → ℂ} {M N₀ : ℕ} {C r : ℝ}
    (hM0 : ⌈‖v₀ 0‖ + 1⌉₊ ≤ M) (hM1 : ⌈‖v₀ 1‖ + 1⌉₊ ≤ M) (hN₀ : ⌈-(v₀ 2).re⌉₊ + 2 ≤ N₀)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hv0 : v 0 ∈ Metric.ball (v₀ 0) 1) (hv1 : v 1 ∈ Metric.ball (v₀ 1) 1)
    (hv2 : v 2 ∈ Metric.ball (v₀ 2) 1) (hv3 : v 3 ∈ Metric.ball 0 r)
    (hcC : ‖(Gamma (v 2 + N₀))⁻¹‖ ≤ C) (m : ℕ) :
    ‖regularizedGaussTerm (N₀ + m) v‖ ≤
      C * (((M + N₀ + m : ℕ) : ℝ) ^ (2 * (M + N₀)) * r ^ (N₀ + m)) := by
  have hnorm_le : ∀ i : Fin 4, v i ∈ Metric.ball (v₀ i) 1 → ⌈‖v₀ i‖ + 1⌉₊ ≤ M → ‖v i‖ ≤ M := by
    intro i hvi hMi
    have hin : ‖v i - v₀ i‖ < 1 := mem_ball_iff_norm.1 hvi
    have hlt : ‖v i‖ < ‖v₀ i‖ + 1 := by
      calc ‖v i‖ ≤ ‖v i - v₀ i‖ + ‖v₀ i‖ := norm_le_norm_sub_add _ _
        _ < 1 + ‖v₀ i‖ := by linarith
        _ = ‖v₀ i‖ + 1 := add_comm _ _
    exact hlt.le.trans ((Nat.le_ceil _).trans (by exact_mod_cast hMi))
  have hc : 1 ≤ (v 2 + N₀).re := by
    have h2n : ‖v 2 - v₀ 2‖ < 1 := mem_ball_iff_norm.1 hv2
    have hre : (v₀ 2).re - 1 ≤ (v 2).re := by
      have h := (abs_re_le_norm (v 2 - v₀ 2)).trans h2n.le
      linarith [(abs_le.1 h).1, sub_re (v 2) (v₀ 2)]
    have hN : -(v₀ 2).re + 2 ≤ N₀ := by
      have hN' : (⌈-(v₀ 2).re⌉₊ : ℝ) + 2 ≤ N₀ := by exact_mod_cast hN₀
      linarith [Nat.le_ceil (-(v₀ 2).re)]
    simp only [add_re, natCast_re]
    linarith
  exact norm_regularizedGaussTerm_shift_le hC hr (hnorm_le 0 hv0 hM0) (hnorm_le 1 hv1 hM1) hc hcC
    (by simpa [mem_ball_zero_iff] using (mem_ball_zero_iff.1 hv3).le) m

private theorem analyticAt_tsum_regularizedGaussTerm_shift {v₀ : Fin 4 → ℂ} {U : Set (Fin 4 → ℂ)}
    {N₀ : ℕ} {u : ℕ → ℝ} (hU_open : IsOpen U) (hv₀U : v₀ ∈ U) (hu : Summable u)
    (hbound : ∀ m : ℕ, ∀ v ∈ U, ‖regularizedGaussTerm (N₀ + m) v‖ ≤ u m) :
    AnalyticAt ℂ (fun v => ∑' m : ℕ, regularizedGaussTerm (N₀ + m) v) v₀ := by
  have htail_cont : ContinuousOn (fun v => ∑' m : ℕ, regularizedGaussTerm (N₀ + m) v) U :=
    continuousOn_tsum
      (fun m => (differentiable_regularizedGaussTerm (N₀ + m)).continuous.continuousOn) hu hbound
  refine htail_cont.analyticAt_of_differentiableAt_update (hU_open.mem_nhds hv₀U) ?_
  intro y hy i
  let V : Set ℂ := (fun x => Function.update y i x) ⁻¹' U
  have hV_open : IsOpen V := hU_open.preimage (Continuous.update continuous_const i continuous_id)
  have hyV : y i ∈ V := by simpa [V] using hy
  have hupd : Differentiable ℂ (fun x : ℂ => Function.update y i x) := by
    rw [differentiable_pi]; intro j; by_cases hj : j = i <;> simp [Function.update, hj]
  exact (differentiableOn_tsum_of_summable_norm hu
    (fun m => ((differentiable_regularizedGaussTerm (N₀ + m)).comp hupd).differentiableOn)
    hV_open (fun m w hw => hbound m _ hw)).differentiableAt (hV_open.mem_nhds hyV)

private theorem analyticAt_regularizedGaussHGFun_pi {v₀ : Fin 4 → ℂ} (hv₀ : ‖v₀ 3‖ < 1) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ => regularizedGaussHGFun (v 0) (v 1) (v 2) (v 3)) v₀ := by
  let M : ℕ := max ⌈‖v₀ 0‖ + 1⌉₊ ⌈‖v₀ 1‖ + 1⌉₊
  let N₀ : ℕ := ⌈-(v₀ 2).re⌉₊ + 2
  let r : ℝ := (‖v₀ 3‖ + 1) / 2
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (v₀ 2) 1).exists_bound_of_continuousOn
    (f := fun c : ℂ => (Gamma (c + N₀))⁻¹)
    ((differentiable_one_div_Gamma.comp
      (differentiable_id.add_const (N₀ : ℂ))).continuous.continuousOn)
  let C : ℝ := max C₀ 0
  let u : ℕ → ℝ := fun m => C * (((M + N₀ + m : ℕ) : ℝ) ^ (2 * (M + N₀)) * r ^ (N₀ + m))
  have hu : Summable u := summable_gauss_majorant C (M + N₀) N₀ hr0 hr1
  let U : Set (Fin 4 → ℂ) :=
    ((fun v : Fin 4 → ℂ => v 0) ⁻¹' Metric.ball (v₀ 0) 1 ∩
      (fun v : Fin 4 → ℂ => v 1) ⁻¹' Metric.ball (v₀ 1) 1) ∩
    ((fun v : Fin 4 → ℂ => v 2) ⁻¹' Metric.ball (v₀ 2) 1 ∩
      (fun v : Fin 4 → ℂ => v 3) ⁻¹' Metric.ball 0 r)
  have hU_open : IsOpen U :=
    ((Metric.isOpen_ball.preimage (continuous_apply 0)).inter
      (Metric.isOpen_ball.preimage (continuous_apply 1))).inter
      ((Metric.isOpen_ball.preimage (continuous_apply 2)).inter
        (Metric.isOpen_ball.preimage (continuous_apply 3)))
  have hv₀U : v₀ ∈ U := ⟨⟨Metric.mem_ball_self zero_lt_one, Metric.mem_ball_self zero_lt_one⟩,
    ⟨Metric.mem_ball_self zero_lt_one, by simp [Metric.mem_ball, r]; linarith⟩⟩
  have hbound : ∀ m : ℕ, ∀ v ∈ U, ‖regularizedGaussTerm (N₀ + m) v‖ ≤ u m := fun m v hv =>
    norm_regularizedGaussTerm_shift_le_on_box (le_max_left _ _) (le_max_right _ _) le_rfl
      (le_max_right _ _) hr0.le hv.1.1 hv.1.2 hv.2.1 hv.2.2
      ((hC₀ (v 2) (Metric.ball_subset_closedBall hv.2.1)).trans (le_max_left _ _)) m
  have htail_an := analyticAt_tsum_regularizedGaussTerm_shift hU_open hv₀U hu hbound
  have hpre_diff : Differentiable ℂ (fun v => ∑ n ∈ Finset.range N₀, regularizedGaussTerm n v) :=
    Differentiable.fun_sum fun n _ => differentiable_regularizedGaussTerm n
  have hpre_an : AnalyticAt ℂ (fun v => ∑ n ∈ Finset.range N₀, regularizedGaussTerm n v) v₀ :=
    hpre_diff.differentiableOn.analyticAt_of_finiteDimensional univ_mem
  refine (hpre_an.add htail_an).congr ?_
  filter_upwards [hU_open.mem_nhds hv₀U] with v hv
  have hv3 : ‖v 3‖ < 1 := (mem_ball_zero_iff.1 hv.2.2).trans hr1
  have hsum := hasSum_regularizedGaussHGFun (v 0) (v 1) (v 2) hv3
  rw [Pi.add_apply, ← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add N₀]
  simp [regularizedGaussTerm, add_comm N₀]

/-- **Joint holomorphy of the regularized Gauss hypergeometric function.** On `{p | ‖z‖ < 1}`,
`regularizedGaussHGFun a b c z` is jointly analytic in all four complex variables `(a, b, c, z)`,
with no pole-avoidance restriction on `c`. -/
theorem analyticOnNhd_regularizedGaussHGFun :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => regularizedGaussHGFun p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | ‖p.2.2.2‖ < 1} := by
  intro p hp
  let emb : ℂ × ℂ × ℂ × ℂ → Fin 4 → ℂ := fun q i =>
    match i with
    | 0 => q.1
    | 1 => q.2.1
    | 2 => q.2.2.1
    | 3 => q.2.2.2
  have hemb_diff : Differentiable ℂ emb := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> dsimp [emb] <;> fun_prop
  have hemb : AnalyticAt ℂ emb p :=
    hemb_diff.differentiableOn.analyticAt_of_finiteDimensional univ_mem
  exact ((analyticAt_regularizedGaussHGFun_pi (v₀ := emb p)
    (by simpa [emb] using hp)).comp hemb).congr (Eventually.of_forall fun _ => rfl)

end Complex
