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
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Analytic.OfScalars

/-!
# Regularized hypergeometric functions `₀F₁` and `₂F₁`

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement, develops the
function `₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))` (`a = 0`, `b = {b}`) underlying the Bessel functions,
and establishes the unit-disk calculus, parameter-shift relations, first-order contiguous-derivative
relations, and parameter entirety of the regularized Gaussian function
`Complex.regularizedGaussHGFun a b c z = ∑ (a)ₙ (b)ₙ zⁿ / (n! Γ(c + n))`.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
Likewise, on the open unit disk `‖z‖ < 1`, `Complex.regularizedGaussHGFun a b c` is analytic in `z`,
has derivative `a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z`, satisfies the classical
first-order parameter-shift and derivative-contiguous relations, and is entire under holomorphic
variation of `(a, b, c)`. Because `1 / Γ` vanishes at the poles of `Γ`, none of these statements
needs a pole-avoidance hypothesis on the lower parameter.

## Main results

* `Complex.hasSum_regularizedHGFun` — the power series of `regularizedHGFun a b` converges to it
  everywhere when `a.card ≤ b.card`, absolutely by `Complex.summable_norm_regularizedHGFun`.
* `Complex.hasSum_deriv_regularizedHGFun` — the termwise differentiated series converges to the
  derivative.
* `Complex.regularizedHGFunCoeff_one_singleton` — the coefficients `1 / Γ(b + n)` of the Kummer
  function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments.
* `Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re` — joint continuity in `(b, y)`.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re` — the derivative in `y`.
* `Complex.hasFPowerSeriesOnBall_regularizedGaussHGFun`, `Complex.analyticAt_regularizedGaussHGFun`,
  `Complex.analyticOnNhd_regularizedGaussHGFun` — power-series representation and analyticity of
  `regularizedGaussHGFun` on the open unit disk.
* `Complex.deriv_regularizedGaussHGFun`, `Complex.hasDerivAt_regularizedGaussHGFun` — the derivative
  `a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z` on `‖z‖ < 1` (DLMF 15.5.1).
* `Complex.regularizedGaussHGFun_eq_sub_mul_add_mul`,
  `Complex.regularizedGaussHGFun_eq_sub_mul_mul`,
  `Complex.mul_deriv_regularizedGaussHGFun_add_mul_eq`,
  `Complex.mul_deriv_regularizedGaussHGFun_add_right`,
  `Complex.mul_one_sub_mul_deriv_regularizedGaussHGFun` — parameter-shift and first-order
  contiguous-derivative identities on `‖z‖ < 1` (DLMF §15.5).
* `Differentiable.regularizedGaussHGFun` — entirety of
  `w ↦ regularizedGaussHGFun (fa w) (fb w) (fc w) z` for holomorphic `fa`, `fb`, `fc` and `‖z‖ < 1`.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology ENNReal

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

section Gaussian

/-- The regularized Gaussian hypergeometric function is represented on the open unit ball by
`regularizedGaussHGFunSeries a b c`, for all complex parameters `a`, `b`, `c`. -/
theorem hasFPowerSeriesOnBall_regularizedGaussHGFun (a b c : ℂ) :
    HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (regularizedGaussHGFunSeries a b c) 0 1 := by
  have hr := radius_regularizedGaussHGFunSeries_ge_one a b c
  exact ⟨hr, zero_lt_one, fun hy =>
    ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall (zero_lt_one.trans_le hr)).hasSum
      (Metric.eball_subset_eball hr hy)⟩

/-- For any complex parameters `a`, `b`, `c`, `regularizedGaussHGFun a b c` is analytic at every
point of the open unit disk. -/
theorem analyticAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedGaussHGFun a b c) z :=
  analyticAt_regularizedHGFun_of_card_eq_add_one rfl hz

/-- For any complex parameters `a`, `b`, `c`, `regularizedGaussHGFun a b c` is analytic on the open
unit disk. -/
theorem analyticOnNhd_regularizedGaussHGFun (a b c : ℂ) :
    AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (Metric.ball 0 1) := fun _ hz =>
  analyticAt_regularizedGaussHGFun a b c (by simpa using hz)

/-- The defining `tsum` expansion of `regularizedGaussHGFun a b c z` in powers of `z`. -/
theorem regularizedGaussHGFun_eq_tsum_coeff_mul_pow (a b c z : ℂ) :
    regularizedGaussHGFun a b c z =
      ∑' n : ℕ, (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  simp [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.sum, mul_comm]

/-- On the open unit disk, the power series of `regularizedGaussHGFun a b c` is summable. -/
theorem summable_coeff_regularizedGaussHGFunSeries_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  have hmem : z ∈ Metric.eball (0 : ℂ) 1 := by
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  have hs := (hasFPowerSeriesOnBall_regularizedGaussHGFun a b c).hasSum (y := z) hmem
  simpa [regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs.summable

private theorem succ_mul_coeff_regularizedGaussHGFunSeries_succ (a b c : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      a * b * (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff n := by
  have ha := (ascPochhammer_succ_eval n a).trans (ascPochhammer_eval_succ n a).symm
  have hb := (ascPochhammer_succ_eval n b).trans (ascPochhammer_eval_succ n b).symm
  have hn : (n : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero n
  have hc : c + ((n : ℂ) + 1) = c + 1 + n := by ring
  rw [coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries, ha, hb,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hc]
  field_simp

/-- On the open unit disk, the derivative of `regularizedGaussHGFun a b c` is
`a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1)` (DLMF 15.5.1 in regularized form). -/
theorem deriv_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (regularizedGaussHGFun a b c) z =
      a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  have hz' : ‖z‖ₑ < 1 := by rwa [← ofReal_norm, ENNReal.ofReal_lt_one]
  have hcoeff : (regularizedGaussHGFunSeries a b c).coeff = regularizedHGFunCoeff {a, b} {c} :=
    regularizedHGFunSeries_coeff
  have hp : HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (FormalMultilinearSeries.ofScalars ℂ (regularizedGaussHGFunSeries a b c).coeff) 0 1 := by
    rw [hcoeff]
    exact hasFPowerSeriesOnBall_regularizedGaussHGFun a b c
  have hd := hp.iteratedDeriv_eq_tsum_descFactorial_mul_pow hz' 1
  rw [iteratedDeriv_one] at hd
  have hsum : Summable fun k : ℕ =>
      (k.descFactorial 1 : ℂ) * (regularizedGaussHGFunSeries a b c).coeff k * z ^ (k - 1) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_coeff_regularizedGaussHGFunSeries_mul_pow (a + 1) (b + 1) (c + 1) hz).mul_left
      (a * b)).congr fun n => ?_
    simp only [Nat.descFactorial_one, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one,
      succ_mul_coeff_regularizedGaussHGFunSeries_succ, mul_assoc]
  rw [hd, hsum.tsum_eq_zero_add]
  simp only [Nat.descFactorial_one, Nat.cast_zero, zero_mul, zero_add, add_tsub_cancel_right,
    Nat.cast_add, Nat.cast_one, succ_mul_coeff_regularizedGaussHGFunSeries_succ, mul_assoc,
    regularizedGaussHGFun_eq_tsum_coeff_mul_pow, ← tsum_mul_left]

/-- `HasDerivAt` form of `Complex.deriv_regularizedGaussHGFun` on the open unit disk. -/
theorem hasDerivAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (regularizedGaussHGFun a b c)
      (a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z) z := by
  rw [← deriv_regularizedGaussHGFun a b c hz]
  exact (analyticAt_regularizedGaussHGFun a b c hz).differentiableAt.hasDerivAt

/-- Regularized Gauss contiguous shift in `c` and `a` on the open unit disk (DLMF 15.5.15):
`𝐅(a, b; c; z) = (c - a) 𝐅(a, b; c + 1; z) + a 𝐅(a + 1, b; c + 1; z)`. -/
theorem regularizedGaussHGFun_eq_sub_mul_add_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z := by
  have hs₁ := (summable_coeff_regularizedGaussHGFunSeries_mul_pow a b (c + 1) hz).mul_left (c - a)
  have hs₂ :=
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow (a + 1) b (c + 1) hz).mul_left a
  simp_rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow, ← tsum_mul_left, ← hs₁.tsum_add hs₂]
  refine tsum_congr fun n => ?_
  have hap : a * (ascPochhammer ℂ n).eval (a + 1) = (a + n) * (ascPochhammer ℂ n).eval a := by
    rw [ascPochhammer_eval_succ, mul_comm]
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n)
  simp only [coeff_regularizedGaussHGFunSeries, div_eq_mul_inv, mul_inv]
  rw [add_right_comm c 1 (n : ℂ), hΓ]
  linear_combination
    (ascPochhammer ℂ n).eval b * (n ! : ℂ)⁻¹ * (Gamma (c + n + 1))⁻¹ * z ^ n * (-hap)

/-- Regularized Gauss contiguous shift in `b` on the open unit disk (DLMF 15.5.16):
`𝐅(a, b; c; z) = 𝐅(a, b + 1; c; z) - a z 𝐅(a + 1, b + 1; c + 1; z)`. -/
theorem regularizedGaussHGFun_eq_sub_mul_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (b + 1) c z -
        a * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  rw [eq_sub_iff_add_eq]
  have hs₀ := summable_coeff_regularizedGaussHGFunSeries_mul_pow a b c hz
  have hs₁ := (summable_coeff_regularizedGaussHGFunSeries_mul_pow
    (a + 1) (b + 1) (c + 1) hz).mul_left (a * z)
  have hs₂ := summable_coeff_regularizedGaussHGFunSeries_mul_pow a (b + 1) c hz
  simp_rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow]
  rw [← tsum_mul_left, hs₀.tsum_eq_zero_add, hs₂.tsum_eq_zero_add, add_assoc,
    ← ((summable_nat_add_iff 1).2 hs₀).tsum_add hs₁]
  simp only [coeff_regularizedGaussHGFunSeries, ascPochhammer_zero, Polynomial.eval_one, mul_one,
    Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero, pow_zero]
  congr 1
  refine tsum_congr fun n => ?_
  have hb₁ := (ascPochhammer_succ_eval n b).trans (ascPochhammer_eval_succ n b).symm
  have ha₁ := (ascPochhammer_succ_eval n a).trans (ascPochhammer_eval_succ n a).symm
  have hb₂ := ascPochhammer_succ_eval n (b + 1)
  have hn : (n : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero n
  have hc : c + ((n : ℂ) + 1) = c + 1 + n := by ring
  rw [hb₁, ha₁, hb₂, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hc, pow_succ]
  field_simp
  ring

/-- Regularized differential-contiguous relation lowering `c` on the open unit disk (DLMF 15.5.4):
`z * deriv (𝐅(a, b; c + 1)) z + c * 𝐅(a, b; c + 1; z) = 𝐅(a, b; c; z)`. -/
theorem mul_deriv_regularizedGaussHGFun_add_mul_eq (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (regularizedGaussHGFun a b (c + 1)) z + c * regularizedGaussHGFun a b (c + 1) z =
      regularizedGaussHGFun a b c z := by
  have h₁ := regularizedGaussHGFun_eq_sub_mul_add_mul a b c hz
  have h₂ := regularizedGaussHGFun_eq_sub_mul_mul b a (c + 1) hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₂
  rw [deriv_regularizedGaussHGFun a b (c + 1) hz]
  linear_combination -h₁ + a * h₂

/-- Regularized differential-contiguous relation raising `b` on the open unit disk (DLMF 15.5.3):
`z * deriv (𝐅(a, b; c)) z + b * 𝐅(a, b; c; z) = b * 𝐅(a, b + 1; c; z)`. -/
theorem mul_deriv_regularizedGaussHGFun_add_right (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (regularizedGaussHGFun a b c) z + b * regularizedGaussHGFun a b c z =
      b * regularizedGaussHGFun a (b + 1) c z := by
  rw [deriv_regularizedGaussHGFun a b c hz]
  linear_combination b * regularizedGaussHGFun_eq_sub_mul_mul a b c hz

/-- Regularized differential-contiguous relation lowering `b` on the open unit disk (DLMF 15.5.19):
`z * (1 - z) * deriv (𝐅(a, b; c)) z` equals
`(c - b) * 𝐅(a, b - 1; c; z) - (c - b - a * z) * 𝐅(a, b; c; z)`. -/
theorem mul_one_sub_mul_deriv_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (regularizedGaussHGFun a b c) z =
      (c - b) * regularizedGaussHGFun a (b - 1) c z -
        (c - b - a * z) * regularizedGaussHGFun a b c z := by
  have h₁ := regularizedGaussHGFun_eq_sub_mul_add_mul b (a + 1) c hz
  rw [regularizedGaussHGFun_symm b (a + 1), regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₁
  have h₂ := regularizedGaussHGFun_eq_sub_mul_mul b a c hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₂
  have h₃ := regularizedGaussHGFun_eq_sub_mul_mul a (b - 1) c hz
  rw [sub_add_cancel] at h₃
  rw [deriv_regularizedGaussHGFun a b c hz]
  linear_combination -a * z * h₁ - a * z * h₂ - (c - b) * h₃

private theorem norm_regularizedGaussHGFun_term_add_le {fa fb fc : ℂ → ℂ} {M k : ℕ} {CΓ : ℝ}
    {w z : ℂ} (hfa : ‖fa w‖ ≤ M) (hfb : ‖fb w‖ ≤ M) (hfc : 1 ≤ (fc w + ((M + 1 : ℕ) : ℂ)).re)
    (hCΓ : ‖(Gamma (fc w + ((M + 1 : ℕ) : ℂ)))⁻¹‖ ≤ CΓ) :
    ‖(ascPochhammer ℂ (M + 1 + k)).eval (fa w) * (ascPochhammer ℂ (M + 1 + k)).eval (fb w) /
        ((M + 1 + k)! * Gamma (fc w + ((M + 1 + k : ℕ) : ℂ))) * z ^ (M + 1 + k)‖ ≤
      CΓ * (M.ascFactorial (M + 1) : ℝ) ^ 2 * ‖z‖ ^ (M + 1) *
        ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff k *
          z ^ k‖ := by
  have hpoch {s : ℂ} (hs : ‖s‖ ≤ M) (n : ℕ) :
      ‖(ascPochhammer ℂ n).eval s‖ ≤ (M.ascFactorial n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_right, Nat.ascFactorial_succ, Nat.cast_mul, mul_comm ((M + n : ℕ) : ℝ)]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, norm_mul]
      exact mul_le_mul ih ((norm_add_le s n).trans (by simp [hs])) (norm_nonneg _)
        (Nat.cast_nonneg _)
  let P : ℝ := M.ascFactorial (M + 1)
  have hΓk : ‖(Gamma (fc w + ((M + 1 + k : ℕ) : ℂ)))⁻¹‖ ≤ CΓ / k ! := by
    rw [Nat.cast_add, ← add_assoc]
    exact (norm_inv_Gamma_add_natCast_le hfc k).trans
      (div_le_div_of_nonneg_right hCΓ (Nat.cast_nonneg _))
  have hM2 : M + (M + 1) = 2 * M + 1 := by omega
  have hpM : (M.ascFactorial (M + 1 + k) : ℝ) = P * ((2 * M + 1).ascFactorial k : ℝ) := by
    rw [← Nat.ascFactorial_mul_ascFactorial M (M + 1) k, hM2, Nat.cast_mul]
  have hk_coeff :
      ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff k *
          z ^ k‖ =
        ((2 * M + 1).ascFactorial k : ℝ) ^ 2 / (k ! * k !) * ‖z‖ ^ k := by
    rw [coeff_regularizedGaussHGFunSeries, add_comm (1 : ℂ) k, Gamma_nat_eq_factorial,
      ascPochhammer_nat_eq_natCast_ascFactorial, norm_mul, norm_div, norm_mul, norm_mul, norm_pow,
      Complex.norm_natCast, Complex.norm_natCast, sq]
  rw [hk_coeff, div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_mul,
    norm_inv (((M + 1 + k)! : ℕ) : ℂ), Complex.norm_natCast, norm_pow, pow_add ‖z‖ (M + 1) k]
  have ha_le := (hpoch hfa (M + 1 + k)).trans_eq hpM
  have hb_le := (hpoch hfb (M + 1 + k)).trans_eq hpM
  have hinv_fac : ((((M + 1 + k)! : ℕ) : ℝ))⁻¹ ≤ ((k ! : ℝ))⁻¹ :=
    inv_anti₀ (mod_cast Nat.factorial_pos k) (mod_cast Nat.factorial_le (Nat.le_add_left k (M + 1)))
  calc ‖(ascPochhammer ℂ (M + 1 + k)).eval (fa w)‖ *
          ‖(ascPochhammer ℂ (M + 1 + k)).eval (fb w)‖ *
          (((((M + 1 + k)! : ℕ) : ℝ))⁻¹ * ‖(Gamma (fc w + ↑(M + 1 + k)))⁻¹‖) *
          (‖z‖ ^ (M + 1) * ‖z‖ ^ k)
      ≤ (P * ((2 * M + 1).ascFactorial k : ℝ)) * (P * ((2 * M + 1).ascFactorial k : ℝ)) *
          (((k ! : ℝ))⁻¹ * (CΓ / k !)) * (‖z‖ ^ (M + 1) * ‖z‖ ^ k) := by gcongr
    _ = CΓ * P ^ 2 * ‖z‖ ^ (M + 1) *
          (((2 * M + 1).ascFactorial k : ℝ) ^ 2 / (k ! * k !) * ‖z‖ ^ k) := by ring

private theorem exists_summable_bound_regularizedGaussHGFun_comp {fa fb fc : ℂ → ℂ}
    (ha : Differentiable ℂ fa) (hb : Differentiable ℂ fb) (hc : Differentiable ℂ fc)
    {z : ℂ} (hz : ‖z‖ < 1) (w₀ : ℂ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ w ∈ Metric.ball w₀ 1,
      ‖(ascPochhammer ℂ n).eval (fa w) * (ascPochhammer ℂ n).eval (fb w) /
        (n ! * Gamma (fc w + n)) * z ^ n‖ ≤ u n := by
  let K : Set ℂ := Metric.closedBall w₀ 1
  have hK : IsCompact K := isCompact_closedBall w₀ 1
  obtain ⟨Ca, hCa⟩ := hK.exists_bound_of_continuousOn ha.continuous.continuousOn
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn hb.continuous.continuousOn
  obtain ⟨Cc, hCc⟩ := hK.exists_bound_of_continuousOn hc.continuous.continuousOn
  obtain ⟨M, hM⟩ := exists_nat_gt (max (max Ca Cb) Cc + 1)
  have hinv (c₀ : ℂ) : Differentiable ℂ fun w => (Gamma (fc w + c₀))⁻¹ := by
    convert differentiable_one_div_Gamma.comp (hc.add (differentiable_const c₀)) using 1
    rfl
  obtain ⟨CΓ, hCΓ⟩ := hK.exists_bound_of_continuousOn (hinv (M + 1 : ℕ)).continuous.continuousOn
  have hfin (n : ℕ) : ∃ B : ℝ, ∀ w ∈ K,
      ‖(ascPochhammer ℂ n).eval (fa w) * (ascPochhammer ℂ n).eval (fb w) /
        (n ! * Gamma (fc w + n)) * z ^ n‖ ≤ B := by
    refine hK.exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    simp only [div_eq_mul_inv, mul_inv]
    exact ((((ascPochhammer ℂ n).differentiable.comp ha).mul
      ((ascPochhammer ℂ n).differentiable.comp hb)).mul
        ((differentiable_const _).mul (hinv n))).mul (differentiable_const _) |>.continuous
  choose Bf hBf using hfin
  let C : ℝ := CΓ * (M.ascFactorial (M + 1) : ℝ) ^ 2 * ‖z‖ ^ (M + 1)
  let u : ℕ → ℝ := fun n => if n < M + 1 then Bf n else
    C * ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff
      (n - (M + 1)) * z ^ (n - (M + 1))‖
  refine ⟨u, ?_, fun n w hw => ?_⟩
  · rw [← summable_nat_add_iff (M + 1)]
    refine ((summable_coeff_regularizedGaussHGFunSeries_mul_pow
      ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1 hz).norm.mul_left C).congr fun k => ?_
    dsimp only [u]
    split_ifs with h
    · omega
    · rw [Nat.add_sub_cancel]
  · have hwK : w ∈ K := Metric.ball_subset_closedBall hw
    dsimp only [u]
    split_ifs with hlt
    · exact hBf n w hwK
    · obtain ⟨k, rfl⟩ : ∃ k, n = M + 1 + k :=
        ⟨n - (M + 1), (Nat.add_sub_of_le (not_lt.mp hlt)).symm⟩
      rw [Nat.add_sub_cancel_left]
      refine norm_regularizedGaussHGFun_term_add_le
        ((hCa w hwK).trans (by linarith [le_max_left Ca Cb, le_max_left (max Ca Cb) Cc]))
        ((hCb w hwK).trans (by linarith [le_max_right Ca Cb, le_max_left (max Ca Cb) Cc])) ?_
        (hCΓ w hwK)
      have h1 : ‖fc w‖ ≤ M - 1 := by linarith [hCc w hwK, le_max_right (max Ca Cb) Cc]
      have h2 := neg_le_of_abs_le ((Complex.abs_re_le_norm (fc w)).trans h1)
      simp only [add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]
      linarith

/-- For fixed `z` in the open unit disk, `w ↦ regularizedGaussHGFun (fa w) (fb w) (fc w) z` is
entire whenever `fa`, `fb`, `fc` are entire. -/
theorem _root_.Differentiable.regularizedGaussHGFun {fa fb fc : ℂ → ℂ}
    (ha : Differentiable ℂ fa) (hb : Differentiable ℂ fb) (hc : Differentiable ℂ fc)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) z := by
  intro w₀
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound_regularizedGaussHGFun_comp ha hb hc hz w₀
  have hfun : (fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) z) =
      fun w => ∑' n : ℕ, (ascPochhammer ℂ n).eval (fa w) * (ascPochhammer ℂ n).eval (fb w) /
        (n ! * Gamma (fc w + n)) * z ^ n := by
    ext w
    simp [regularizedGaussHGFun_eq_tsum_coeff_mul_pow, coeff_regularizedGaussHGFunSeries]
  rw [hfun]
  refine (differentiableOn_tsum_of_summable_norm hu (fun n => ?_) Metric.isOpen_ball
    hbound).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
  refine Differentiable.differentiableOn ?_
  simp only [div_eq_mul_inv, mul_inv]
  have hinvΓ : Differentiable ℂ fun w => (Gamma (fc w + n))⁻¹ := by
    convert differentiable_one_div_Gamma.comp (hc.add (differentiable_const (n : ℂ))) using 1
    rfl
  exact ((((ascPochhammer ℂ n).differentiable.comp ha).mul
    ((ascPochhammer ℂ n).differentiable.comp hb)).mul
      ((differentiable_const _).mul hinvΓ)).mul (differentiable_const _)

end Gaussian

end Complex
