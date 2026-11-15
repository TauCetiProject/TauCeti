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
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The regularized hypergeometric functions `₀F₁` and `regularizedGaussHGFun`

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement, develops the function
`₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))` (the case `a = 0`, `b = {b}`, which underlies the Bessel
functions), and provides unit-disk analyticity, power-series `HasSum`, and Taylor addition series
for the regularized Gaussian hypergeometric function `Complex.regularizedGaussHGFun`.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
Because `1 / Γ` vanishes at the poles of `Γ`, none of these statements needs a hypothesis on `b`.

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
* `Complex.analyticAt_regularizedGaussHGFun` — unit-disk analyticity of `regularizedGaussHGFun`.
* `Complex.hasSum_regularizedGaussHGFun` — unit-disk `HasSum` power-series expansion of
  `regularizedGaussHGFun`.
* `Complex.hasSum_regularizedGaussHGFun_add` — Taylor addition series for
  `regularizedGaussHGFun a b c (z + w)` when `‖z‖ + ‖w‖ < 1`.
* `Complex.regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun` — Burchnall and
  Chaundy's finite expansion of `regularizedGaussHGFun a b c z` in powers of `z` and `1 - z` on
  `‖z‖ < 1`.

## References

* J. L. Burchnall and T. W. Chaundy, *Expansions of Appell's double hypergeometric functions*,
  Quart. J. Math. Oxford Ser. **11** (1940), 249–270.
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

/-! ### The regularized Gaussian hypergeometric function on the unit disk -/

/-- The regularized Gaussian hypergeometric function `regularizedGaussHGFun a b c` is analytic at
every point of the open unit disk `‖z‖ < 1`, for all parameters `a, b, c : ℂ`. -/
theorem analyticAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedGaussHGFun a b c) z := by
  have heq : regularizedGaussHGFun a b c = regularizedHGFun {a, b} {c} := by
    ext w
    unfold regularizedGaussHGFun regularizedGaussHGFunSeries regularizedHGFun
    rfl
  rw [heq]
  exact analyticAt_regularizedHGFun_of_card_eq_add_one rfl hz

/-- On the open unit disk `‖z‖ < 1`, the power series of `regularizedGaussHGFun a b c` converges to
`regularizedGaussHGFun a b c z` for all parameters `a, b, c : ℂ`. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (regularizedGaussHGFunSeries a b c).coeff k * z ^ k)
      (regularizedGaussHGFun a b c z) := by
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
    Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
      (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
        ENNReal.ofReal_lt_one] using hz)
  have hs := (regularizedGaussHGFunSeries a b c).hasSum hmem
  simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

/-- **Taylor addition series for `regularizedGaussHGFun`.** Whenever `‖z‖ + ‖w‖ < 1` and
`a, b, c : ℂ` are arbitrary, `regularizedGaussHGFun a b c (z + w)` expands in powers of `w` with
coefficients `((a)_n (b)_n / n!) * regularizedGaussHGFun (a + n) (b + n) (c + n) z`. -/
theorem hasSum_regularizedGaussHGFun_add (a b c : ℂ) {z w : ℂ} (hzw : ‖z‖ + ‖w‖ < 1) :
    HasSum
      (fun n : ℕ => (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n ! * w ^ n *
        regularizedGaussHGFun (a + n) (b + n) (c + n) z)
      (regularizedGaussHGFun a b c (z + w)) := by
  let p := regularizedGaussHGFunSeries a b c
  have hp1 : 1 ≤ p.radius := radius_regularizedGaussHGFunSeries_ge_one a b c
  have hlt : (‖z‖₊ + ‖w‖₊ : ENNReal) < p.radius := by
    refine (?_ : (‖z‖₊ + ‖w‖₊ : ENNReal) < 1).trans_le hp1
    exact_mod_cast hzw
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg w]
  have hz_mem : z ∈ Metric.eball (0 : ℂ) p.radius :=
    mem_eball_zero_iff.mpr ((le_add_right le_rfl).trans_lt hlt)
  have hw_mem : w ∈ Metric.eball (0 : ℂ) (p.changeOrigin z).radius := by
    refine mem_eball_zero_iff.mpr ((?_ : (‖w‖₊ : ENNReal) < p.radius - ‖z‖₊).trans_le
      p.changeOrigin_radius)
    rwa [lt_tsub_iff_right, add_comm]
  have hmain : HasSum (fun n : ℕ => p.changeOrigin z n fun _ => w)
      (regularizedGaussHGFun a b c (z + w)) := by
    rw [regularizedGaussHGFun, ← p.changeOrigin_eval hlt]
    exact (p.changeOrigin z).hasSum hw_mem
  refine hmain.congr_fun fun n => ?_
  have hterm := ContinuousMultilinearMap.hasSum_eval
    ((p.hasFPowerSeriesOnBall_changeOrigin n (zero_lt_one.trans_le hp1)).hasSum hz_mem)
    fun _ => w
  rw [zero_add] at hterm
  refine (((hasSum_regularizedGaussHGFun (a + n) (b + n) (c + n) hz).mul_left
    ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n ! * w ^ n)).congr_fun
    fun k => ?_).unique hterm
  have hp_apply : ((p.changeOriginSeries n k) fun _ => z) (fun _ => w) =
      ((n + k).choose k : ℂ) * (regularizedGaussHGFunSeries a b c).coeff (n + k) *
        (z ^ k * w ^ n) := by
    have h := FormalMultilinearSeries.changeOriginSeries_ofScalars_apply
      (regularizedHGFunCoeff {a, b} {c}) z w n k
    simpa only [p, regularizedGaussHGFunSeries, regularizedHGFunSeries,
      FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul, smul_eq_mul, mul_assoc] using h
  have hc_eq : c + ((n + k : ℕ) : ℂ) = c + n + k := by push_cast; ring
  have hch := (Nat.inv_factorial_mul_inv_factorial (K := ℂ) k n).symm
  rw [Nat.add_comm k n] at hch
  simp only [hp_apply, coeff_regularizedGaussHGFunSeries, TauCeti.ascPochhammer_add_eval n k a,
    TauCeti.ascPochhammer_add_eval n k b, hc_eq, div_eq_mul_inv, mul_inv]
  linear_combination
    (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ k).eval (a + n) *
      (ascPochhammer ℂ n).eval b * (ascPochhammer ℂ k).eval (b + n) *
      (Gamma (c + n + k))⁻¹ * w ^ n * z ^ k * hch

section

open Finset

private theorem regularizedGaussHGFun_step_one (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
        (c - a) * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z := by
  have hs₀ := (hasSum_nat_add_iff' 1).mpr (hasSum_regularizedGaussHGFun a b c hz)
  have hs₁ := (hasSum_nat_add_iff' 1).mpr
    ((hasSum_regularizedGaussHGFun (a + 1) (b + 1) (c + 1) hz).mul_left c)
  have hs₂ := (hasSum_regularizedGaussHGFun (a + 1) (b + 1) (c + 1) hz).mul_left (c * z)
  have hs₃ := (hasSum_regularizedGaussHGFun (a + 1) (b + 1) (c + 2) hz).mul_left
    ((c - a) * (c - b) * z)
  have hcomb := (hs₁.sub hs₂).add hs₃
  have hzero : (regularizedGaussHGFunSeries a b c).coeff 0 * z ^ 0 =
      c * ((regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff 0 * z ^ 0) := by
    simp [coeff_regularizedGaussHGFunSeries, ← one_div_Gamma_eq_self_mul_one_div_Gamma_add_one c]
  have hterm : _ := hs₀.unique (hcomb.congr_fun fun k ↦ ?_)
  · simp only [range_one, sum_singleton, hzero] at hterm
    linear_combination hterm
  · have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + 1 + k)
    have hc1 : c + (k + 1 : ℕ) = c + 1 + k := by push_cast; ring
    have hc2 : c + 1 + (k + 1 : ℕ) = c + 1 + k + 1 := by push_cast; ring
    have hc3 : c + 2 + (k : ℂ) = c + 1 + k + 1 := by ring
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simp only [coeff_regularizedGaussHGFunSeries, hc1, hc2, hc3, div_eq_mul_inv, mul_inv,
      Nat.factorial_succ, Nat.cast_mul, pow_succ, TauCeti.ascPochhammer_succ_left_eval k a,
      TauCeti.ascPochhammer_succ_left_eval k b, ascPochhammer_succ_eval]
    rw [hΓ]
    field_simp; push_cast; ring

private theorem burchnallChaundy_step_mid (a b c z : ℂ) {n k : ℕ} (hkn : k + 1 ≤ n) :
    c * (1 - z) * ((n.choose (k + 1) : ℂ) *
        (ascPochhammer ℂ (k + 1)).eval (c + 1 - (a + 1)) *
        (ascPochhammer ℂ (k + 1)).eval (c + 1 - (b + 1)) *
        (ascPochhammer ℂ (n - (k + 1))).eval (c + 1 + (k + 1 : ℕ)) * z ^ (k + 1) *
        (1 - z) ^ (n - (k + 1)) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 1 + n + (k + 1 : ℕ)) z) +
      (c - a) * (c - b) * z * ((n.choose k : ℂ) *
        (ascPochhammer ℂ k).eval (c + 2 - (a + 1)) *
        (ascPochhammer ℂ k).eval (c + 2 - (b + 1)) *
        (ascPochhammer ℂ (n - k)).eval (c + 2 + k) * z ^ k * (1 - z) ^ (n - k) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 2 + n + k) z) =
    ((n + 1).choose (k + 1) : ℂ) * (ascPochhammer ℂ (k + 1)).eval (c - a) *
      (ascPochhammer ℂ (k + 1)).eval (c - b) *
      (ascPochhammer ℂ (n + 1 - (k + 1))).eval (c + (k + 1 : ℕ)) * z ^ (k + 1) *
      (1 - z) ^ (n + 1 - (k + 1)) *
      regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
        (c + (n + 1 : ℕ) + (k + 1 : ℕ)) z := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hkn
  have hs1 : n - (k + 1) = l := by omega
  have hs2 : n - k = l + 1 := by omega
  have hs3 : n + 1 - (k + 1) = l + 1 := by omega
  have hp4 : (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ) + 1) =
      (ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) * (c + (k + 1 : ℕ) + (l + 1 : ℕ)) := by
    rw [ascPochhammer_succ_eval]; push_cast; ring
  have hchoose_id :
      c * (n.choose (k + 1) : ℂ) * (ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) +
        (n.choose k : ℂ) * (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ) + 1) =
      ((n + 1).choose (k + 1) : ℂ) * (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ)) := by
    have hstep : (n.choose (k + 1) : ℂ) * (k + 1 : ℕ) = (n.choose k : ℂ) * (l + 1 : ℕ) := by
      have h := Nat.choose_succ_right_eq n k; rw [hs2] at h; exact_mod_cast h
    have hpas : ((n + 1).choose (k + 1) : ℂ) = (n.choose k : ℂ) + (n.choose (k + 1) : ℂ) := by
      exact_mod_cast Nat.choose_succ_succ n k
    rw [hp4, TauCeti.ascPochhammer_succ_left_eval l (c + (k + 1 : ℕ)), hpas]
    linear_combination -(ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) * hstep
  have he1 : c + 1 - (a + 1) = c - a := by ring
  have he2 : c + 1 - (b + 1) = c - b := by ring
  have he3 : c + 2 - (a + 1) = c - a + 1 := by ring
  have he4 : c + 2 - (b + 1) = c - b + 1 := by ring
  have he5 : c + 1 + (k + 1 : ℕ) = c + (k + 1 : ℕ) + 1 := by ring
  have he6 : c + 2 + (k : ℂ) = c + (k + 1 : ℕ) + 1 := by push_cast; ring
  have he7 : a + 1 + (n : ℂ) = a + (n + 1 : ℕ) := by push_cast; ring
  have he8 : b + 1 + (n : ℂ) = b + (n + 1 : ℕ) := by push_cast; ring
  have he9 : c + 1 + (n : ℂ) + (k + 1 : ℕ) = c + (n + 1 : ℕ) + (k + 1 : ℕ) := by push_cast; ring
  have he10 : c + 2 + (n : ℂ) + k = c + (n + 1 : ℕ) + (k + 1 : ℕ) := by push_cast; ring
  simp only [hs1, hs2, hs3, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, pow_succ]
  rw [TauCeti.ascPochhammer_succ_left_eval k (c - a),
    TauCeti.ascPochhammer_succ_left_eval k (c - b)]
  linear_combination
    (c - a) * (ascPochhammer ℂ k).eval (c - a + 1) *
      (c - b) * (ascPochhammer ℂ k).eval (c - b + 1) *
      (z ^ k * z) * ((1 - z) ^ l * (1 - z)) *
      regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
        (c + (n + 1 : ℕ) + (k + 1 : ℕ)) z * hchoose_id

private theorem burchnallChaundy_step_bd (a b c z : ℂ) (n : ℕ) :
    c * (1 - z) * ((n.choose 0 : ℂ) * (ascPochhammer ℂ 0).eval (c + 1 - (a + 1)) *
        (ascPochhammer ℂ 0).eval (c + 1 - (b + 1)) *
        (ascPochhammer ℂ (n - 0)).eval (c + 1 + (0 : ℕ)) * z ^ 0 * (1 - z) ^ (n - 0) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 1 + n + (0 : ℕ)) z) +
      (c - a) * (c - b) * z * ((n.choose n : ℂ) * (ascPochhammer ℂ n).eval (c + 2 - (a + 1)) *
        (ascPochhammer ℂ n).eval (c + 2 - (b + 1)) *
        (ascPochhammer ℂ (n - n)).eval (c + 2 + n) * z ^ n * (1 - z) ^ (n - n) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 2 + n + n) z) =
    ((n + 1).choose 0 : ℂ) * (ascPochhammer ℂ 0).eval (c - a) *
        (ascPochhammer ℂ 0).eval (c - b) *
        (ascPochhammer ℂ (n + 1 - 0)).eval (c + (0 : ℕ)) * z ^ 0 * (1 - z) ^ (n + 1 - 0) *
        regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
          (c + (n + 1 : ℕ) + (0 : ℕ)) z +
      ((n + 1).choose (n + 1) : ℂ) * (ascPochhammer ℂ (n + 1)).eval (c - a) *
        (ascPochhammer ℂ (n + 1)).eval (c - b) *
        (ascPochhammer ℂ (n + 1 - (n + 1))).eval (c + (n + 1 : ℕ)) * z ^ (n + 1) *
        (1 - z) ^ (n + 1 - (n + 1)) *
        regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
          (c + (n + 1 : ℕ) + (n + 1 : ℕ)) z := by
  have ha1 : a + 1 + (n : ℂ) = a + (n + 1 : ℕ) := by push_cast; ring
  have hb1 : b + 1 + (n : ℂ) = b + (n + 1 : ℕ) := by push_cast; ring
  have hc1 : c + 1 + (n : ℂ) = c + (n + 1 : ℕ) := by push_cast; ring
  have hc2 : c + 2 + (n : ℂ) + n = c + (n + 1 : ℕ) + (n + 1 : ℕ) := by push_cast; ring
  have hca2 : c + 2 - (a + 1) = c - a + 1 := by ring
  have hcb2 : c + 2 - (b + 1) = c - b + 1 := by ring
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, ascPochhammer_zero,
    Polynomial.eval_one, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, add_zero, pow_zero,
    one_mul, mul_one, pow_succ, ha1, hb1, hc1, hc2, hca2, hcb2]
  rw [TauCeti.ascPochhammer_succ_left_eval n c,
    TauCeti.ascPochhammer_succ_left_eval n (c - a),
    TauCeti.ascPochhammer_succ_left_eval n (c - b)]
  ring

/-- **Finite Burchnall–Chaundy expansion on the open unit disk.** For every `n : ℕ`, `‖z‖ < 1`,
and arbitrary complex parameters `a`, `b`, `c`, `𝐅(a, b; c; z)` expands as a finite binomial sum
in `z ^ s * (1 - z) ^ (n - s) * 𝐅(a + n, b + n; c + n + s; z)` (Burchnall and Chaundy, 1940). -/
theorem regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) (n : ℕ) :
    regularizedGaussHGFun a b c z =
      ∑ s ∈ range (n + 1),
        (n.choose s : ℂ) * (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
          (ascPochhammer ℂ (n - s)).eval (c + s) * z ^ s * (1 - z) ^ (n - s) *
            regularizedGaussHGFun (a + n) (b + n) (c + n + s) z := by
  induction n generalizing a b c with
  | zero => simp
  | succ n ih =>
    have h₁ := congrArg (c * (1 - z) * ·) (ih (a + 1) (b + 1) (c + 1))
    rw [mul_sum, sum_range_succ'] at h₁
    have h₂ := congrArg ((c - a) * (c - b) * z * ·) (ih (a + 1) (b + 1) (c + 2))
    rw [mul_sum, sum_range_succ] at h₂
    rw [regularizedGaussHGFun_step_one a b c hz, h₁, h₂]
    conv_rhs => rw [sum_range_succ, sum_range_succ']
    have hmid := sum_congr (s₁ := range n) rfl fun k hk ↦
      burchnallChaundy_step_mid a b c z (mem_range.mp hk)
    rw [sum_add_distrib] at hmid
    have hbd := burchnallChaundy_step_bd a b c z n
    linear_combination hmid + hbd

end

end Complex
