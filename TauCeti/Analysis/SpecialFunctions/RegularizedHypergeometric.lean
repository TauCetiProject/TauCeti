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
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.UniformLimit

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

private theorem regularizedGaussHGFunSeries_apply_eq (a b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFunSeries a b c n (fun _ => z) =
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / (n ! * Gamma (c + n))) *
        z ^ n := by
  have hc := coeff_regularizedGaussHGFunSeries (a := a) (b := b) (c := c) (n := n)
  simp only [regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hc ⊢
  rw [← hc]; simp [FormalMultilinearSeries.coeff_ofScalars, mul_comm]

/-- On the open unit disk `‖z‖ < 1`, the Gaussian hypergeometric power series converges to
`regularizedGaussHGFun a b c z` for all complex parameters `a`, `b`, `c`. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / (n ! * Gamma (c + n))) * z ^ n)
      (regularizedGaussHGFun a b c z) := by
  have hm := (ENNReal.ofReal_lt_one.2 hz).trans_le (radius_regularizedGaussHGFunSeries_ge_one a b c)
  simpa only [regularizedGaussHGFun, regularizedGaussHGFunSeries_apply_eq] using
    (regularizedGaussHGFunSeries a b c).hasSum (by simpa [edist_zero_right, ofReal_norm] using hm)

/-- On the open unit disk `‖z‖ < 1`, the Gaussian hypergeometric power series converges absolutely
for all complex parameters `a`, `b`, `c`. -/
theorem summable_norm_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ‖((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / (n ! * Gamma (c + n))) *
        z ^ n‖ := by
  have hm := (ENNReal.ofReal_lt_one.2 hz).trans_le (radius_regularizedGaussHGFunSeries_ge_one a b c)
  simpa only [regularizedGaussHGFunSeries_apply_eq] using
    (regularizedGaussHGFunSeries a b c).summable_norm_apply
      (by simpa [edist_zero_right, ofReal_norm] using hm)

private theorem norm_regularizedGaussTerm_shift_le {M N₀ : ℕ} {C r : ℝ}
    {a b c z : ℂ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : 1 ≤ (c + N₀).re)
    (hcC : ‖(Gamma (c + N₀))⁻¹‖ ≤ C) (hz : ‖z‖ ≤ r) (m : ℕ) :
    ‖((ascPochhammer ℂ (N₀ + m)).eval a * (ascPochhammer ℂ (N₀ + m)).eval b /
        ((N₀ + m)! * Gamma (c + ((N₀ + m : ℕ) : ℂ)))) * z ^ (N₀ + m)‖ ≤
      C * (((M + N₀ + m : ℕ) : ℝ) ^ (2 * (M + N₀)) * r ^ (N₀ + m)) := by
  generalize hK : M + N₀ = K
  have hab {w : ℂ} (hw : ‖w‖ ≤ M) :
      ‖(ascPochhammer ℂ (N₀ + m)).eval w‖ ≤ (m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K := by
    have hnat : (m + K)! ≤ m ! * (m + K) ^ K := by
      rw [← Nat.factorial_mul_ascFactorial m K]
      exact Nat.mul_le_mul_left (m !) (Nat.ascFactorial_le_pow_add m K)
    refine (norm_ascPochhammer_eval_le_factorial hw (N₀ + m)).trans ?_
    rw [show M + (N₀ + m) = m + K by omega]
    simpa [add_comm m K] using (Nat.cast_le (α := ℝ)).2 hnat
  have hNm : (m ! : ℝ) ≤ ((N₀ + m)! : ℝ) :=
    (Nat.cast_le (α := ℝ)).2 (Nat.factorial_le (Nat.le_add_left m N₀))
  have hm_pos : (0 : ℝ) < m ! := Nat.cast_pos.2 m.factorial_pos
  have hC : 0 ≤ C := (norm_nonneg _).trans hcC
  have hΓ : ‖Gamma (c + ((N₀ + m : ℕ) : ℂ))‖⁻¹ ≤ C / (m ! : ℝ) := by
    rw [← norm_inv]
    refine le_trans ?_ (div_le_div_of_nonneg_right hcC (by positivity))
    simpa only [Nat.cast_add, add_assoc] using norm_inv_Gamma_add_natCast_le hc m
  have hNm_inv : (((N₀ + m)! : ℝ))⁻¹ ≤ (m ! : ℝ)⁻¹ := inv_anti₀ hm_pos hNm
  have ha' := hab ha
  have hb' := hab hb
  simp only [div_eq_mul_inv, mul_inv, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc ‖(ascPochhammer ℂ (N₀ + m)).eval a‖ * ‖(ascPochhammer ℂ (N₀ + m)).eval b‖ *
        ((((N₀ + m)! : ℝ))⁻¹ * ‖Gamma (c + ((N₀ + m : ℕ) : ℂ))‖⁻¹) * ‖z‖ ^ (N₀ + m)
      ≤ ((m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K) * ((m ! : ℝ) * ((K + m : ℕ) : ℝ) ^ K) *
        ((m ! : ℝ)⁻¹ * (C / (m ! : ℝ))) * r ^ (N₀ + m) := by gcongr
    _ = C * (((K + m : ℕ) : ℝ) ^ (2 * K) * r ^ (N₀ + m)) := by
        rw [two_mul, pow_add]; field_simp [hm_pos.ne']; ring

private theorem summable_gauss_majorant (C : ℝ) (K N₀ : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun m : ℕ => C * (((K + m : ℕ) : ℝ) ^ (2 * K) * r ^ (N₀ + m)) := by
  generalize 2 * K = L
  have hpow : Summable fun m : ℕ => ((m + K : ℕ) : ℝ) ^ L * r ^ (m + K) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ L * r ^ n) K).2
      (summable_pow_mul_geometric_of_norm_lt_one L (by rwa [Real.norm_of_nonneg hr0.le]))
  refine (hpow.mul_left (C * (r ^ N₀ / r ^ K))).congr fun m => ?_
  rw [add_comm m K, pow_add (a := r) K m, pow_add (a := r) N₀ m]
  field_simp [pow_ne_zero K hr0.ne']

private def regularizedGaussTerm (n : ℕ) (p : ℂ × ℂ × ℂ × ℂ) : ℂ :=
  ((ascPochhammer ℂ n).eval p.1 * (ascPochhammer ℂ n).eval p.2.1 /
    (n ! * Gamma (p.2.2.1 + n))) * p.2.2.2 ^ n

private theorem differentiable_regularizedGaussTerm (n : ℕ) :
    Differentiable ℂ (regularizedGaussTerm n) := by
  have h2 : Differentiable ℂ (fun p : ℂ × ℂ × ℂ × ℂ => (Gamma (p.2.2.1 + n))⁻¹) := fun p =>
    DifferentiableAt.comp (g := fun s => (Gamma s)⁻¹) p (differentiable_one_div_Gamma _)
      ((by fun_prop : Differentiable ℂ fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1 + n) p)
  have heq : regularizedGaussTerm n = fun p => (ascPochhammer ℂ n).eval p.1 *
      (ascPochhammer ℂ n).eval p.2.1 * ((n ! : ℂ)⁻¹ * (Gamma (p.2.2.1 + n))⁻¹) * p.2.2.2 ^ n := by
    ext p; simp only [regularizedGaussTerm, div_eq_mul_inv, mul_inv]
  rw [heq]
  exact (((((ascPochhammer ℂ n).differentiable.comp differentiable_fst).mul
    ((ascPochhammer ℂ n).differentiable.comp (differentiable_fst.comp differentiable_snd))).mul
    (h2.const_mul _)).mul
    ((differentiable_snd.comp (differentiable_snd.comp differentiable_snd)).pow n))

private theorem norm_regularizedGaussTerm_shift_le_on_box {p₀ p : ℂ × ℂ × ℂ × ℂ} {M N₀ : ℕ}
    {C r : ℝ} (hM0 : ⌈‖p₀.1‖ + 1⌉₊ ≤ M) (hM1 : ⌈‖p₀.2.1‖ + 1⌉₊ ≤ M)
    (hN₀ : ⌈-p₀.2.2.1.re⌉₊ + 2 ≤ N₀) (hp0 : p.1 ∈ Metric.ball p₀.1 1)
    (hp1 : p.2.1 ∈ Metric.ball p₀.2.1 1) (hp2 : p.2.2.1 ∈ Metric.ball p₀.2.2.1 1)
    (hp3 : p.2.2.2 ∈ Metric.ball 0 r) (hcC : ‖(Gamma (p.2.2.1 + N₀))⁻¹‖ ≤ C) (m : ℕ) :
    ‖regularizedGaussTerm (N₀ + m) p‖ ≤
      C * (((M + N₀ + m : ℕ) : ℝ) ^ (2 * (M + N₀)) * r ^ (N₀ + m)) := by
  have hnorm_le {w₀ w : ℂ} (hw : w ∈ Metric.ball w₀ 1) (hMw : ⌈‖w₀‖ + 1⌉₊ ≤ M) :
      ‖w‖ ≤ M := by
    have hlt : ‖w‖ < ‖w₀‖ + 1 := by
      linarith [norm_le_norm_sub_add w w₀, mem_ball_iff_norm.1 hw]
    exact hlt.le.trans ((Nat.le_ceil _).trans (by exact_mod_cast hMw))
  have hc : 1 ≤ (p.2.2.1 + N₀).re := by
    have h := (abs_re_le_norm (p.2.2.1 - p₀.2.2.1)).trans (mem_ball_iff_norm.1 hp2).le
    have hN' : (⌈-p₀.2.2.1.re⌉₊ : ℝ) + 2 ≤ N₀ := by exact_mod_cast hN₀
    simp only [add_re, natCast_re]
    linarith [(abs_le.1 h).1, sub_re p.2.2.1 p₀.2.2.1, Nat.le_ceil (-p₀.2.2.1.re)]
  exact norm_regularizedGaussTerm_shift_le (hnorm_le hp0 hM0) (hnorm_le hp1 hM1) hc hcC
    (mem_ball_zero_iff.1 hp3).le m

/-- **Joint holomorphy of the regularized Gauss hypergeometric function.** On `{p | ‖z‖ < 1}`,
`regularizedGaussHGFun a b c z` is jointly analytic in all four complex variables `(a, b, c, z)`,
with no pole-avoidance restriction on `c`. -/
theorem analyticOnNhd_regularizedGaussHGFun :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => regularizedGaussHGFun p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | ‖p.2.2.2‖ < 1} := by
  intro p₀ hp₀
  simp only [mem_ofPred_eq] at hp₀
  let M : ℕ := max ⌈‖p₀.1‖ + 1⌉₊ ⌈‖p₀.2.1‖ + 1⌉₊
  let N₀ : ℕ := ⌈-p₀.2.2.1.re⌉₊ + 2
  let r : ℝ := (‖p₀.2.2.2‖ + 1) / 2
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall p₀.2.2.1 1).exists_bound_of_continuousOn
    (f := fun c : ℂ => (Gamma (c + N₀))⁻¹)
    ((differentiable_one_div_Gamma.comp
      (differentiable_id.add_const (N₀ : ℂ))).continuous.continuousOn)
  let C : ℝ := max C₀ 0
  let U : Set (ℂ × ℂ × ℂ × ℂ) :=
    Metric.ball p₀.1 1 ×ˢ (Metric.ball p₀.2.1 1 ×ˢ (Metric.ball p₀.2.2.1 1 ×ˢ Metric.ball 0 r))
  have hU_open : IsOpen U :=
    Metric.isOpen_ball.prod (Metric.isOpen_ball.prod (Metric.isOpen_ball.prod Metric.isOpen_ball))
  have hp₀U : p₀ ∈ U := ⟨Metric.mem_ball_self zero_lt_one, Metric.mem_ball_self zero_lt_one,
    Metric.mem_ball_self zero_lt_one, by simp [Metric.mem_ball, r]; linarith⟩
  have htail_an : AnalyticAt ℂ (fun p => ∑' m : ℕ, regularizedGaussTerm (N₀ + m) p) p₀ :=
    ((tendstoUniformlyOn_tsum (s := U)
        (summable_gauss_majorant C (M + N₀) N₀ hr0 hr1) fun m p hp =>
        norm_regularizedGaussTerm_shift_le_on_box (le_max_left _ _) (le_max_right _ _) le_rfl
          hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
          ((hC₀ p.2.2.1 (Metric.ball_subset_closedBall hp.2.2.1)).trans (le_max_left _ _)) m
      ).differentiableOn
      (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun m _ =>
        (differentiable_regularizedGaussTerm (N₀ + m)).differentiableOn) hU_open
    ).analyticAt_of_finiteDimensional (hU_open.mem_nhds hp₀U)
  have hpre_an : AnalyticAt ℂ (fun p => ∑ n ∈ Finset.range N₀, regularizedGaussTerm n p) p₀ :=
    (Differentiable.fun_sum fun n _ =>
      differentiable_regularizedGaussTerm n).differentiableOn.analyticAt_of_finiteDimensional
      univ_mem
  refine (hpre_an.add htail_an).congr ?_
  filter_upwards [hU_open.mem_nhds hp₀U] with p hp
  have hsum : HasSum (fun n => regularizedGaussTerm n p)
      (regularizedGaussHGFun p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    hasSum_regularizedGaussHGFun p.1 p.2.1 p.2.2.1 ((mem_ball_zero_iff.1 hp.2.2.2).trans hr1)
  rw [Pi.add_apply, ← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add N₀]
  exact congrArg (_ + ·) (tsum_congr fun m => by rw [add_comm _ m])

end Complex
