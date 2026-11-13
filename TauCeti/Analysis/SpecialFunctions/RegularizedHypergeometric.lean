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
import Mathlib.RingTheory.Binomial

/-!
# The regularized hypergeometric function `₀F₁`

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement and develops the
function `₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))`, the case `a = 0`, `b = {b}`, which underlies the
Bessel and Airy functions.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For every pair of complex parameters `a`, `b`, the product `₀F₁(; a; z) ₀F₁(; b; z)` expands as
an everywhere convergent power series with coefficients
`(a + b + n - 1)_n / (n! Γ(a + n) Γ(b + n))`, valid without pole exclusions on `a` or `b`.
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
* `Complex.sum_regularizedHGFunCoeff_zero_singleton_mul` and
  `Complex.hasSum_regularizedHGFun_zero_singleton_mul` — the Cauchy product series of
  `₀F₁(; a; z) ₀F₁(; b; z)`, absolutely convergent by
  `Complex.summable_norm_regularizedHGFun_zero_singleton_mul`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments, with Cauchy product `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re_mul`.
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

private theorem descPochhammer_int_smeval_eq_eval (z : ℂ) (m : ℕ) :
    (descPochhammer ℤ m).smeval z = (descPochhammer ℂ m).eval z := by
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, ← Polynomial.eval_map, descPochhammer_map]

/-- The finite convolution of the coefficients of `₀F₁(; a; z)` and `₀F₁(; b; z)`, valid at every
pair of complex parameters `a`, `b`, including poles of `Γ`. -/
theorem sum_regularizedHGFunCoeff_zero_singleton_mul (a b : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k) =
    (ascPochhammer ℂ n).eval (a + b + n - 1) / (n ! * Gamma (a + n) * Gamma (b + n)) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k) =
        ((n.choose k : ℂ) *
          ((descPochhammer ℤ k).smeval (b + n - 1) *
            (descPochhammer ℤ (n - k)).smeval (a + n - 1))) /
          (n ! * Gamma (a + n) * Gamma (b + n)) := by
    intro k hk_mem
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    have ha : (Gamma (a + k))⁻¹ =
        (descPochhammer ℤ (n - k)).smeval (a + n - 1) * (Gamma (a + n))⁻¹ := by
      have han : a + k + ((n - k : ℕ) : ℂ) = a + n := by rw [Nat.cast_sub hk]; ring
      have hsub : a + n - 1 - ((n - k : ℕ) : ℂ) + 1 = a + k := by rw [Nat.cast_sub hk]; ring
      rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (a + k) (n - k), han, ← hsub,
        ← descPochhammer_eval_eq_ascPochhammer, descPochhammer_int_smeval_eq_eval]
    have hb : (Gamma (b + (n - k : ℕ)))⁻¹ =
        (descPochhammer ℤ k).smeval (b + n - 1) * (Gamma (b + n))⁻¹ := by
      have hbn : b + ((n - k : ℕ) : ℂ) + k = b + n := by rw [Nat.cast_sub hk]; ring
      have hsub : b + n - 1 - k + 1 = b + ((n - k : ℕ) : ℂ) := by rw [Nat.cast_sub hk]; ring
      rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (b + (n - k : ℕ)) k, hbn, ← hsub,
        ← descPochhammer_eval_eq_ascPochhammer, descPochhammer_int_smeval_eq_eval]
    have hfac : (k ! : ℂ)⁻¹ * ((n - k)! : ℂ)⁻¹ = (n.choose k : ℂ) * (n ! : ℂ)⁻¹ := by
      have hchoose : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
      have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
      have hnk0 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
      have hn0 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
      field_simp
      linear_combination -hchoose
    rw [regularizedHGFunCoeff_zero_singleton, regularizedHGFunCoeff_zero_singleton,
      mul_inv, mul_inv, mul_mul_mul_comm, hfac, ha, hb]
    ring
  have harg : b + n - 1 + (a + n - 1) - n + 1 = a + b + n - 1 := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l =>
      (n.choose k : ℂ) *
        ((descPochhammer ℤ k).smeval (b + n - 1) * (descPochhammer ℤ l).smeval (a + n - 1)),
    ← Ring.descPochhammer_smeval_add n (Commute.all _ _), descPochhammer_int_smeval_eq_eval,
    descPochhammer_eval_eq_ascPochhammer, harg]

private theorem sum_range_regularizedHGFun_zero_singleton_mul (a b z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (regularizedHGFunCoeff 0 {a} k * z ^ k) *
        (regularizedHGFunCoeff 0 {b} (n - k) * z ^ (n - k)) =
    (ascPochhammer ℂ n).eval (a + b + n - 1) / (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n := by
  have hpow : ∀ k ∈ Finset.range (n + 1),
      (regularizedHGFunCoeff 0 {a} k * z ^ k) *
        (regularizedHGFunCoeff 0 {b} (n - k) * z ^ (n - k)) =
      (regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k)) * z ^ n := by
    intro k hk_mem
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le hk]
  rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul, sum_regularizedHGFunCoeff_zero_singleton_mul]

/-- The Cauchy product series of `₀F₁(; a; z) ₀F₁(; b; z)` converges everywhere, without pole
exclusions on `a` or `b`. -/
theorem hasSum_regularizedHGFun_zero_singleton_mul (a b z : ℂ) :
    HasSum
      (fun n : ℕ =>
        (ascPochhammer ℂ n).eval (a + b + n - 1) /
          (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n)
      (regularizedHGFun 0 {a} z * regularizedHGFun 0 {b} z) := by
  have ha := hasSum_regularizedHGFun (a := 0) (b := {a}) (by simp) z
  have hb := hasSum_regularizedHGFun (a := 0) (b := {b}) (by simp) z
  have h := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_regularizedHGFun (a := 0) (b := {a}) (by simp) z)
    (summable_norm_regularizedHGFun (a := 0) (b := {b}) (by simp) z)
  rw [ha.tsum_eq, hb.tsum_eq] at h
  simpa only [sum_range_regularizedHGFun_zero_singleton_mul] using h

/-- The Cauchy product series of `₀F₁(; a; z) ₀F₁(; b; z)` converges absolutely everywhere. -/
theorem summable_norm_regularizedHGFun_zero_singleton_mul (a b z : ℂ) :
    Summable fun n : ℕ =>
      ‖(ascPochhammer ℂ n).eval (a + b + n - 1) /
        (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n‖ := by
  simpa only [sum_range_regularizedHGFun_zero_singleton_mul] using
    summable_norm_sum_mul_range_of_summable_norm
      (summable_norm_regularizedHGFun (a := 0) (b := {a}) (by simp) z)
      (summable_norm_regularizedHGFun (a := 0) (b := {b}) (by simp) z)

/-- At real parameters and a real argument, the product of two `₀F₁` functions is given by the real
Cauchy product series. -/
theorem hasSum_regularizedHGFun_zero_singleton_ofReal_re_mul (a b y : ℝ) :
    HasSum
      (fun n : ℕ =>
        (ascPochhammer ℝ n).eval (a + b + n - 1) /
          (n ! * Real.Gamma (a + n) * Real.Gamma (b + n)) * y ^ n)
      ((regularizedHGFun 0 {(a : ℂ)} y).re * (regularizedHGFun 0 {(b : ℂ)} y).re) := by
  have h := hasSum_re (hasSum_regularizedHGFun_zero_singleton_mul a b y)
  have hre : (regularizedHGFun 0 {(a : ℂ)} y * regularizedHGFun 0 {(b : ℂ)} y).re =
      (regularizedHGFun 0 {(a : ℂ)} y).re * (regularizedHGFun 0 {(b : ℂ)} y).re := by
    simp [mul_re]
  rw [hre] at h
  refine h.congr_fun fun n => ?_
  have heval : (ascPochhammer ℂ n).eval ((a + b + n - 1 : ℝ) : ℂ) =
      (((ascPochhammer ℝ n).eval (a + b + n - 1) : ℝ) : ℂ) := by
    simpa using Polynomial.eval_map_apply ofRealHom (a + b + n - 1) (p := ascPochhammer ℝ n)
  have hc : (a : ℂ) + b + n - 1 = ((a + b + n - 1 : ℝ) : ℂ) := by push_cast; ring
  have ha : (a : ℂ) + n = ((a + n : ℝ) : ℂ) := by push_cast; ring
  have hb : (b : ℂ) + n = ((b + n : ℝ) : ℂ) := by push_cast; ring
  rw [hc, ha, hb, heval, Gamma_ofReal, Gamma_ofReal]
  norm_cast

end Complex
