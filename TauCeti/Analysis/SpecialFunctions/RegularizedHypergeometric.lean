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

/-!
# Regularized hypergeometric functions

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement, develops the function
`₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))` (the case `a = 0`, `b = {b}`, which underlies the Bessel
functions), and establishes the foundational series and terminating-polynomial API for the
regularized Gaussian hypergeometric function `Complex.regularizedGaussHGFun a b c z`.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
Because `1 / Γ` vanishes at the poles of `Γ`, none of these statements needs a hypothesis on `b`.

In the `p = q + 1` case (`a.card = b.card + 1`), the power series of `regularizedHGFun a b z`
converges absolutely to it on the open unit disk `‖z‖ < 1`, and when a nonpositive integer `-n`
belongs to `a` the series terminates after `n + 1` terms everywhere. Specializing to `{a, b}` and
`{c}` gives the unit-disk series, analyticity, terminating-polynomial formulas (DLMF 15.2.4), and
contiguous parameter-shift relations (DLMF 15.5.15 and 15.5.16) for
`Complex.regularizedGaussHGFun a b c z` at all complex parameters, including nonpositive integer
values of `c`.

## Main results

* `Complex.hasSum_regularizedHGFun` — the power series of `regularizedHGFun a b` converges to it
  everywhere when `a.card ≤ b.card`, absolutely by `Complex.summable_norm_regularizedHGFun`.
* `Complex.hasSum_regularizedHGFun_of_card_eq_add_one`,
  `Complex.summable_norm_regularizedHGFun_of_card_eq_add_one` — unit-disk `HasSum` and absolute
  convergence when `a.card = b.card + 1`.
* `Complex.regularizedHGFun_eq_sum_of_neg_natCast_mem` — finite-sum termination when
  `-(n : ℂ) ∈ a`.
* `Complex.hasSum_deriv_regularizedHGFun` — the termwise differentiated series converges to the
  derivative.
* `Complex.regularizedHGFunCoeff_one_singleton` — the coefficients `1 / Γ(b + n)` of the Kummer
  function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments.
* `Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re` — joint continuity in `(b, y)`.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re` — the derivative in `y`.
* `Complex.regularizedGaussHGFun_eq_regularizedHGFun`, `Complex.analyticAt_regularizedGaussHGFun`,
  `Complex.hasSum_regularizedGaussHGFun`, `Complex.summable_norm_regularizedGaussHGFun` — wrapper
  agreement, analyticity, power series, and absolute convergence of `regularizedGaussHGFun a b c z`
  on `‖z‖ < 1`.
* `Complex.regularizedGaussHGFun_neg_natCast_eq_sum`, `Complex.regularizedGaussHGFun_neg_natCast` —
  finite-sum formulas for the terminating polynomials `regularizedGaussHGFun (-n) b c z`
  (DLMF 15.2.4).
* `Complex.regularizedGaussHGFun_eq_sub_mul_add_mul`,
  `Complex.regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul` — contiguous `c`- and
  `b`-shift relations (DLMF 15.5.15 and 15.5.16) on `‖z‖ < 1 ∨ ∃ n : ℕ, a = -n`, specialized to
  `-(n + 1 : ℕ)` in `Complex.regularizedGaussHGFun_neg_natCast_succ_eq_sub` and
  `Complex.regularizedGaussHGFun_neg_natCast_succ_eq_add`.

## References

* NIST Digital Library of Mathematical Functions, §15.2.4, §15.5.15, and §15.5.16.
-/

public section

noncomputable section

open Filter Polynomial Set
open scoped ENNReal Nat Topology

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

/-- When there is one more upper than lower parameter, the regularized hypergeometric series
converges to `regularizedHGFun a b z` on the open unit disk `‖z‖ < 1`. -/
theorem hasSum_regularizedHGFun_of_card_eq_add_one {a b : Multiset ℂ}
    (h : a.card = b.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius := by
    refine Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h) ?_
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    mul_comm] using (regularizedHGFunSeries a b).hasSum hmem

/-- When there is one more upper than lower parameter, the regularized hypergeometric series
converges absolutely on the open unit disk `‖z‖ < 1`. -/
theorem summable_norm_regularizedHGFun_of_card_eq_add_one {a b : Multiset ℂ}
    (h : a.card = b.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ := by
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius := by
    refine Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h) ?_
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    (regularizedHGFunSeries a b).summable_norm_apply hmem

/-- When a nonpositive integer `-n` belongs to the upper parameters `a`, the regularized
hypergeometric series terminates after `n + 1` terms at every `z`. -/
theorem regularizedHGFun_eq_sum_of_neg_natCast_mem {a : Multiset ℂ} (b : Multiset ℂ) (z : ℂ)
    {n : ℕ} (ha : -(n : ℂ) ∈ a) :
    regularizedHGFun a b z =
      ∑ k ∈ Finset.range (n + 1), regularizedHGFunCoeff a b k * z ^ k := by
  have hs : HasSum (fun k => regularizedHGFunCoeff a b k * z ^ k) (regularizedHGFun a b z) := by
    simpa [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      mul_comm] using (regularizedHGFunSeries a b).hasSum (x := z)
        (by simp [radius_regularizedHGFunSeries_eq_top_of_finite ha rfl])
  refine hs.unique (hasSum_sum_of_ne_finset_zero fun k hk => ?_)
  rw [regularizedHGFunCoeff_eq_zero_left a b k n ha
    (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk), zero_mul]

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

/-! ### Power series, polynomials, and shift relations of `regularizedGaussHGFun` -/

/-- `regularizedGaussHGFun a b c` is `regularizedHGFun {a, b} {c}`. -/
theorem regularizedGaussHGFun_eq_regularizedHGFun (a b c z : ℂ) :
    regularizedGaussHGFun a b c z = regularizedHGFun {a, b} {c} z := (rfl)

/-- On the open unit disk `‖z‖ < 1`, `regularizedGaussHGFun a b c` is analytic at `z` for all
complex parameters `a`, `b`, `c`. -/
theorem analyticAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedGaussHGFun a b c) z := by
  rw [funext (regularizedGaussHGFun_eq_regularizedHGFun a b c)]
  exact analyticAt_regularizedHGFun_of_card_eq_add_one rfl hz

private theorem regularizedHGFunCoeff_pair_singleton (a b c : ℂ) (k : ℕ) :
    regularizedHGFunCoeff {a, b} {c} k =
      (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + k)) := by
  simp [regularizedHGFunCoeff]

/-- On the open unit disk, the defining power series of `regularizedGaussHGFun a b c z` converges
to it for all complex parameters `a`, `b`, `c`. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
        (k ! * Gamma (c + k)) * z ^ k)
      (regularizedGaussHGFun a b c z) := by
  simpa only [regularizedGaussHGFun_eq_regularizedHGFun, regularizedHGFunCoeff_pair_singleton] using
    hasSum_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c}) rfl hz

/-- On the open unit disk, the defining power series of `regularizedGaussHGFun a b c z` converges
absolutely for all complex parameters `a`, `b`, `c`. -/
theorem summable_norm_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
        (k ! * Gamma (c + k)) * z ^ k‖ := by
  simpa only [regularizedHGFunCoeff_pair_singleton] using
    summable_norm_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c}) rfl hz

/-- When the first upper parameter is a nonpositive integer `-n`, the regularized Gauss
hypergeometric series terminates after `n + 1` terms. -/
theorem regularizedGaussHGFun_neg_natCast_eq_sum (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-n) b c z =
      ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * z ^ k := by
  simpa only [regularizedGaussHGFun_eq_regularizedHGFun, regularizedHGFunCoeff_pair_singleton] using
    regularizedHGFun_eq_sum_of_neg_natCast_mem {c} z (a := {-(n : ℂ), b}) (by simp)

/-- Binomial-coefficient form of the terminating regularized Gauss hypergeometric polynomial
(DLMF 15.2.4). -/
theorem regularizedGaussHGFun_neg_natCast (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-n) b c z =
      ∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * n.choose k * (ascPochhammer ℂ k).eval b / Gamma (c + k) * z ^ k := by
  rw [regularizedGaussHGFun_neg_natCast_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpoch : (ascPochhammer ℂ k).eval (-(n : ℂ)) = (-1) ^ k * n.choose k * k ! := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [hpoch]
  field_simp

/-- With first upper parameter `0`, `regularizedGaussHGFun 0 b c z` reduces to `(Gamma c)⁻¹` at
every complex argument `z`. -/
@[simp]
theorem regularizedGaussHGFun_zero_left (b c z : ℂ) :
    regularizedGaussHGFun 0 b c z = (Gamma c)⁻¹ := by
  simpa [div_eq_mul_inv] using regularizedGaussHGFun_neg_natCast b c z 0

/-- With second upper parameter `0`, `regularizedGaussHGFun a 0 c z` reduces to `(Gamma c)⁻¹` at
every complex argument `z`. -/
@[simp]
theorem regularizedGaussHGFun_zero_right (a c z : ℂ) :
    regularizedGaussHGFun a 0 c z = (Gamma c)⁻¹ := by
  rw [funext_iff.mp (regularizedGaussHGFun_symm a 0 c) z, regularizedGaussHGFun_zero_left]

/-- At zero argument, `regularizedGaussHGFun a b c 0` equals `(Gamma c)⁻¹`. -/
@[simp]
theorem regularizedGaussHGFun_zero (a b c : ℂ) :
    regularizedGaussHGFun a b c 0 = (Gamma c)⁻¹ := by
  simp [regularizedGaussHGFun_eq_regularizedHGFun, regularizedHGFunCoeff]

private theorem hasSum_regularizedGaussHGFun_of_or (b c : ℂ) {a z : ℂ}
    (hz : ‖z‖ < 1 ∨ ∃ n : ℕ, a = -n) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
        (k ! * Gamma (c + k)) * z ^ k)
      (regularizedGaussHGFun a b c z) := by
  rcases hz with hz | ⟨n, rfl⟩
  · exact hasSum_regularizedGaussHGFun a b c hz
  · rw [regularizedGaussHGFun_neg_natCast_eq_sum]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    have hnk : n < k := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
    simp [ascPochhammer_eval_neg_natCast_of_lt hnk]

private theorem shift_add_one_or {a z : ℂ} (ha : a ≠ 0) (hz : ‖z‖ < 1 ∨ ∃ n : ℕ, a = -n) :
    ‖z‖ < 1 ∨ ∃ m : ℕ, a + 1 = -m :=
  hz.imp_right fun ⟨n, hn⟩ => by
    rcases n with _ | m
    · exact False.elim (by simp [hn] at ha)
    · exact ⟨m, by rw [hn]; push_cast; ring⟩

/-- Contiguous `c`-shift relation for `regularizedGaussHGFun` (DLMF 15.5.15), valid on the open
unit disk `‖z‖ < 1` and at every `z` when `a` is a nonpositive integer (including nonpositive
integer values of `c`). -/
theorem regularizedGaussHGFun_eq_sub_mul_add_mul (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1 ∨ ∃ n : ℕ, a = -n) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa [regularizedHGFunCoeff] using
      (mul_regularizedHGFunCoeff_of_mem_right 0 0 (Multiset.mem_singleton_self (c + 1))).symm
  · refine (hasSum_regularizedGaussHGFun_of_or b c hz).unique
      ((((hasSum_regularizedGaussHGFun_of_or b (c + 1) hz).mul_left (c - a)).add
        ((hasSum_regularizedGaussHGFun_of_or b (c + 1) (shift_add_one_or ha hz)).mul_left a))
          |>.congr_fun fun k => ?_)
    have hc := mul_regularizedHGFunCoeff_of_mem_right {a, b} k
      (Multiset.mem_singleton_self (c + 1))
    simp only [Multiset.erase_singleton, Multiset.cons_zero, add_sub_cancel_right,
      Multiset.insert_eq_cons, regularizedHGFunCoeff, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton] at hc
    have hpoch := ascPochhammer_eval_succ k a
    symm
    calc (c - a) * ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + 1 + k)) * z ^ k) +
          a * ((ascPochhammer ℂ k).eval (a + 1) * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + 1 + k)) * z ^ k)
        = ((c - a) * (ascPochhammer ℂ k).eval a + (a * (ascPochhammer ℂ k).eval (a + 1))) *
            (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + 1 + k)) * z ^ k := by ring
      _ = (c + k) * ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + 1 + k))) * z ^ k := by rw [hpoch]; ring
      _ = (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + k)) * z ^ k := by rw [hc]

/-- Contiguous `b`-shift relation for `regularizedGaussHGFun` (DLMF 15.5.16), valid on the open
unit disk `‖z‖ < 1` and at every `z` when `a` is a nonpositive integer (including nonpositive
integer values of `c`). -/
theorem regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1 ∨ ∃ n : ℕ, a = -n) :
    regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (b + 1) c z -
        a * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hs₀ : HasSum (fun k : ℕ => (ascPochhammer ℂ (k + 1)).eval a *
          (ascPochhammer ℂ (k + 1)).eval b / ((k + 1)! * Gamma (c + (k + 1 : ℕ))) * z ^ (k + 1))
        (regularizedGaussHGFun a b c z - (Gamma c)⁻¹) := by
      simpa [div_eq_mul_inv] using
        (hasSum_nat_add_iff' 1).mpr (hasSum_regularizedGaussHGFun_of_or b c hz)
    have hs₁ : HasSum (fun k : ℕ => (ascPochhammer ℂ (k + 1)).eval a *
          (ascPochhammer ℂ (k + 1)).eval (b + 1) /
            ((k + 1)! * Gamma (c + (k + 1 : ℕ))) * z ^ (k + 1))
        (regularizedGaussHGFun a (b + 1) c z - (Gamma c)⁻¹) := by
      simpa [div_eq_mul_inv] using
        (hasSum_nat_add_iff' 1).mpr (hasSum_regularizedGaussHGFun_of_or (b + 1) c hz)
    have hs₂ :=
      (hasSum_regularizedGaussHGFun_of_or (b + 1) (c + 1) (shift_add_one_or ha hz)).mul_left (a * z)
    have heq := hs₀.unique ((hs₁.sub hs₂).congr_fun fun k => ?_)
    · linear_combination heq
    · have hb : (ascPochhammer ℂ (k + 1)).eval b =
          (ascPochhammer ℂ (k + 1)).eval (b + 1) -
            (k + 1) * (ascPochhammer ℂ k).eval (b + 1) := by
        have h := congr_arg (Polynomial.eval b) (ascPochhammer_succ_comp_X_add_one (S := ℂ) k)
        simp only [nsmul_eq_mul, eval_add, eval_mul, eval_comp, eval_X, eval_one,
          eval_natCast] at h
        push_cast at h
        linear_combination -h
      have ha_poch : (ascPochhammer ℂ (k + 1)).eval a =
          a * (ascPochhammer ℂ k).eval (a + 1) := by
        rw [ascPochhammer_succ_eval, ascPochhammer_eval_succ]
      have hfac : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hc1 : c + ((k + 1 : ℕ) : ℂ) = c + 1 + k := by push_cast; ring
      rw [hb, ha_poch, Nat.factorial_succ, Nat.cast_mul, hc1, pow_succ]
      field_simp
      push_cast
      ring

/-- Recurrence relating `regularizedGaussHGFun (-(n + 1 : ℕ)) b c z` to lower-parameter values at
`c + 1`, valid at all complex parameters including nonpositive integer values of `c`. -/
theorem regularizedGaussHGFun_neg_natCast_succ_eq_sub (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b c z =
      (c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z -
        (n + 1) * regularizedGaussHGFun (-n) b (c + 1) z := by
  have h := regularizedGaussHGFun_eq_sub_mul_add_mul (-((n + 1 : ℕ) : ℂ)) b c (z := z)
    (Or.inr ⟨n + 1, rfl⟩)
  have hshift : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
  rw [hshift] at h
  linear_combination (norm := (push_cast; ring)) h

/-- Recurrence relating `regularizedGaussHGFun (-(n + 1 : ℕ)) b c z` to shifted-parameter values at
`b + 1`, valid at all complex parameters including nonpositive integer values of `c`. -/
theorem regularizedGaussHGFun_neg_natCast_succ_eq_add (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b c z =
      regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z +
        (n + 1) * z * regularizedGaussHGFun (-n) (b + 1) (c + 1) z := by
  have h := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul (-((n + 1 : ℕ) : ℂ)) b c
    (z := z) (Or.inr ⟨n + 1, rfl⟩)
  have hshift : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
  rw [hshift] at h
  linear_combination (norm := (push_cast; ring)) h

end Complex
