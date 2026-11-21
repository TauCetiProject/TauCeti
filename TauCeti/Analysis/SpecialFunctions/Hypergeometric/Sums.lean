/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.RingTheory.Binomial

/-!
# Inverse-argument expansions in Gauss hypergeometric polynomials

Given a nonzero base point `z₀ ∈ ℂ`, the Gauss hypergeometric function at `z⁻¹` expands in powers
of `(1 - z / z₀)⁻¹` with terminating hypergeometric polynomial coefficients
`regularizedGaussHGFun (-s) b c z₀⁻¹` (DLMF 15.15.1):
$$\sum_{s=0}^{\infty} \frac{(a)_s}{s!}\,\mathbf{F}(-s, b, c; z_0^{-1})\,(1 - z / z_0)^{-s}
  = (1 - z_0 / z)^a\,\mathbf{F}(a, b, c; z^{-1})$$
for `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` (equivalently, multiplying the series on the left by
`(1 - z₀ / z) ^ (-a)` as printed in DLMF 15.15.1, since `(1 - z₀ / z) ^ (-a)` is the inverse of
`(1 - z₀ / z) ^ a`).

Because `regularizedGaussHGFun (-s) b c z₀⁻¹` is a polynomial of degree at most `s` in `z₀⁻¹` with
coefficients entire in `(b, c)`, its value is well defined at every `z₀ ≠ 0` and every `c ∈ ℂ`,
including when `z₀⁻¹` lies on the branch cut `[1, ∞)` of the general hypergeometric function or `c`
is a nonpositive integer. Meanwhile, the exterior condition `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` keeps
`1 - z₀ / z` in the open right half-plane (so the principal power `(1 - z₀ / z) ^ a` is analytic)
and keeps `z⁻¹` off `[1, ∞)`.

Building on the terminating-polynomial API in
`TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic` and
`Complex.eulerIntegral_neg_natCast` in
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral`, this file proves that the
DLMF 15.15.1 series converges absolutely and defines a holomorphic function throughout
`{z | max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖}` for all complex parameters `a`, `b`, `c`, and establishes the
inverse-argument expansion for:
* `Complex.eulerIntegral` across the full exterior domain `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` when
  `0 < b.re < c.re`;
* `Complex.regularizedGaussHGFun` at all complex parameters `a`, `b`, `c` whenever `1 < ‖z‖` and
  `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` (where `1 < ‖z‖` places `z⁻¹` inside the open unit disk on which
  Mathlib defines `regularizedGaussHGFun` via its power series);
* `ordinaryHypergeometric` (`₂F₁`) away from nonpositive integer values of `c` on the same domain.

## Main statements

* `Complex.hasSum_eulerIntegral_inv`: DLMF 15.15.1 for `eulerIntegral` on
  `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` when `0 < b.re < c.re`.
* `Complex.summable_norm_regularizedGaussHGFun_neg_natCast_mul_inv_pow`,
  `Complex.analyticOnNhd_tsum_regularizedGaussHGFun_neg_natCast_mul_inv_pow`: absolute convergence
  and holomorphy of the DLMF 15.15.1 series on `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖` for all `a`, `b`, `c`.
* `Complex.hasSum_regularizedGaussHGFun_inv`, `Complex.hasSum_ordinaryHypergeometric_inv`:
  DLMF 15.15.1 for `regularizedGaussHGFun` (all `a`, `b`, `c`) and `₂F₁` (`∀ k : ℕ, c ≠ -k`) when
  `1 < ‖z‖` and `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖`.

## References

* NIST Digital Library of Mathematical Functions, §15.2.4 and §15.15.1.
* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. I, McGraw–Hill, 1953, §2.5.2.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Polynomial Set
open scoped ENNReal NNReal Nat Topology Interval ComplexConjugate

namespace Complex

/-! ### DLMF 15.15.1 on the Euler integral range -/

/-- For `t ∈ [0, 1]`, the segment point `z₀ - t` has norm at most `max ‖z₀‖ ‖z₀ - 1‖`. -/
private theorem norm_sub_ofReal_le_max (z₀ : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖z₀ - (t : ℂ)‖ ≤ max ‖z₀‖ ‖z₀ - 1‖ := by
  have hmem : z₀ + t • ((z₀ - 1) - z₀) ∈ Metric.closedBall (0 : ℂ) (max ‖z₀‖ ‖z₀ - 1‖) :=
    (convex_closedBall (0 : ℂ) (max ‖z₀‖ ‖z₀ - 1‖)).add_smul_sub_mem
      (mem_closedBall_zero_iff.mpr (le_max_left _ _))
      (mem_closedBall_zero_iff.mpr (le_max_right _ _)) ht
  have heq : z₀ + t • ((z₀ - 1) - z₀) = z₀ - (t : ℂ) := by
    simp only [real_smul]; ring
  exact mem_closedBall_zero_iff.mp (heq ▸ hmem)

private theorem ne_of_norm_lt_norm_sub {z z₀ : ℂ} (h : ‖z₀‖ < ‖z - z₀‖) : z ≠ z₀ :=
  sub_ne_zero.mp (norm_pos_iff.mp ((norm_nonneg z₀).trans_lt h))

private theorem ne_zero_of_norm_lt_norm_sub {z z₀ : ℂ} (h : ‖z₀‖ < ‖z - z₀‖) : z ≠ 0 := by
  rintro rfl
  exact lt_irrefl ‖z₀‖ (by simpa only [zero_sub, norm_neg] using h)

/-- When `z` is strictly farther from `z₀` than `0` is, `1 - z₀ / z` lies in the open right
half-plane. -/
private theorem one_sub_div_re_pos {z z₀ : ℂ} (h : ‖z₀‖ < ‖z - z₀‖) :
    0 < (1 - z₀ / z).re := by
  have hzz₀_pos : 0 < ‖z - z₀‖ := (norm_nonneg z₀).trans_lt h
  have hzz₀ : z - z₀ ≠ 0 := norm_pos_iff.mp hzz₀_pos
  have hz : z ≠ 0 := ne_zero_of_norm_lt_norm_sub h
  have hinv : (1 - z₀ / z)⁻¹ = 1 + z₀ / (z - z₀) := by field
  rw [← inv_re_pos, hinv]
  exact TauCeti.re_pos_of_norm_sub_one_lt_one <| by
    rwa [add_sub_cancel_left, norm_div, div_lt_one hzz₀_pos]

private theorem inv_one_sub_div_eq {z z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hzz₀ : z ≠ z₀) :
    (1 - z / z₀)⁻¹ = z₀ / (z₀ - z) := by
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem one_sub_inv_one_sub_div_eq {z z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hzz₀ : z ≠ z₀) :
    1 - (1 - z / z₀)⁻¹ = -z / (z₀ - z) := by
  rw [inv_one_sub_div_eq hz₀ hzz₀]
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem one_sub_div_eq_inv_one_sub_inv_one_sub_div {z z₀ : ℂ} (hz : z ≠ 0)
    (hz₀ : z₀ ≠ 0) (hzz₀ : z ≠ z₀) :
    1 - z₀ / z = (1 - (1 - z / z₀)⁻¹)⁻¹ := by
  rw [one_sub_inv_one_sub_div_eq hz₀ hzz₀]
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem inv_eq_neg_inv_mul_inv_one_sub_div_mul {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0)
    (hzz₀ : z ≠ z₀) :
    z⁻¹ = -z₀⁻¹ * (1 - z / z₀)⁻¹ * (1 - (1 - z / z₀)⁻¹)⁻¹ := by
  rw [one_sub_inv_one_sub_div_eq hz₀ hzz₀, inv_one_sub_div_eq hz₀ hzz₀]
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem eulerKernel_ratio_eq {z z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hzz₀ : z ≠ z₀) (t : ℂ) :
    (1 - z₀⁻¹ * t) * (1 - z / z₀)⁻¹ = (z₀ - t) / (z₀ - z) := by
  rw [inv_one_sub_div_eq hz₀ hzz₀]
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem one_sub_div_mul_one_sub_eulerKernel_ratio {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0)
    (hzz₀ : z ≠ z₀) (t : ℂ) :
    (1 - z₀ / z) * (1 - (1 - z₀⁻¹ * t) * (1 - z / z₀)⁻¹) = 1 - z⁻¹ * t := by
  rw [eulerKernel_ratio_eq hz₀ hzz₀ t]
  have : z₀ - z ≠ 0 := sub_ne_zero.mpr hzz₀.symm
  field

private theorem norm_eval_ascPochhammer_div_factorial_le {a : ℂ} {R : ℝ} (ha : ‖a‖ ≤ R)
    (s : ℕ) :
    ‖(ascPochhammer ℂ s).eval a / (s ! : ℂ)‖ ≤ Ring.multichoose R s := by
  rw [div_eq_inv_mul, ← TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer]
  exact TauCeti.norm_multichoose_le_of_norm_le ha s

/-- Pointwise norm bound on the factored Euler kernel ratio on `[0, 1]`. -/
private theorem norm_eulerKernel_ratio_le {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(1 - z₀⁻¹ * (t : ℂ)) * (1 - z / z₀)⁻¹‖ ≤ max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖ := by
  rw [eulerKernel_ratio_eq hz₀ (ne_of_norm_lt_norm_sub ((le_max_left _ _).trans_lt hz)) (t : ℂ),
    norm_div, norm_sub_rev z₀ z]
  exact div_le_div_of_nonneg_right (norm_sub_ofReal_le_max z₀ ht) (norm_nonneg _)

/-- Pointwise binomial series expansion of the factored Euler kernel on `[0, 1]`. -/
private theorem hasSum_eulerKernel_inv (a : ℂ) {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a / s ! *
        ((1 - z₀⁻¹ * (t : ℂ)) * (1 - z / z₀)⁻¹) ^ s)
      ((1 - z₀ / z) ^ a * (1 - z⁻¹ * (t : ℂ)) ^ (-a)) := by
  have h_ext : ‖z₀‖ < ‖z - z₀‖ := (le_max_left _ _).trans_lt hz
  have hzz₀_pos : 0 < ‖z - z₀‖ := (norm_nonneg z₀).trans_lt h_ext
  let vt : ℂ := (1 - z₀⁻¹ * (t : ℂ)) * (1 - z / z₀)⁻¹
  have hvt_lt : ‖vt‖ < 1 :=
    (norm_eulerKernel_ratio_le hz₀ hz ht).trans_lt ((div_lt_one hzz₀_pos).mpr hz)
  let w₁ : ℂ := 1 - z₀ / z
  have hw₁_re : 0 < w₁.re := one_sub_div_re_pos h_ext
  have hw₁a_ne : w₁ ^ a ≠ 0 := by
    rw [cpow_def_of_ne_zero (by rintro h0; simp [h0] at hw₁_re)]; exact exp_ne_zero _
  have hw₂_re : 0 < (1 - vt).re :=
    TauCeti.re_pos_of_norm_sub_one_lt_one (by simpa [sub_sub_cancel_left] using hvt_lt)
  have hprod : w₁ * (1 - vt) = 1 - z⁻¹ * (t : ℂ) :=
    one_sub_div_mul_one_sub_eulerKernel_ratio (ne_zero_of_norm_lt_norm_sub h_ext) hz₀
      (ne_of_norm_lt_norm_sub h_ext) (t : ℂ)
  rw [← hprod, TauCeti.mul_cpow_of_re_pos hw₁_re hw₂_re (-a), cpow_neg w₁ a,
    ← mul_assoc, mul_inv_cancel₀ hw₁a_ne, one_mul]
  have hbin := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a) hvt_lt
  rw [one_div, ← cpow_neg] at hbin
  refine hbin.congr_fun fun s => ?_
  rw [TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer]
  dsimp only [vt]
  ring

/-- Pointwise norm majorant for the `s`-th Euler integrand term in DLMF 15.15.1. -/
private theorem norm_eulerKernel_inv_term_le (a b c : ℂ) {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (s : ℕ) :
    ‖((ascPochhammer ℂ s).eval a / s ! * ((1 - z / z₀)⁻¹) ^ s) *
        (((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (1 - z₀⁻¹ * (t : ℂ)) ^ (-(-(s : ℂ))))‖ ≤
      ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ *
        (Ring.multichoose ‖a‖ s * (max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖) ^ s) := by
  have hpoch_norm := norm_eval_ascPochhammer_div_factorial_le (a := a) le_rfl s
  let W : ℂ := (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  let vt : ℂ := (1 - z₀⁻¹ * (t : ℂ)) * (1 - z / z₀)⁻¹
  have h_rearrange : ((ascPochhammer ℂ s).eval a / s ! * ((1 - z / z₀)⁻¹) ^ s) *
      (W * (1 - z₀⁻¹ * (t : ℂ)) ^ (-(-(s : ℂ)))) =
      W * ((ascPochhammer ℂ s).eval a / s ! * vt ^ s) := by
    dsimp only [vt]; rw [neg_neg, cpow_natCast, mul_pow]; ring
  rw [h_rearrange, norm_mul W, norm_mul (_ / _), norm_pow]
  gcongr
  exacts [(norm_nonneg _).trans hpoch_norm,
    norm_eulerKernel_ratio_le hz₀ hz (Ioc_subset_Icc_self ht)]

/-- **Inverse-argument expansion of Euler's hypergeometric integral** (DLMF 15.15.1).
For `0 < b.re < c.re`, `z₀ ≠ 0`, and `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖`, the series in terminating
Gauss polynomials `regularizedGaussHGFun (-s) b c z₀⁻¹` converges to
`(1 - z₀ / z) ^ a * eulerIntegral a b c z⁻¹`. -/
theorem hasSum_eulerIntegral_inv (a : ℂ) {b c z z₀ : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    (hz₀ : z₀ ≠ 0) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a / s ! *
        regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s)
      ((1 - z₀ / z) ^ a * eulerIntegral a b c z⁻¹) := by
  have hM0 : 0 < max ‖z₀‖ ‖z₀ - 1‖ := (norm_pos_iff.mpr hz₀).trans_le (le_max_left _ _)
  have hzz₀_pos : 0 < ‖z - z₀‖ := hM0.trans hz
  let ρ : ℝ := max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖
  have hρ_abs : |ρ| < 1 := by
    rw [abs_of_nonneg (div_nonneg hM0.le hzz₀_pos.le)]
    exact (div_lt_one hzz₀_pos).mpr hz
  let W : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  have hW_int : IntervalIntegrable W volume 0 1 :=
    betaIntegral_convergent hb (by simpa using sub_pos.mpr hbc)
  have hdom_sum : Summable (fun s : ℕ => Ring.multichoose ‖a‖ s * ρ ^ s) :=
    (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one hρ_abs).summable
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun (s : ℕ) (t : ℝ) => ((ascPochhammer ℂ s).eval a / s ! * ((1 - z / z₀)⁻¹) ^ s) *
      (W t * (1 - z₀⁻¹ * (t : ℂ)) ^ (-(-(s : ℂ)))))
    (f := fun t : ℝ => (1 - z₀ / z) ^ a * (W t * (1 - z⁻¹ * (t : ℂ)) ^ (-a)))
    (bound := fun s t => ‖W t‖ * (Ring.multichoose ‖a‖ s * ρ ^ s))
    (a := 0) (b := 1) (μ := volume)
    (fun s => (intervalIntegrable_iff.mp
      ((hW_int.mul_continuousOn (by simp only [neg_neg, cpow_natCast]; fun_prop)).const_mul
        _)).aestronglyMeasurable)
    (fun s => ae_of_all _ fun t ht =>
      norm_eulerKernel_inv_term_le a b c hz₀ hz (uIoc_of_le (zero_le_one' ℝ) ▸ ht) s)
    (ae_of_all _ fun t _ => hdom_sum.mul_left ‖W t‖)
    (by simp_rw [tsum_mul_left]; exact hW_int.norm.mul_const _)
    (ae_of_all _ fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      convert (hasSum_eulerKernel_inv a hz₀ hz (Ioc_subset_Icc_self ht)).mul_left (W t) using 1
      · ext s; rw [neg_neg, cpow_natCast, mul_pow]; ring
      · ring)
  convert key.mul_left (Gamma b * Gamma (c - b))⁻¹ using 1
  · ext s
    rw [← eulerIntegral_neg_natCast hb hbc z₀⁻¹ s, eulerIntegral_def,
      intervalIntegral.integral_const_mul]
    ring
  · rw [eulerIntegral_def, intervalIntegral.integral_const_mul]
    ring

/-! ### Absolute convergence and holomorphy of the 15.15.1 series for all parameters -/

/-- Formal power series in `u = (1 - z / z₀)⁻¹` underlying DLMF 15.15.1. -/
private def invExpansionSeries (a b c z₀ : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ fun s => (ascPochhammer ℂ s).eval a / s ! * regularizedGaussHGFun (-s) b c z₀⁻¹

/-- Weighted summability of `regularizedGaussHGFun (-s) b c z₀⁻¹` in the Euler integral range. -/
private theorem summable_norm_regularizedGaussHGFun_neg_natCast_of_euler {b c z₀ : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz₀ : z₀ ≠ 0) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖) :
    Summable fun s : ℕ => ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r ^ s := by
  let M : ℝ := max ‖z₀‖ ‖z₀ - 1‖
  have hM0 : 0 < M := (norm_pos_iff.mpr hz₀).trans_le (le_max_left _ _)
  have hz0_pos : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
  let W : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  have hW_int : IntervalIntegrable W volume 0 1 :=
    betaIntegral_convergent hb (by simpa using sub_pos.mpr hbc)
  let C : ℝ := ‖(Gamma b * Gamma (c - b))⁻¹‖ * ∫ t : ℝ in 0..1, ‖W t‖
  have hbound (s : ℕ) : ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ ≤ C * (M / ‖z₀‖) ^ s := by
    rw [← eulerIntegral_neg_natCast hb hbc z₀⁻¹ s, eulerIntegral_def, norm_mul, mul_assoc]
    gcongr
    have hker : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(1 - z₀⁻¹ * (t : ℂ)) ^ s‖ ≤ (M / ‖z₀‖) ^ s := by
      intro t ht
      rw [norm_pow]
      gcongr
      have heq : 1 - z₀⁻¹ * (t : ℂ) = (z₀ - (t : ℂ)) / z₀ := by field
      rw [heq, norm_div]
      exact div_le_div_of_nonneg_right (norm_sub_ofReal_le_max z₀ (Ioc_subset_Icc_self ht))
        hz0_pos.le
    calc ‖∫ t : ℝ in 0..1, W t * (1 - z₀⁻¹ * (t : ℂ)) ^ (-(-(s : ℂ)))‖
        ≤ ∫ t : ℝ in 0..1, ‖W t‖ * (M / ‖z₀‖) ^ s := by
          refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (ae_of_all _ fun t ht => ?_) (hW_int.norm.mul_const _)
          rw [neg_neg, cpow_natCast, norm_mul]
          exact mul_le_mul_of_nonneg_left (hker t ht) (norm_nonneg _)
      _ = (∫ t : ℝ in 0..1, ‖W t‖) * (M / ‖z₀‖) ^ s := intervalIntegral.integral_mul_const _ _
  have hratio_lt : M / ‖z₀‖ * r < 1 := by
    rwa [mul_comm, ← lt_div_iff₀ (div_pos hM0 hz0_pos), div_div_eq_mul_div, one_mul]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun s => ?_)
    ((summable_geometric_of_lt_one (by positivity) hratio_lt).mul_left C)
  calc ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r ^ s
      ≤ C * (M / ‖z₀‖) ^ s * r ^ s := by gcongr; exact hbound s
    _ = C * (M / ‖z₀‖ * r) ^ s := by rw [mul_pow, mul_assoc]

/-- Multiplying a sequence by the index `s` preserves weighted summability strictly inside the
radius `R`. -/
private theorem summable_nat_mul_of_forall_lt {f : ℕ → ℝ} {R : ℝ}
    (hf : ∀ r : ℝ, 0 ≤ r → r < R → Summable fun s : ℕ => f s * r ^ s)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < R) :
    Summable fun s : ℕ => (s : ℝ) * f s * r ^ s := by
  let w : ℝ := (r + R) / 2
  have hw0 : 0 ≤ w := by dsimp only [w]; linarith
  have hwR : w < R := by dsimp only [w]; linarith
  have hrw : ‖r‖ < ‖w‖ := by
    rw [Real.norm_of_nonneg hr0, Real.norm_of_nonneg hw0]
    dsimp only [w]; linarith
  simpa only [pow_one] using TauCeti.summable_pow_mul_powerSeries_of_norm_lt 1
    ((hf w hw0 hwR).hasSum.tendsto_sum_nat.cauchySeq) hrw

/-- Lowering `c + 1 → c` preserves weighted summability of `regularizedGaussHGFun (-s) b c z₀⁻¹`. -/
private theorem summable_norm_regularizedGaussHGFun_neg_natCast_of_shift_c {b c z₀ : ℂ} {R : ℝ}
    (h : ∀ r : ℝ, 0 ≤ r → r < R → Summable fun s : ℕ =>
      ‖regularizedGaussHGFun (-s) b (c + 1) z₀⁻¹‖ * r ^ s) :
    ∀ r : ℝ, 0 ≤ r → r < R → Summable fun s : ℕ =>
      ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r ^ s := by
  intro r hr0 hr
  rw [← summable_nat_add_iff 1]
  have hw := summable_nat_mul_of_forall_lt h hr0 hr
  have hs1 := ((h r hr0 hr).comp_injective (add_left_injective 1)).mul_left (‖c‖ + 1)
  have hs2 := hw.comp_injective (add_left_injective 1)
  have hs3 := hw.mul_left r
  have hs4 := (h r hr0 hr).mul_left r
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    (((hs1.add hs2).add hs3).add hs4)
  dsimp only [Function.comp_def, Pi.add_apply]
  rw [regularizedGaussHGFun_neg_natCast_succ_eq_sub b c z₀⁻¹ n]
  have htri : ‖(c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹ -
        (n + 1) * regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ ≤
      (‖c‖ + 1 + ((n + 1 : ℕ) : ℝ)) *
          ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ +
        ((n : ℝ) + 1) * ‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ := by
    calc ‖(c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹ -
            (n + 1) * regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖
        ≤ ‖(c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ +
            ‖((n : ℂ) + 1) * regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ := norm_sub_le _ _
      _ = ‖c + n + 1‖ * ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ +
            ((n : ℝ) + 1) * ‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ := by
          rw [norm_mul, norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
          push_cast; rfl
      _ ≤ (‖c‖ + 1 + ((n + 1 : ℕ) : ℝ)) *
            ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ +
            ((n : ℝ) + 1) * ‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ := by
          gcongr
          calc ‖c + (n : ℂ) + 1‖ ≤ ‖c + (n : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ ≤ ‖c‖ + ‖(n : ℂ)‖ + 1 := by rw [norm_one]; gcongr; exact norm_add_le _ _
            _ ≤ ‖c‖ + 1 + ((n + 1 : ℕ) : ℝ) := by
              rw [Complex.norm_natCast]; push_cast; linarith
  calc ‖(c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹ -
          (n + 1) * regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ * r ^ (n + 1)
      ≤ ((‖c‖ + 1 + ((n + 1 : ℕ) : ℝ)) *
          ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ +
          ((n : ℝ) + 1) * ‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖) * r ^ (n + 1) := by gcongr
    _ = ((‖c‖ + 1) * (‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ * r ^ (n + 1)) +
          ((n + 1 : ℕ) : ℝ) * ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z₀⁻¹‖ *
            r ^ (n + 1)) +
        r * ((n : ℝ) * ‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ * r ^ n) +
        r * (‖regularizedGaussHGFun (-n) b (c + 1) z₀⁻¹‖ * r ^ n) := by
          rw [pow_succ r n]; ring

/-- Lowering `b + 1 → b` preserves weighted summability of `regularizedGaussHGFun (-s) b c z₀⁻¹`. -/
private theorem summable_norm_regularizedGaussHGFun_neg_natCast_of_shift_b {b z₀ : ℂ} {R : ℝ}
    (h : ∀ c : ℂ, ∀ r : ℝ, 0 ≤ r → r < R → Summable fun s : ℕ =>
      ‖regularizedGaussHGFun (-s) (b + 1) c z₀⁻¹‖ * r ^ s) :
    ∀ c : ℂ, ∀ r : ℝ, 0 ≤ r → r < R → Summable fun s : ℕ =>
      ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r ^ s := by
  intro c r hr0 hr
  rw [← summable_nat_add_iff 1]
  have hw := summable_nat_mul_of_forall_lt (h (c + 1)) hr0 hr
  have hs1 := (h c r hr0 hr).comp_injective (add_left_injective 1)
  have hs2 := hw.mul_left (‖z₀⁻¹‖ * r)
  have hs3 := (h (c + 1) r hr0 hr).mul_left (‖z₀⁻¹‖ * r)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) ((hs1.add hs2).add hs3)
  dsimp only [Function.comp_def, Pi.add_apply]
  rw [regularizedGaussHGFun_neg_natCast_succ_eq_add b c z₀⁻¹ n]
  have htri : ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z₀⁻¹ +
        (n + 1) * z₀⁻¹ * regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖ ≤
      ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z₀⁻¹‖ +
        ((n : ℝ) + 1) * ‖z₀⁻¹‖ * ‖regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
    push_cast
    exact le_rfl
  calc ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z₀⁻¹ +
          (n + 1) * z₀⁻¹ * regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖ * r ^ (n + 1)
      ≤ (‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z₀⁻¹‖ +
          ((n : ℝ) + 1) * ‖z₀⁻¹‖ * ‖regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖) *
            r ^ (n + 1) := by gcongr
    _ = ‖regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z₀⁻¹‖ * r ^ (n + 1) +
        (‖z₀⁻¹‖ * r) * ((n : ℝ) * ‖regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖ * r ^ n) +
        (‖z₀⁻¹‖ * r) * (‖regularizedGaussHGFun (-n) (b + 1) (c + 1) z₀⁻¹‖ * r ^ n) := by
          rw [pow_succ r n]; ring

/-- Weighted summability of `regularizedGaussHGFun (-s) b c z₀⁻¹` for all complex parameters `b`
and `c`. -/
private theorem summable_norm_regularizedGaussHGFun_neg_natCast_mul_pow (b c : ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖) :
    Summable fun s : ℕ => ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r ^ s := by
  let R : ℝ := ‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖
  have hpoly_of_re_pos : ∀ b' : ℂ, 0 < b'.re → ∀ c' : ℂ, ∀ r' : ℝ, 0 ≤ r' → r' < R →
      Summable fun s : ℕ => ‖regularizedGaussHGFun (-s) b' c' z₀⁻¹‖ * r' ^ s := by
    intro b' hb' c'
    have hstep : ∀ q : ℕ, ∀ c₀ : ℂ, b'.re < (c₀ + q).re → ∀ r' : ℝ, 0 ≤ r' → r' < R →
        Summable fun s : ℕ => ‖regularizedGaussHGFun (-s) b' c₀ z₀⁻¹‖ * r' ^ s := by
      intro q
      induction q with
      | zero =>
        intro c₀ hc₀ r' hr0' hr'
        exact summable_norm_regularizedGaussHGFun_neg_natCast_of_euler hb' (by simpa using hc₀)
          hz₀ hr0' hr'
      | succ q ih =>
        intro c₀ hc₀
        refine summable_norm_regularizedGaussHGFun_neg_natCast_of_shift_c (ih (c₀ + 1) ?_)
        simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one] at hc₀ ⊢
        linarith
    refine hstep (⌈b'.re - c'.re⌉₊ + 1) c' ?_
    simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (b'.re - c'.re)]
  have hpoly_step_b : ∀ p : ℕ, ∀ b₀ : ℂ, 0 < (b₀ + p).re → ∀ c' : ℂ, ∀ r' : ℝ, 0 ≤ r' → r' < R →
      Summable fun s : ℕ => ‖regularizedGaussHGFun (-s) b₀ c' z₀⁻¹‖ * r' ^ s := by
    intro p
    induction p with
    | zero => intro b₀ hb₀; exact hpoly_of_re_pos b₀ (by simpa using hb₀)
    | succ p ih =>
      intro b₀ hb₀
      refine summable_norm_regularizedGaussHGFun_neg_natCast_of_shift_b (ih (b₀ + 1) ?_)
      simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one] at hb₀ ⊢
      linarith
  refine hpoly_step_b (⌈-b.re⌉₊ + 1) b ?_ c r hr0 hr
  simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (-b.re)]

/-- The formal series `invExpansionSeries a b c z₀` has convergence radius at least
`‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖` for all complex parameters `a`, `b`, `c`. -/
private theorem le_radius_invExpansionSeries (a b c : ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ENNReal.ofReal (‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖) ≤ (invExpansionSeries a b c z₀).radius := by
  let R : ℝ := ‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr0 hrR => ?_
  have hr_lt : (r : ℝ) < R := by
    rw [← ENNReal.ofReal_coe_nnreal] at hrR
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hrR
  have hr_pos : 0 < (r : ℝ) := hr0
  let r' : ℝ := ((r : ℝ) + R) / 2
  have hr' : (r : ℝ) < r' := by dsimp only [r']; linarith
  have hr'R : r' < R := by dsimp only [r']; linarith
  have hr'_pos : 0 < r' := hr_pos.trans hr'
  have hθ_lt : |(r : ℝ) / r'| < 1 := by
    rw [abs_of_pos (div_pos hr_pos hr'_pos)]
    exact (div_lt_one hr'_pos).mpr hr'
  obtain ⟨C, hC⟩ := bddAbove_def.mp <|
    (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := ‖a‖) hθ_lt)
      |>.summable.tendsto_atTop_zero.bddAbove_range
  refine (invExpansionSeries a b c z₀).le_radius_of_summable_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun s => ?_)
    ((summable_norm_regularizedGaussHGFun_neg_natCast_mul_pow b c hz₀ hr'_pos.le hr'R).mul_left C)
  have hpoch_norm := norm_eval_ascPochhammer_div_factorial_le (a := a) le_rfl s
  have hsC : Ring.multichoose ‖a‖ s * ((r : ℝ) / r') ^ s ≤ C := hC _ ⟨s, rfl⟩
  have hsplit : (r : ℝ) ^ s = ((r : ℝ) / r') ^ s * r' ^ s := by
    rw [← mul_pow, div_mul_cancel₀ _ hr'_pos.ne']
  rw [invExpansionSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul]
  calc ‖(ascPochhammer ℂ s).eval a / (s ! : ℂ)‖ * ‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ *
          (r : ℝ) ^ s
      = (‖(ascPochhammer ℂ s).eval a / (s ! : ℂ)‖ * ((r : ℝ) / r') ^ s) *
          (‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r' ^ s) := by rw [hsplit]; ring
    _ ≤ (Ring.multichoose ‖a‖ s * ((r : ℝ) / r') ^ s) *
          (‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r' ^ s) := by gcongr
    _ ≤ C * (‖regularizedGaussHGFun (-s) b c z₀⁻¹‖ * r' ^ s) := by gcongr

/-- On the exterior domain `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖`, `(1 - z / z₀)⁻¹` lies inside the
convergence ball of `invExpansionSeries a b c z₀`. -/
private theorem mem_eball_invExpansionSeries (a b c : ℂ) {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    (1 - z / z₀)⁻¹ ∈ Metric.eball (0 : ℂ) (invExpansionSeries a b c z₀).radius := by
  have hM0 : 0 < max ‖z₀‖ ‖z₀ - 1‖ := (norm_pos_iff.mpr hz₀).trans_le (le_max_left _ _)
  have hu_norm : ‖(1 - z / z₀)⁻¹‖ < ‖z₀‖ / max ‖z₀‖ ‖z₀ - 1‖ := by
    rw [inv_one_sub_div_eq hz₀ (ne_of_norm_lt_norm_sub ((le_max_left _ _).trans_lt hz)),
      norm_div, norm_sub_rev z₀ z]
    exact div_lt_div_of_pos_left (norm_pos_iff.mpr hz₀) hM0 hz
  refine Metric.eball_subset_eball (le_radius_invExpansionSeries a b c hz₀) ?_
  rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
    ENNReal.ofReal_lt_ofReal_iff (div_pos (norm_pos_iff.mpr hz₀) hM0)]

/-- For arbitrary complex parameters `a`, `b`, `c` and any `z₀ ≠ 0`, the inverse-argument
hypergeometric polynomial series (DLMF 15.15.1) converges absolutely throughout the exterior
domain `max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖`. -/
theorem summable_norm_regularizedGaussHGFun_neg_natCast_mul_inv_pow (a b c : ℂ) {z z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    Summable fun s : ℕ =>
      ‖(ascPochhammer ℂ s).eval a / s ! * regularizedGaussHGFun (-s) b c z₀⁻¹ *
        ((1 - z / z₀)⁻¹) ^ s‖ := by
  simpa [invExpansionSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm, mul_left_comm,
    mul_assoc] using
    (invExpansionSeries a b c z₀).summable_norm_apply (mem_eball_invExpansionSeries a b c hz₀ hz)

/-- For arbitrary complex parameters `a`, `b`, `c` and any `z₀ ≠ 0`, the sum of the
inverse-argument hypergeometric polynomial series (DLMF 15.15.1) is holomorphic on the open
exterior domain `{z | max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖}`. -/
theorem analyticOnNhd_tsum_regularizedGaussHGFun_neg_natCast_mul_inv_pow (a b c : ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' s : ℕ, (ascPochhammer ℂ s).eval a / s ! *
        regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s)
      {z | max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖} := by
  have heq : (fun z : ℂ => ∑' s : ℕ, (ascPochhammer ℂ s).eval a / s ! *
        regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s) =
      ((invExpansionSeries a b c z₀).sum ∘ fun z : ℂ => (1 - z / z₀)⁻¹) := by
    ext z
    simp [FormalMultilinearSeries.sum, invExpansionSeries, mul_comm]
  rw [heq]
  intro z hz
  have hzz₀ : z ≠ z₀ := ne_of_norm_lt_norm_sub ((le_max_left _ _).trans_lt hz)
  have h1zz₀ : 1 - z / z₀ ≠ 0 := fun h0 =>
    hzz₀ ((div_eq_one_iff_eq hz₀).mp (sub_eq_zero.mp h0).symm)
  have hφ : AnalyticAt ℂ (fun w : ℂ => (1 - w / z₀)⁻¹) z :=
    (analyticAt_const.sub (analyticAt_id.div analyticAt_const hz₀)).inv h1zz₀
  exact ((invExpansionSeries a b c z₀).analyticOnNhd _
    (mem_eball_invExpansionSeries a b c hz₀ hz)).comp_of_eq hφ rfl

/-! ### Double-series rearrangement and DLMF 15.15.1 for `regularizedGaussHGFun` and `₂F₁` -/

/-- Antidiagonal convolution of `regularizedGaussHGFun` coefficients with shifted binomial
coefficients produces the `s`-th coefficient of DLMF 15.15.1. -/
private theorem sum_regularizedGaussHGFunCoeff_mul_eq (a b c w : ℂ) (s : ℕ) :
    (∑ k ∈ Finset.range (s + 1),
        (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * (-w) ^ k *
          ((ascPochhammer ℂ (s - k)).eval (a + k) / (s - k)!)) =
      (ascPochhammer ℂ s).eval a / s ! * regularizedGaussHGFun (-s) b c w := by
  rw [regularizedGaussHGFun_neg_natCast_eq_sum b c w s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpoch_a : (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ (s - k)).eval (a + k) =
      (ascPochhammer ℂ s).eval a := by
    have h := congr_arg (Polynomial.eval a) (ascPochhammer_mul (S := ℂ) k (s - k))
    simpa [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, Nat.add_sub_of_le hks] using h
  have hpoch_s : (ascPochhammer ℂ k).eval (-(s : ℂ)) * (s - k)! = (-1) ^ k * s ! := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
    have hdesc : s.descFactorial k * (s - k)! = s ! := by
      rw [mul_comm, Nat.factorial_mul_descFactorial hks]
    calc (-1 : ℂ) ^ k * (s.descFactorial k : ℂ) * ((s - k)! : ℂ)
        = (-1 : ℂ) ^ k * ((s.descFactorial k * (s - k)! : ℕ) : ℂ) := by push_cast; ring
      _ = (-1 : ℂ) ^ k * s ! := by rw [hdesc]
  have hk_fac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hsk_fac : ((s - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (s - k).factorial_ne_zero
  have hs_fac : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  have hmw : (-w) ^ k = (-1) ^ k * w ^ k := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [hmw]
  calc (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * ((-1) ^ k * w ^ k) *
          ((ascPochhammer ℂ (s - k)).eval (a + k) / (s - k)!)
      = ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ (s - k)).eval (a + k)) *
          (ascPochhammer ℂ k).eval b * ((-1) ^ k * s !) /
          (s ! * ((s - k)! * (k ! * Gamma (c + k)))) * w ^ k := by field_simp
    _ = (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ k).eval b *
          ((ascPochhammer ℂ k).eval (-(s : ℂ)) * (s - k)!) /
          (s ! * ((s - k)! * (k ! * Gamma (c + k)))) * w ^ k := by rw [hpoch_a, hpoch_s]
    _ = (ascPochhammer ℂ s).eval a / s ! *
          ((ascPochhammer ℂ k).eval (-(s : ℂ)) * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + k)) * w ^ k) := by field_simp

/-- Bivariate term of the double-series expansion of `(1 - u) ^ (-a) * regularizedGaussHGFun`. -/
private def doubleSeriesTerm (a b c z₀ u : ℂ) (km : ℕ × ℕ) : ℂ :=
  (ascPochhammer ℂ km.1).eval a * (ascPochhammer ℂ km.1).eval b /
    (km.1 ! * Gamma (c + km.1)) * (-z₀⁻¹) ^ km.1 * u ^ km.1 *
    ((ascPochhammer ℂ km.2).eval (a + km.1) / km.2 ! * u ^ km.2)

/-- Pointwise norm majorant for `doubleSeriesTerm`. -/
private theorem norm_doubleSeriesTerm_le (a b c z₀ u : ℂ) (k m : ℕ) :
    ‖doubleSeriesTerm a b c z₀ u (k, m)‖ ≤
      ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + k))‖ *
        (‖z₀‖⁻¹ * ‖u‖) ^ k * (Ring.multichoose (‖a‖ + k) m * ‖u‖ ^ m) := by
  simp only [doubleSeriesTerm, norm_mul, norm_pow, norm_neg, norm_inv, mul_pow]
  have hm_le := norm_eval_ascPochhammer_div_factorial_le
    (by simpa [Complex.norm_natCast] using norm_add_le a k) m
  calc ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + k))‖ *
          ‖z₀‖⁻¹ ^ k * ‖u‖ ^ k * (‖(ascPochhammer ℂ m).eval (a + k) / (m ! : ℂ)‖ * ‖u‖ ^ m)
      ≤ ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + k))‖ *
          ‖z₀‖⁻¹ ^ k * ‖u‖ ^ k * (Ring.multichoose (‖a‖ + k) m * ‖u‖ ^ m) := by gcongr
    _ = _ := by ring

/-- Absolute summability of `doubleSeriesTerm` when `‖u‖ < 1` and `‖u‖ / (‖z₀‖ * (1 - ‖u‖)) < 1`. -/
private theorem summable_norm_doubleSeriesTerm (a b c : ℂ) {z₀ u : ℂ} (hz₀ : z₀ ≠ 0)
    (hu : ‖u‖ < 1) (hρ : ‖u‖ / (‖z₀‖ * (1 - ‖u‖)) < 1) :
    Summable fun km : ℕ × ℕ => ‖doubleSeriesTerm a b c z₀ u km‖ := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  have hinner (k : ℕ) : HasSum (fun m : ℕ => Ring.multichoose (‖a‖ + k) m * ‖u‖ ^ m)
      ((1 - ‖u‖) ^ (-‖a‖ - (k : ℝ))) := by
    simpa only [one_div, ← Real.rpow_neg (sub_nonneg.mpr hu.le), neg_add'] using
      TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := ‖a‖ + k) (x := ‖u‖)
        (by rwa [abs_of_nonneg (norm_nonneg u)])
  refine ⟨fun k => Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_doubleSeriesTerm_le a b c z₀ u k) ((hinner k).summable.mul_left _), ?_⟩
  let ρ : ℝ := ‖u‖ / (‖z₀‖ * (1 - ‖u‖))
  have h1u : 0 < 1 - ‖u‖ := sub_pos.mpr hu
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg u) (mul_pos (norm_pos_iff.mpr hz₀) h1u).le
  have hout := (summable_norm_regularizedGaussHGFun a b c (z := (ρ : ℂ))
    (by rwa [Complex.norm_real, Real.norm_of_nonneg hρ0])).mul_left ((1 - ‖u‖) ^ (-‖a‖))
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun k => ?_) hout
  calc (∑' m, ‖doubleSeriesTerm a b c z₀ u (k, m)‖)
      ≤ ∑' m, ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k))‖ * (‖z₀‖⁻¹ * ‖u‖) ^ k *
          (Ring.multichoose (‖a‖ + k) m * ‖u‖ ^ m) :=
        Summable.tsum_le_tsum (norm_doubleSeriesTerm_le a b c z₀ u k)
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (norm_doubleSeriesTerm_le a b c z₀ u k) ((hinner k).summable.mul_left _))
          ((hinner k).summable.mul_left _)
    _ = ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b / (k ! * Gamma (c + k))‖ *
          (‖z₀‖⁻¹ * ‖u‖) ^ k * ((1 - ‖u‖) ^ (-‖a‖ - (k : ℝ))) := by
      rw [tsum_mul_left, (hinner k).tsum_eq]
    _ = (1 - ‖u‖) ^ (-‖a‖) *
          ‖(ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
            (k ! * Gamma (c + k)) * (ρ : ℂ) ^ k‖ := by
      have : ‖z₀‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀
      have : 1 - ‖u‖ ≠ 0 := h1u.ne'
      rw [Real.rpow_sub h1u, Real.rpow_natCast, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hρ0]
      dsimp only [ρ]
      rw [div_pow, mul_pow, mul_pow, inv_pow]
      field

/-- Far from `z₀` (`1 + ‖z₀‖ < ‖z - z₀‖`), the bivariate family `doubleSeriesTerm` has sum
`(1 - z₀ / z) ^ a * regularizedGaussHGFun a b c z⁻¹`. -/
private theorem hasSum_doubleSeriesTerm (a b c : ℂ) {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : 1 + ‖z₀‖ < ‖z - z₀‖) :
    HasSum (doubleSeriesTerm a b c z₀ ((1 - z / z₀)⁻¹))
      ((1 - z₀ / z) ^ a * regularizedGaussHGFun a b c z⁻¹) := by
  have h_ext : ‖z₀‖ < ‖z - z₀‖ := by linarith
  have hzz₀_pos : 0 < ‖z - z₀‖ := (norm_nonneg z₀).trans_lt h_ext
  have hzz₀ : z ≠ z₀ := ne_of_norm_lt_norm_sub h_ext
  have hz1 : 1 < ‖z‖ := by linarith [norm_sub_le z z₀]
  have hz_ne : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz1)
  let u : ℂ := (1 - z / z₀)⁻¹
  have hu_eq : u = z₀ / (z₀ - z) := inv_one_sub_div_eq hz₀ hzz₀
  have hu_lt : ‖u‖ < 1 := by
    rw [hu_eq, norm_div, norm_sub_rev z₀ z, div_lt_one hzz₀_pos]; linarith
  have hρ_lt : ‖u‖ / (‖z₀‖ * (1 - ‖u‖)) < 1 := by
    have hz0_ne : ‖z₀‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀
    have hsub : ‖z - z₀‖ - ‖z₀‖ ≠ 0 := by linarith
    have hρ_eq : ‖u‖ / (‖z₀‖ * (1 - ‖u‖)) = 1 / (‖z - z₀‖ - ‖z₀‖) := by
      rw [hu_eq, norm_div, norm_sub_rev z₀ z]; field
    rw [hρ_eq, div_lt_one (by linarith)]; linarith
  have hH := (summable_norm_doubleSeriesTerm a b c hz₀ hu_lt hρ_lt).of_norm
  have h1u_re : 0 < (1 - u).re :=
    TauCeti.re_pos_of_norm_sub_one_lt_one (by simpa [sub_sub_cancel_left] using hu_lt)
  have h1u_ne : 1 - u ≠ 0 := by rintro h0; simp [h0] at h1u_re
  have hfib_k (k : ℕ) : HasSum (fun m : ℕ => doubleSeriesTerm a b c z₀ u (k, m))
      ((1 - u) ^ (-a) * ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
        (k ! * Gamma (c + k)) * (z⁻¹) ^ k)) := by
    have hbin := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a + k) hu_lt
    simp_rw [TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer, inv_mul_eq_div,
      one_div, ← cpow_neg] at hbin
    have hzinv : z⁻¹ = -z₀⁻¹ * u * (1 - u)⁻¹ :=
      inv_eq_neg_inv_mul_inv_one_sub_div_mul hz_ne hz₀ hzz₀
    have hcpow : (1 - u) ^ (-(a + k)) = (1 - u) ^ (-a) * ((1 - u)⁻¹) ^ k := by
      rw [neg_add, cpow_add _ _ h1u_ne, cpow_neg (1 - u) (k : ℂ), cpow_natCast, inv_pow]
    have hval : ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * (-z₀⁻¹) ^ k * u ^ k) * (1 - u) ^ (-(a + k)) =
        (1 - u) ^ (-a) * ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * (z⁻¹) ^ k) := by
      rw [hcpow, hzinv, mul_pow, mul_pow]; ring
    exact hval ▸ hbin.mul_left _
  have hw_eq : 1 - z₀ / z = (1 - u)⁻¹ := one_sub_div_eq_inv_one_sub_inv_one_sub_div hz_ne hz₀ hzz₀
  have hw_pow : (1 - u) ^ (-a) = (1 - z₀ / z) ^ a := by
    rw [hw_eq, inv_cpow _ _ (slitPlane_arg_ne_pi (Or.inl h1u_re)), cpow_neg]
  have hgauss := (hasSum_regularizedGaussHGFun a b c
    (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)).mul_left ((1 - u) ^ (-a))
  simp_rw [coeff_regularizedGaussHGFunSeries] at hgauss
  have htsum_eq : (∑' km, doubleSeriesTerm a b c z₀ u km) =
      (1 - z₀ / z) ^ a * regularizedGaussHGFun a b c z⁻¹ := by
    rw [(hH.hasSum.prod_fiberwise hfib_k).unique hgauss, hw_pow]
  exact htsum_eq ▸ hH.hasSum

/-- Far from `z₀` (`1 + ‖z₀‖ < ‖z - z₀‖`), antidiagonal rearrangement of `doubleSeriesTerm` yields
DLMF 15.15.1 for `regularizedGaussHGFun` at all complex parameters `a`, `b`, `c`. -/
private theorem hasSum_regularizedGaussHGFun_inv_of_one_add_norm_lt (a b c : ℂ) {z z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz : 1 + ‖z₀‖ < ‖z - z₀‖) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a / s ! *
        regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s)
      ((1 - z₀ / z) ^ a * regularizedGaussHGFun a b c z⁻¹) := by
  let u : ℂ := (1 - z / z₀)⁻¹
  have hanti := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hasSum_doubleSeriesTerm a b c hz₀ hz)).sigma fun _ => hasSum_fintype _
  refine hanti.congr_fun fun s => ?_
  simp only [Function.comp_def, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_coe_sort, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← sum_regularizedGaussHGFunCoeff_mul_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : u ^ k * u ^ (s - k) = u ^ s := by rw [← pow_add, Nat.add_sub_of_le hks]
  simp only [doubleSeriesTerm]
  linear_combination
    (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b /
      (k ! * Gamma (c + k)) * (-z₀⁻¹) ^ k *
      ((ascPochhammer ℂ (s - k)).eval (a + k) / (s - k)!) * hpow.symm

/-- Holomorphy of `(1 - z₀ / w) ^ a * regularizedGaussHGFun a b c w⁻¹` on
`{w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖}`. -/
private theorem analyticOnNhd_cpow_mul_regularizedGaussHGFun_inv (a b c z₀ : ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => (1 - z₀ / w) ^ a * regularizedGaussHGFun a b c w⁻¹)
      {w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖} := by
  intro w hw
  have hw_ne : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hw.1)
  have hcpow : AnalyticAt ℂ (fun ζ : ℂ => (1 - z₀ / ζ) ^ a) w :=
    (analyticAt_const.sub (analyticAt_const.div analyticAt_id hw_ne)).cpow analyticAt_const
      (Or.inl (one_sub_div_re_pos ((le_max_left _ _).trans_lt hw.2)))
  have hhg : AnalyticAt ℂ (fun ζ : ℂ => regularizedGaussHGFun a b c ζ⁻¹) w :=
    (analyticAt_regularizedGaussHGFun a b c
      (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw.1)).fun_comp (analyticAt_id.inv hw_ne)
  exact hcpow.mul hhg

/-- Every point of `{w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖}` lies in a preconnected subset
contained in the domain that meets the far region `{w | 1 + ‖z₀‖ < ‖w - z₀‖}`. -/
private theorem exists_isPreconnected_mem_far_of_exterior {z z₀ : ℂ}
    (hz₁ : 1 < ‖z‖) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    ∃ S : Set ℂ, IsPreconnected S ∧
      S ⊆ {w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖} ∧
      z ∈ S ∧ ∃ w ∈ S, 1 + ‖z₀‖ < ‖w - z₀‖ := by
  obtain ⟨ε, hε, hv_ip⟩ : ∃ ε : ℂ, (ε = I ∨ ε = -I) ∧ 0 ≤ ((z - z₀) * conj (ε * z)).re := by
    rcases le_total 0 (((z - z₀) * conj (I * z)).re) with h | h
    · exact ⟨I, Or.inl rfl, h⟩
    · exact ⟨-I, Or.inr rfl, by rw [neg_mul, map_neg, mul_neg, neg_re]; linarith⟩
  let v : ℂ := ε * z
  let S : Set ℂ := (fun t : ℝ => z + (t : ℂ) * v) '' Ici 0
  have hSU : S ⊆ {w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖} := by
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · have hmul : z + (t : ℂ) * v = z * (1 + (t : ℂ) * ε) := by dsimp only [v]; ring
      have hre1 : (1 + (t : ℂ) * ε).re = 1 := by rcases hε with rfl | rfl <;> simp
      rw [hmul, norm_mul]
      exact lt_of_lt_of_le hz₁ (le_mul_of_one_le_right (norm_nonneg z) (hre1 ▸ re_le_norm _))
    · have hident : normSq (z + (t : ℂ) * v - z₀) =
          normSq (z - z₀) + 2 * t * ((z - z₀) * conj v).re + t ^ 2 * normSq v := by
        rw [add_sub_right_comm, normSq_add, normSq_mul (t : ℂ) v, normSq_ofReal,
          map_mul (starRingEnd ℂ) (t : ℂ) v, conj_ofReal, mul_left_comm, re_ofReal_mul]
        ring
      have hsq : normSq (z - z₀) ≤ normSq (z + (t : ℂ) * v - z₀) := by
        nlinarith [mem_Ici.mp ht, normSq_nonneg v]
      exact hz.trans_le (by simpa [norm_def] using Real.sqrt_le_sqrt hsq)
  let T : ℝ := 1 + ‖z₀‖ + ‖z - z₀‖ + 1
  have hT_pos : 0 ≤ T := by positivity
  refine ⟨S, isPreconnected_Ici.image _ (by fun_prop), hSU, ⟨0, le_rfl, by simp⟩,
    z + (T : ℂ) * v, ⟨T, hT_pos, rfl⟩, ?_⟩
  have hv_norm : ‖(T : ℂ) * v‖ = T * ‖z‖ := by
    rcases hε with rfl | rfl <;> simp [v, abs_of_nonneg hT_pos]
  have hsub : z + (T : ℂ) * v - z₀ = (T : ℂ) * v - (z₀ - z) := by ring
  linarith [hsub ▸ norm_sub_norm_le ((T : ℂ) * v) (z₀ - z), norm_sub_rev z₀ z,
    le_mul_of_one_le_right hT_pos hz₁.le, hv_norm]

/-- **Inverse-argument expansion of the regularized Gauss hypergeometric function**
(DLMF 15.15.1) on `{z | 1 < ‖z‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖}`, valid for all complex
parameters `a`, `b`, `c` (including nonpositive integer values of `c`). -/
theorem hasSum_regularizedGaussHGFun_inv (a b c : ℂ) {z z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz₁ : 1 < ‖z‖) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a / s ! *
        regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s)
      ((1 - z₀ / z) ^ a * regularizedGaussHGFun a b c z⁻¹) := by
  let U : Set ℂ := {w | 1 < ‖w‖ ∧ max ‖z₀‖ ‖z₀ - 1‖ < ‖w - z₀‖}
  let L : ℂ → ℂ := fun w => ∑' s : ℕ, (ascPochhammer ℂ s).eval a / s ! *
    regularizedGaussHGFun (-s) b c z₀⁻¹ * ((1 - w / z₀)⁻¹) ^ s
  let G : ℂ → ℂ := fun w => (1 - z₀ / w) ^ a * regularizedGaussHGFun a b c w⁻¹
  obtain ⟨S, hS_pre, hSU, hzS, w, hwS, hw_far⟩ := exists_isPreconnected_mem_far_of_exterior hz₁ hz
  have hev : L =ᶠ[𝓝 w] G := by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds
      hw_far] with ζ hζ
    exact (hasSum_regularizedGaussHGFun_inv_of_one_add_norm_lt a b c hz₀ hζ).tsum_eq
  have heq_z : L z = G z :=
    (((analyticOnNhd_tsum_regularizedGaussHGFun_neg_natCast_mul_inv_pow a b c hz₀).mono
      (s := U) (fun _ hw => hw.2)).mono hSU).eqOn_of_preconnected_of_eventuallyEq
      ((analyticOnNhd_cpow_mul_regularizedGaussHGFun_inv a b c z₀).mono hSU)
      hS_pre hwS hev hzS
  have hsum :=
    (summable_norm_regularizedGaussHGFun_neg_natCast_mul_inv_pow a b c hz₀ hz).of_norm.hasSum
  convert hsum using 1
  exact heq_z.symm

/-- **Inverse-argument expansion of the ordinary Gauss hypergeometric function `₂F₁`**
(unregularized form of DLMF 15.15.1), when `c` is not a nonpositive integer. -/
theorem hasSum_ordinaryHypergeometric_inv (a b : ℂ) {c z z₀ : ℂ} (hc : ∀ k : ℕ, c ≠ -k)
    (hz₀ : z₀ ≠ 0) (hz₁ : 1 < ‖z‖) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a / s ! *
        ₂F₁ (-s : ℂ) b c z₀⁻¹ * ((1 - z / z₀)⁻¹) ^ s)
      ((1 - z₀ / z) ^ a * ₂F₁ a b c z⁻¹) := by
  have hGc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hmul (u w : ℂ) : Gamma c * regularizedGaussHGFun u b c w = ₂F₁ u b c w := by
    rw [← ordinaryHypergeometric_div_Gamma_eq hc, mul_div_cancel₀ _ hGc]
  convert (hasSum_regularizedGaussHGFun_inv a b c hz₀ hz₁ hz).mul_left (Gamma c) using 1
  · ext s; rw [← hmul (-s) z₀⁻¹]; ring
  · rw [← hmul a z⁻¹]; ring

end Complex

end
