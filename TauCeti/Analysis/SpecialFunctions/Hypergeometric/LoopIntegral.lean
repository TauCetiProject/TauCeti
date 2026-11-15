/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Loop and Pochhammer contour integrals for the Gauss hypergeometric function

Euler's integral `Complex.eulerIntegral` represents Olver's regularized Gauss hypergeometric
function only when `0 < re b < re c`. Replacing one or both endpoints of `[0, 1]` by small keyhole
loops continues the integral analytically across the parameter half-plane boundaries throughout the
principal cut plane `{z | 1 - z ∈ Complex.slitPlane}`:

* `Complex.hypergeometricLoopOne` is the `(1+)` loop integral (DLMF 15.6.2) running from `0` to
  `1 - ρ` below `[1, ∞)` (`ph t = 0`, `ph (t - 1) = -π`), counterclockwise around `1 + ρ e^{iθ}`
  (`θ ∈ [-π, π]`) with principal values on `(1, ∞)`, and back from `1 - ρ` to `0` above `[1, ∞)`
  (`ph (t - 1) = π`). For `0 < re b` it is independent of `ρ` and holomorphic in `(a, c, z)`.
* `Complex.hypergeometricLoopZero` is the `(0+)` loop integral (DLMF 15.6.4) running from `1` to
  `ρ` (`ph t = ph (1 - t) = 0`), counterclockwise around `ρ e^{iθ}` (`θ ∈ [0, 2π]`, `ph t = π` on
  `(-∞, 0)`), and back from `ρ` to `1` (`ph t = 2π`). For `0 < re (c - b)` it is independent of `ρ`
  and jointly holomorphic in `(a, b, z)` along lines of fixed `c - b`.
* `Complex.hypergeometricPochhammerLoop` is Pochhammer's `(0+, 1+, 0-, 1-)` commutator contour
  integral (DLMF 15.6.5) based at `A ∈ (0, 1)` (`ph t = ph (1 - t) = 0`) with radii `ρ₀` around `0`
  and `ρ₁` around `1`. Avoiding both `0` and `1`, it is independent of `(A, ρ₀, ρ₁)` and jointly
  holomorphic in `(a, b, c, z)` with no real-part restrictions.

For `0 < re b < re c`, shrinking the loop radii collapses each contour onto `[0, 1]`, yielding
DLMF 15.6.2, 15.6.4, and 15.6.5 on the cut plane. At `a = 0` or `z = 0`, parameter holomorphy
evaluates all three integrals in closed form via reciprocal Gamma factors, including Pochhammer's
Beta contour integral (DLMF 5.12.12) across all `(b, c) ∈ ℂ × ℂ`.

## Implementation notes

All three contours reduce to a single internal `(0+)` keyhole functional `affineLoopZero` for
`u ^ (β - 1) * (1 - u) ^ (γ - 1) * (w₀ - w₁ * u) ^ (-a)` on `[ρ, A]`: directly at `(b, c - b, 1, z)`
for `hypergeometricLoopZero`, via `u = 1 - t` at `(c - b, b, 1 - z, -z)` for
`hypergeometricLoopOne`, and as a linear combination of both halves split at `A` for
`hypergeometricPochhammerLoop`. Under `w = log u`, two radii bound a rectangle
`[log ρ₁, log ρ₂] × [0, 2π]`, so Cauchy's theorem on rectangles proves radius independence
uniformly.

## References

* NIST Digital Library of Mathematical Functions, §§5.12 (5.12.12) and 15.6
  (15.6.2, 15.6.4, 15.6.5).
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5, §9.3.
* N. M. Temme, *Special Functions*, §5.2.2; E. T. Whittaker and G. N. Watson, *A Course of Modern
  Analysis*, §§12.43 and 14.6.
* Bastiaan J. Braams, `DLMF.Hypergeometric.LoopIntegral` in `lean-DLMF`
  (https://github.com/bjbraams/lean-DLMF, Apache-2.0): the logarithmic-rectangle Cauchy argument for
  the `(1+)` loop on the unit disk is adapted here to the unified `(0+)` keyhole functional on the
  principal cut plane.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Real Set
open scoped Topology Interval

namespace Complex

/-! ### Internal `(0+)` keyhole functional -/

private def affineSegIntegrand (a β γ w₀ w₁ : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (β - 1) * (1 - (u : ℂ)) ^ (γ - 1) * (w₀ - w₁ * u) ^ (-a)

private def affineCircIntegrand (a β γ w₀ w₁ : ℂ) (ρ θ : ℝ) : ℂ :=
  ((ρ : ℂ) ^ (β - 1) * exp (θ * I * (β - 1))) * (1 - ρ * exp (θ * I)) ^ (γ - 1) *
    (w₀ - w₁ * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))

private def affineLoopZero (a β γ w₀ w₁ : ℂ) (A ρ : ℝ) : ℂ :=
  (exp (2 * π * I * (β - 1)) - 1) * (∫ u : ℝ in ρ..A, affineSegIntegrand a β γ w₀ w₁ u) +
    ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a β γ w₀ w₁ ρ θ

private def affineLogIntegrand (a β γ w₀ w₁ : ℂ) (w : ℂ) : ℂ :=
  exp ((β - 1) * w) * (1 - exp w) ^ (γ - 1) * (w₀ - w₁ * exp w) ^ (-a) * exp w

private theorem affineSub_mem_slitPlane_of_closedBall {w₀ w₁ u : ℂ} {ρ : ℝ}
    (hw : closedBall w₀ (‖w₁‖ * ρ) ⊆ slitPlane) (hu : ‖u‖ ≤ ρ) :
    w₀ - w₁ * u ∈ slitPlane := by
  apply hw
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg w₁)

private theorem one_sub_mem_slitPlane_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) :
    1 - u ∈ slitPlane :=
  mem_slitPlane_iff.mpr <| Or.inl <| TauCeti.re_pos_of_norm_sub_one_lt_one <| by
    simpa only [ sub_sub_cancel_left, norm_neg] using hu

private theorem differentiableAt_affineLogIntegrand (a β γ w₀ w₁ : ℂ) {w : ℂ}
    (hw : w.re < 0) (hslit : w₀ - w₁ * exp w ∈ slitPlane) :
    DifferentiableAt ℂ (affineLogIntegrand a β γ w₀ w₁) w := by
  have hexp_lt : ‖exp w‖ < 1 := by
    rw [norm_exp]
    exact exp_lt_one_iff.mpr hw
  have h1 : 1 - exp w ∈ slitPlane := one_sub_mem_slitPlane_of_norm_lt_one hexp_lt
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => 1 - exp z) w :=
    (differentiableAt_const 1).sub differentiableAt_exp
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => w₀ - w₁ * exp z) w :=
    (differentiableAt_const w₀).sub ((differentiableAt_const w₁).mul differentiableAt_exp)
  have hd0 : DifferentiableAt ℂ (fun z : ℂ => exp ((β - 1) * z)) w :=
    ((differentiableAt_const (β - 1)).mul differentiableAt_id).cexp
  exact (((hd0.mul (hd1.cpow (differentiableAt_const _) h1)).mul
    (hd2.cpow (differentiableAt_const _) hslit)).mul differentiableAt_exp)

private theorem I_mul_affineLogIntegrand_vertical (a β γ w₀ w₁ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : ℝ) :
    I * affineLogIntegrand a β γ w₀ w₁ ((Real.log ρ : ℂ) + θ * I) =
      affineCircIntegrand a β γ w₀ w₁ ρ θ := by
  have hcpow : (ρ : ℂ) ^ (β - 1) = exp ((β - 1) * Real.log ρ) := by
    have h := TauCeti.ofReal_exp_cpow (Real.log ρ) (β - 1)
    rwa [Real.exp_log hρ, mul_comm] at h
  have hexp : exp ((Real.log ρ : ℂ) + θ * I) = ρ * exp (θ * I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hρ]
  have hθβ : (β - 1) * (θ * I) = θ * I * (β - 1) := mul_comm _ _
  simp only [affineLogIntegrand, affineCircIntegrand, hexp, hcpow, mul_add, exp_add, hθβ]
  ring

private theorem continuousOn_affineSegIntegrand_Icc (a β γ w₀ w₁ : ℂ) {r s : ℝ}
    (hr : 0 < r) (hs : s < 1) (hslit : ∀ u ∈ Icc r s, w₀ - w₁ * u ∈ slitPlane) :
    ContinuousOn (affineSegIntegrand a β γ w₀ w₁) (Icc r s) := by
  refine continuousOn_of_forall_continuousAt fun u hu => ?_
  have hu0 : (u : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (hr.trans_le hu.1)
  have hu1 : 1 - (u : ℂ) ∈ slitPlane := by
    simpa using ofReal_mem_slitPlane.mpr (sub_pos.mpr (hu.2.trans_lt hs))
  refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
  · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const hu0
  · exact ContinuousAt.cpow (continuousAt_const.sub continuous_ofReal.continuousAt)
      continuousAt_const hu1
  · exact ContinuousAt.cpow
      (continuousAt_const.sub (continuousAt_const.mul continuous_ofReal.continuousAt))
      continuousAt_const (hslit u hu)

private theorem integral_affineLogIntegrand_bottom (a β γ w₀ w₁ : ℂ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hslit : ∀ u ∈ uIcc ρ₁ ρ₂, w₀ - w₁ * u ∈ slitPlane) :
    (∫ x : ℝ in Real.log ρ₁..Real.log ρ₂, affineLogIntegrand a β γ w₀ w₁ x) =
      ∫ u : ℝ in ρ₁..ρ₂, affineSegIntegrand a β γ w₀ w₁ u := by
  have hcont : ContinuousOn (affineSegIntegrand a β γ w₀ w₁)
      (Real.exp '' uIcc (Real.log ρ₁) (Real.log ρ₂)) :=
    (continuousOn_affineSegIntegrand_Icc a β γ w₀ w₁ (lt_min hρ₁ hρ₂) (max_lt hρ₁1 hρ₂1)
      hslit).mono (by
        simpa only [uIcc, Real.exp_log hρ₁, Real.exp_log hρ₂] using
          Real.exp_monotone.image_uIcc_subset (a := Real.log ρ₁) (b := Real.log ρ₂))
  have hsub := intervalIntegral.integral_deriv_smul_comp' (f := Real.exp) (f' := Real.exp)
    (g := affineSegIntegrand a β γ w₀ w₁) (a := Real.log ρ₁) (b := Real.log ρ₂)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hcont
  rw [Real.exp_log hρ₁, Real.exp_log hρ₂] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hpow : exp (x : ℂ) ^ (β - 1) = exp ((β - 1) * x) := by
    rw [← ofReal_exp, TauCeti.ofReal_exp_cpow, mul_comm]
  simp only [Function.comp_apply, real_smul, affineLogIntegrand, affineSegIntegrand, ofReal_exp,
    hpow]
  ring

private theorem integral_affineLogIntegrand_top (a β γ w₀ w₁ : ℂ) {ρ₁ ρ₂ : ℝ} :
    (∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
        affineLogIntegrand a β γ w₀ w₁ ((x : ℂ) + (2 * π : ℝ) * I)) =
      exp (2 * π * I * (β - 1)) *
        ∫ x : ℝ in Real.log ρ₁..Real.log ρ₂, affineLogIntegrand a β γ w₀ w₁ x := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hexp : exp ((x : ℂ) + (2 * π : ℝ) * I) = exp x := by
    rw [exp_add, ofReal_mul, ofReal_ofNat, exp_two_pi_mul_I, mul_one]
  have hβ : exp ((β - 1) * ((x : ℂ) + (2 * π : ℝ) * I)) =
      exp (2 * π * I * (β - 1)) * exp ((β - 1) * x) := by
    rw [← exp_add]; congr 1; push_cast; ring
  simp only [affineLogIntegrand, hexp, hβ]; ring

private theorem affineLoopZero_eq_of_radius (a β γ w₀ w₁ : ℂ) {A ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hw₁ : closedBall w₀ (‖w₁‖ * ρ₁) ⊆ slitPlane)
    (hw₂ : closedBall w₀ (‖w₁‖ * ρ₂) ⊆ slitPlane)
    (hint₁ : IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume ρ₁ A)
    (hint₂ : IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume ρ₂ A) :
    affineLoopZero a β γ w₀ w₁ A ρ₁ = affineLoopZero a β γ w₀ w₁ A ρ₂ := by
  have hw_max : closedBall w₀ (‖w₁‖ * max ρ₁ ρ₂) ⊆ slitPlane := by
    rcases le_total ρ₁ ρ₂ with h | h <;> simp only [max_eq_right, max_eq_left, h, hw₁, hw₂]
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn
    (affineLogIntegrand a β γ w₀ w₁)
    ((Real.log ρ₁ : ℂ) + (0 : ℝ) * I) ((Real.log ρ₂ : ℂ) + (2 * π : ℝ) * I)
    (fun w hw => by
      have hwre : w.re ≤ max (Real.log ρ₁) (Real.log ρ₂) := by
        simpa [mem_reProdIm, uIcc] using hw.1.2
      have hw0 : w.re < 0 :=
        hwre.trans_lt (max_lt (Real.log_neg hρ₁ hρ₁1) (Real.log_neg hρ₂ hρ₂1))
      have hexp_le : ‖exp w‖ ≤ max ρ₁ ρ₂ := by
        rw [norm_exp]
        rcases le_max_iff.mp hwre with h | h
        · exact (Real.exp_le_exp.mpr h).trans ((Real.exp_log hρ₁).le.trans (le_max_left _ _))
        · exact (Real.exp_le_exp.mpr h).trans ((Real.exp_log hρ₂).le.trans (le_max_right _ _))
      exact (differentiableAt_affineLogIntegrand a β γ w₀ w₁ hw0
        (affineSub_mem_slitPlane_of_closedBall hw_max hexp_le)).differentiableWithinAt)
  simp only [add_re, ofReal_re, ofReal_zero, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero,
    mul_one, sub_zero, add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hrect
  have hslit_seg : ∀ u ∈ uIcc ρ₁ ρ₂, w₀ - w₁ * u ∈ slitPlane := fun u hu => by
    apply affineSub_mem_slitPlane_of_closedBall hw_max
    rw [Complex.norm_real, Real.norm_of_nonneg ((lt_min hρ₁ hρ₂).le.trans hu.1)]
    exact hu.2
  have hbot := integral_affineLogIntegrand_bottom a β γ w₀ w₁ hρ₁ hρ₁1 hρ₂ hρ₂1 hslit_seg
  have htop := integral_affineLogIntegrand_top a β γ w₀ w₁ (ρ₁ := ρ₁) (ρ₂ := ρ₂)
  have hvert (ρ : ℝ) (hρ : 0 < ρ) :
      I * (∫ θ : ℝ in 0..(2 * π), affineLogIntegrand a β γ w₀ w₁ ((Real.log ρ : ℂ) + θ * I)) =
        ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a β γ w₀ w₁ ρ θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ =>
      I_mul_affineLogIntegrand_vertical a β γ w₀ w₁ hρ θ
  rw [htop, hbot, hvert ρ₂ hρ₂, hvert ρ₁ hρ₁] at hrect
  have hseg : (∫ u : ℝ in ρ₁..A, affineSegIntegrand a β γ w₀ w₁ u) -
      (∫ u : ℝ in ρ₂..A, affineSegIntegrand a β γ w₀ w₁ u) =
      ∫ u : ℝ in ρ₁..ρ₂, affineSegIntegrand a β γ w₀ w₁ u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint₁.trans hint₂.symm) hint₂]
    ring
  simp only [affineLoopZero]
  linear_combination (exp (2 * π * I * (β - 1)) - 1) * hseg - hrect

private theorem norm_affineCircIntegrand_bound (a β γ w₀ w₁ : ℂ) {ρ : ℝ}
    (hρ1 : ρ < 1) (hw : closedBall w₀ (‖w₁‖ * ρ) ⊆ slitPlane) :
    ∃ K : ℝ, ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ → ∀ θ ∈ Icc 0 (2 * π),
      ‖affineCircIntegrand a β γ w₀ w₁ ρ' θ‖ ≤ K * ρ' ^ β.re := by
  have hcont : ContinuousOn (fun u : ℂ => (1 - u) ^ (γ - 1) * (w₀ - w₁ * u) ^ (-a))
      (closedBall 0 ρ) := by
    refine continuousOn_of_forall_continuousAt fun u hu => ?_
    rw [mem_closedBall_zero_iff] at hu
    exact (ContinuousAt.cpow (continuousAt_const.sub continuousAt_id) continuousAt_const
      (one_sub_mem_slitPlane_of_norm_lt_one (hu.trans_lt hρ1))).mul
      (ContinuousAt.cpow (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
        continuousAt_const (affineSub_mem_slitPlane_of_closedBall hw hu))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hcont
  refine ⟨Real.exp (2 * π * |(β - 1).im|) * M, fun ρ' hρ' hρ'ρ θ hθ => ?_⟩
  have hu_mem : (ρ' : ℂ) * exp (θ * I) ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall_zero_iff, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ'.le]
    exact hρ'ρ
  have hexp_le : ‖exp (θ * I * (β - 1))‖ ≤ Real.exp (2 * π * |(β - 1).im|) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (θ * I * (β - 1)).re = -(θ * (β - 1).im) := by simp
    have habs : |θ * (β - 1).im| ≤ 2 * π * |(β - 1).im| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)
    linarith [neg_abs_le (θ * (β - 1).im)]
  have hpow : ρ' ^ (β - 1).re * ρ' = ρ' ^ β.re := by
    rw [← Real.rpow_add_one hρ'.ne']; congr 1; simp
  have hgrouped : ‖affineCircIntegrand a β γ w₀ w₁ ρ' θ‖ =
      (ρ' ^ (β - 1).re * ‖exp (θ * I * (β - 1))‖) *
        ‖(1 - (ρ' : ℂ) * exp (θ * I)) ^ (γ - 1) *
          (w₀ - w₁ * ((ρ' : ℂ) * exp (θ * I))) ^ (-a)‖ * ρ' := by
    simp only [affineCircIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hρ', norm_I, one_mul,
      norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ'.le]
    ring
  rw [hgrouped]
  calc (ρ' ^ (β - 1).re * ‖exp (θ * I * (β - 1))‖) *
        ‖(1 - (ρ' : ℂ) * exp (θ * I)) ^ (γ - 1) *
          (w₀ - w₁ * ((ρ' : ℂ) * exp (θ * I))) ^ (-a)‖ * ρ'
      ≤ (ρ' ^ (β - 1).re * Real.exp (2 * π * |(β - 1).im|)) * M * ρ' := by
        gcongr; exact hM _ hu_mem
    _ = Real.exp (2 * π * |(β - 1).im|) * M * (ρ' ^ (β - 1).re * ρ') := by ring
    _ = Real.exp (2 * π * |(β - 1).im|) * M * ρ' ^ β.re := by rw [hpow]

private theorem tendsto_integral_affineCircIntegrand_zero (a β γ w₀ w₁ : ℂ) (hβ : 0 < β.re)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hw : closedBall w₀ (‖w₁‖ * ρ) ⊆ slitPlane) :
    Tendsto (fun ρ' : ℝ => ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a β γ w₀ w₁ ρ' θ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK⟩ := norm_affineCircIntegrand_bound a β γ w₀ w₁ hρ1 hw
  refine squeeze_zero_norm' ?_ (by
    simpa [Real.zero_rpow hβ.ne'] using
      (((Real.continuousAt_rpow_const 0 β.re (Or.inr hβ.le)).tendsto.mono_left
        nhdsWithin_le_nhds).const_mul K).mul_const (2 * π))
  filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ'
  calc ‖∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a β γ w₀ w₁ ρ' θ‖
      ≤ (K * ρ' ^ β.re) * |2 * π - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
          rw [uIoc_of_le Real.two_pi_pos.le] at hθ
          exact hK ρ' hρ'.1 hρ'.2.le θ (Ioc_subset_Icc_self hθ)
    _ = K * ρ' ^ β.re * (2 * π) := by rw [sub_zero, abs_of_pos Real.two_pi_pos]

private theorem affineLoopZero_eq_integral (a β γ w₀ w₁ : ℂ) (hβ : 0 < β.re) {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hρA : ρ ≤ A)
    (hw : closedBall w₀ (‖w₁‖ * ρ) ⊆ slitPlane)
    (hint : IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume 0 A) :
    affineLoopZero a β γ w₀ w₁ A ρ =
      (exp (2 * π * I * (β - 1)) - 1) * ∫ u : ℝ in 0..A, affineSegIntegrand a β γ w₀ w₁ u := by
  have hA0 : 0 < A := hρ.trans_le hρA
  let Φ : ℝ → ℂ := fun x => ∫ u : ℝ in x..A, affineSegIntegrand a β γ w₀ w₁ u
  have hΦ_eq : ∀ x ∈ Icc 0 A, Φ x =
      (∫ u : ℝ in 0..A, affineSegIntegrand a β γ w₀ w₁ u) -
        ∫ u : ℝ in 0..x, affineSegIntegrand a β γ w₀ w₁ u := fun x hx => by
    have h1 : IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume 0 x :=
      hint.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hA0.le]; exact Icc_subset_Icc_right hx.2)
    have h2 : IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume x A :=
      hint.mono_set (by rw [uIcc_of_le hx.2, uIcc_of_le hA0.le]; exact Icc_subset_Icc_left hx.1)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]; ring
  have hprim : ContinuousOn (fun x : ℝ => ∫ u : ℝ in 0..x, affineSegIntegrand a β γ w₀ w₁ u)
      (Icc 0 A) := by
    simpa only [uIcc_of_le hA0.le] using
      intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
  have hΦ_lim : Tendsto Φ (𝓝[>] 0) (𝓝 (∫ u : ℝ in 0..A, affineSegIntegrand a β γ w₀ w₁ u)) := by
    have h0 := ((hprim 0 (left_mem_Icc.mpr hA0.le)).mono Ioo_subset_Icc_self).tendsto
    rw [nhdsWithin_Ioo_eq_nhdsGT hA0, intervalIntegral.integral_same] at h0
    have hsub :=
      (tendsto_const_nhds (x := ∫ u : ℝ in 0..A, affineSegIntegrand a β γ w₀ w₁ u)).sub h0
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hA0] with x hx
    exact (hΦ_eq x (Ioo_subset_Icc_self hx)).symm
  have hlim : Tendsto (fun ρ' : ℝ => affineLoopZero a β γ w₀ w₁ A ρ') (𝓝[>] 0)
      (𝓝 ((exp (2 * π * I * (β - 1)) - 1) *
        ∫ u : ℝ in 0..A, affineSegIntegrand a β γ w₀ w₁ u)) := by
    simpa [affineLoopZero, Φ, add_zero] using
      (hΦ_lim.const_mul (exp (2 * π * I * (β - 1)) - 1)).add
        (tendsto_integral_affineCircIntegrand_zero a β γ w₀ w₁ hβ hρ hρ1 hw)
  have hconst : Tendsto (fun ρ' : ℝ => affineLoopZero a β γ w₀ w₁ A ρ') (𝓝[>] 0)
      (𝓝 (affineLoopZero a β γ w₀ w₁ A ρ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ'
    have hint_ρ : ∀ r ∈ Icc 0 A,
        IntervalIntegrable (affineSegIntegrand a β γ w₀ w₁) volume r A := fun r hr =>
      hint.mono_set (by rw [uIcc_of_le hr.2, uIcc_of_le hA0.le]; exact Icc_subset_Icc_left hr.1)
    exact affineLoopZero_eq_of_radius a β γ w₀ w₁ hρ hρ1 hρ'.1 (hρ'.2.trans hρ1) hw
      (Subset.trans (closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_left hρ'.2.le (norm_nonneg w₁))) hw)
      (hint_ρ ρ ⟨hρ.le, hρA⟩) (hint_ρ ρ' ⟨hρ'.1.le, hρ'.2.le.trans hρA⟩)
  exact tendsto_nhds_unique hconst hlim

/-! ### Parametric holomorphy of the internal keyhole pieces -/

private theorem analyticAt_integral_affineCircIntegrand {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {fa fβ fγ fw₀ fw₁ : V → ℂ} {p : V}
    (ha : AnalyticAt ℂ fa p) (hβ : AnalyticAt ℂ fβ p) (hγ : AnalyticAt ℂ fγ p)
    (hw₀ : AnalyticAt ℂ fw₀ p) (hw₁ : AnalyticAt ℂ fw₁ p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hslit : closedBall (fw₀ p) (‖fw₁ p‖ * ρ) ⊆ slitPlane) :
    AnalyticAt ℂ (fun q => ∫ θ : ℝ in 0..(2 * π),
      affineCircIntegrand (fa q) (fβ q) (fγ q) (fw₀ q) (fw₁ q) ρ θ) p := by
  let φ : ℝ → ℂ := fun θ => ((projIcc 0 (2 * π) Real.two_pi_pos.le θ : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc (0 : ℝ) (2 * π)
  have hφ : Continuous φ := continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)
  have hφK (θ : ℝ) : φ θ ∈ K := ⟨_, (projIcc 0 (2 * π) Real.two_pi_pos.le θ).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ (fun x : V × ℂ =>
      ((ρ : ℂ) ^ (fβ x.1 - 1) * exp (x.2 * I * (fβ x.1 - 1))) *
        (1 - ρ * exp (x.2 * I)) ^ (fγ x.1 - 1) *
        (fw₀ x.1 - fw₁ x.1 * (ρ * exp (x.2 * I))) ^ (-fa x.1) *
        (I * ρ * exp (x.2 * I))) (p, y) := by
    rintro _ ⟨θ, _, rfl⟩
    have hu_norm : ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ = ρ := by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have h1 : 1 - (ρ : ℂ) * exp ((θ : ℂ) * I) ∈ slitPlane :=
      one_sub_mem_slitPlane_of_norm_lt_one (hu_norm.trans_lt hρ1)
    have h2 : fw₀ p - fw₁ p * ((ρ : ℂ) * exp ((θ : ℂ) * I)) ∈ slitPlane :=
      affineSub_mem_slitPlane_of_closedBall hslit hu_norm.le
    have hρpow : ∀ q : V × ℂ, (ρ : ℂ) ^ (fβ q.1 - 1) = exp ((fβ q.1 - 1) * Real.log ρ) :=
      fun q => by
        have h := TauCeti.ofReal_exp_cpow (Real.log ρ) (fβ q.1 - 1)
        rwa [Real.exp_log hρ, mul_comm] at h
    simp_rw [hρpow]
    have he : AnalyticAt ℂ (fun x : V × ℂ => exp (x.2 * I)) (p, (θ : ℂ)) :=
      (analyticAt_snd.mul analyticAt_const).cexp
    have hρe : AnalyticAt ℂ (fun x : V × ℂ => (ρ : ℂ) * exp (x.2 * I)) (p, (θ : ℂ)) :=
      analyticAt_const.mul he
    refine ((((((hβ.comp analyticAt_fst).sub analyticAt_const).mul analyticAt_const).cexp.mul
      ((analyticAt_snd.mul analyticAt_const).mul
        ((hβ.comp analyticAt_fst).sub analyticAt_const)).cexp).mul
      ((analyticAt_const.sub hρe).cpow ((hγ.comp analyticAt_fst).sub analyticAt_const) h1)).mul
      (((hw₀.comp analyticAt_fst).sub ((hw₁.comp analyticAt_fst).mul hρe)).cpow
        (ha.comp analyticAt_fst).neg h2)).mul ((analyticAt_const.mul analyticAt_const).mul he)
  have hweight : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ioc 0 (2 * π))) := by simp
  convert TauCeti.analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal) hφ hφK hkernel
    hweight using 1
  ext q
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  simp [φ, projIcc_of_mem Real.two_pi_pos.le (Ioc_subset_Icc_self hθ), affineCircIntegrand]

private theorem analyticAt_integral_affineSegIntegrand_unit {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {fa fβ fw₀ fw₁ : V → ℂ} {γ : ℂ} (hγ : 0 < γ.re)
    {p : V} (ha : AnalyticAt ℂ fa p) (hβ : AnalyticAt ℂ fβ p)
    (hw₀ : AnalyticAt ℂ fw₀ p) (hw₁ : AnalyticAt ℂ fw₁ p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hslit : ∀ u ∈ Icc ρ 1, fw₀ p - fw₁ p * u ∈ slitPlane) :
    AnalyticAt ℂ (fun q => ∫ u : ℝ in ρ..1,
      affineSegIntegrand (fa q) (fβ q) γ (fw₀ q) (fw₁ q) u) p := by
  let φ : ℝ → ℂ := fun u => ((projIcc ρ 1 hρ1.le u : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc ρ 1
  have hφ : Continuous φ := continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)
  have hφK (u : ℝ) : φ u ∈ K := ⟨_, (projIcc ρ 1 hρ1.le u).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ (fun x : V × ℂ =>
      x.2 ^ (fβ x.1 - 1) * (fw₀ x.1 - fw₁ x.1 * x.2) ^ (-fa x.1)) (p, y) := by
    rintro _ ⟨u, hu, rfl⟩
    refine (analyticAt_snd.cpow ((hβ.comp analyticAt_fst).sub analyticAt_const)
      (ofReal_mem_slitPlane.mpr (hρ.trans_le hu.1))).mul ?_
    exact ((hw₀.comp analyticAt_fst).sub ((hw₁.comp analyticAt_fst).mul analyticAt_snd)).cpow
      (ha.comp analyticAt_fst).neg (hslit u hu)
  have hbeta : IntervalIntegrable (fun u : ℝ => (1 - (u : ℂ)) ^ (γ - 1)) volume ρ 1 := by
    have h01 := betaIntegral_convergent (u := 1) (v := γ) one_pos hγ
    simp only [sub_self, cpow_zero, one_mul] at h01
    exact h01.mono_set (by
      rw [uIcc_of_le hρ1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_left hρ.le)
  have hweight := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρ1.le).mp hbeta).integrable
  convert TauCeti.analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal) hφ hφK hkernel
    hweight using 1
  ext q
  rw [intervalIntegral.integral_of_le hρ1.le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simp only [smul_eq_mul, φ, projIcc_of_mem hρ1.le (Ioc_subset_Icc_self hu), affineSegIntegrand]
  ring

private theorem analyticAt_integral_affineSegIntegrand_compact {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {fa fβ fγ fw₀ fw₁ : V → ℂ} {p : V}
    (ha : AnalyticAt ℂ fa p) (hβ : AnalyticAt ℂ fβ p) (hγ : AnalyticAt ℂ fγ p)
    (hw₀ : AnalyticAt ℂ fw₀ p) (hw₁ : AnalyticAt ℂ fw₁ p)
    {ρ A : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ A) (hA1 : A < 1)
    (hslit : ∀ u ∈ Icc ρ A, fw₀ p - fw₁ p * u ∈ slitPlane) :
    AnalyticAt ℂ (fun q => ∫ u : ℝ in ρ..A,
      affineSegIntegrand (fa q) (fβ q) (fγ q) (fw₀ q) (fw₁ q) u) p := by
  let φ : ℝ → ℂ := fun u => ((projIcc ρ A hρA u : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc ρ A
  have hφ : Continuous φ := continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)
  have hφK (u : ℝ) : φ u ∈ K := ⟨_, (projIcc ρ A hρA u).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ (fun x : V × ℂ =>
      x.2 ^ (fβ x.1 - 1) * (1 - x.2) ^ (fγ x.1 - 1) *
        (fw₀ x.1 - fw₁ x.1 * x.2) ^ (-fa x.1)) (p, y) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : 1 - (u : ℂ) ∈ slitPlane := by
      have h1 : (0 : ℝ) < 1 - u := sub_pos.mpr (hu.2.trans_lt hA1)
      simpa using ofReal_mem_slitPlane.mpr h1
    refine ((analyticAt_snd.cpow ((hβ.comp analyticAt_fst).sub analyticAt_const)
      (ofReal_mem_slitPlane.mpr (hρ.trans_le hu.1))).mul
      ((analyticAt_const.sub analyticAt_snd).cpow ((hγ.comp analyticAt_fst).sub analyticAt_const)
        hu1)).mul ?_
    exact ((hw₀.comp analyticAt_fst).sub ((hw₁.comp analyticAt_fst).mul analyticAt_snd)).cpow
      (ha.comp analyticAt_fst).neg (hslit u hu)
  have hweight : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ioc ρ A)) := by simp
  convert TauCeti.analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal) hφ hφK hkernel
    hweight using 1
  ext q
  rw [intervalIntegral.integral_of_le hρA]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simp [φ, projIcc_of_mem hρA (Ioc_subset_Icc_self hu), affineSegIntegrand]

/-! ### Exponential, algebraic, and Gamma reflection helpers -/

private theorem sub_neg_mul_one_sub (z w : ℂ) : 1 - z - -z * (1 - w) = 1 - z * w := by ring

private theorem sub_neg_mul_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ slitPlane) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - z) - (-z) * (u : ℂ) ∈ slitPlane := by
  have heq : (1 - z) - (-z) * (u : ℂ) = 1 - z * (1 - u : ℝ) := by push_cast; ring
  rw [heq]
  exact one_sub_mul_ofReal_mem_slitPlane hz ⟨sub_nonneg.mpr hu1, sub_le_self _ hu0⟩

private theorem exp_two_pi_mul_I_sub_one (x : ℂ) :
    exp (2 * π * I * (x - 1)) = exp (2 * π * I * x) := by
  have h : 2 * (π : ℂ) * I * (x - 1) = 2 * π * I * x - 2 * π * I := by ring
  rw [h, exp_sub, exp_two_pi_mul_I, div_one]

private theorem exp_two_pi_sub_one_eq_sin (x : ℂ) :
    exp (2 * π * I * x) - 1 = 2 * I * exp (x * π * I) * sin (π * x) := by
  have h1 : 2 * (π : ℂ) * I * x = x * π * I + π * x * I := by ring
  have h2 : x * (π : ℂ) * I + -(π * x * I) = 0 := by ring
  have h3 : -(π * x) * I = -(π * x * I) := by ring
  rw [Complex.sin, h3]
  calc exp (2 * π * I * x) - 1
      = exp (x * π * I + π * x * I) - exp (x * π * I + -(π * x * I)) := by rw [h1, h2, exp_zero]
    _ = exp (x * π * I) * exp (π * x * I) - exp (x * π * I) * exp (-(π * x * I)) := by
          rw [exp_add, exp_add]
    _ = 2 * I * exp (x * π * I) * ((exp (-(π * x * I)) - exp (π * x * I)) * I / 2) := by
          ring_nf; rw [I_sq]; ring

private theorem sin_mul_Gamma_eq_pi_div_Gamma_one_sub {x : ℂ} (hx : 0 < x.re) :
    sin (π * x) * Gamma x = π / Gamma (1 - x) := by
  by_cases h0 : Gamma (1 - x) = 0
  · obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff (1 - x)).mp h0
    have hxn : x = (n : ℂ) + 1 := by linear_combination -hn
    have hsin : sin (π * x) = 0 := by
      rw [hxn, mul_add, mul_one, sin_add_pi]
      exact neg_eq_zero.mpr (by simpa [mul_comm] using Complex.sin_nat_mul_pi n)
    rw [h0, div_zero, hsin, zero_mul]
  · have hrefl := Complex.Gamma_mul_Gamma_one_sub x
    have hsin0 : sin (π * x) ≠ 0 := fun hs => by
      rw [hs, div_zero] at hrefl
      exact mul_ne_zero (Gamma_ne_zero_of_re_pos hx) h0 hrefl
    rw [eq_div_iff h0]
    calc sin (π * x) * Gamma x * Gamma (1 - x)
        = (Gamma x * Gamma (1 - x)) * sin (π * x) := by ring
      _ = (π / sin (π * x)) * sin (π * x) := by rw [hrefl]
      _ = π := div_mul_cancel₀ _ hsin0

/-! ### The `(1+)` single-loop integral around `1` (DLMF 15.6.2) -/

/-- The `(1+)` single-loop hypergeometric integral (DLMF 15.6.2) over the keyhole contour of
radius `ρ` around `1`: from `0` to `1 - ρ` below `[1, ∞)` where `ph (t - 1) = -π`, counterclockwise
around `t = 1 + ρ e^{iθ}` (`θ ∈ [-π, π]`) crossing `(1, ∞)` with principal values, and back from
`1 - ρ` to `0` above `[1, ∞)` where `ph (t - 1) = π`. -/
def hypergeometricLoopOne (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (∫ t : ℝ in 0..(1 - ρ),
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * exp (-(π * I * (c - b - 1))) *
        (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in (-π)..π,
      (1 + ρ * exp (θ * I)) ^ (b - 1) * ((ρ : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))) *
        (1 - z * (1 + ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) -
    ∫ t : ℝ in 0..(1 - ρ),
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * exp (π * I * (c - b - 1)) *
        (1 - z * t) ^ (-a)

/-- The explicit three-piece contour formula defining `Complex.hypergeometricLoopOne`. -/
theorem hypergeometricLoopOne_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopOne a b c z ρ =
      (∫ t : ℝ in 0..(1 - ρ),
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * exp (-(π * I * (c - b - 1))) *
            (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in (-π)..π,
          (1 + ρ * exp (θ * I)) ^ (b - 1) *
            ((ρ : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))) *
            (1 - z * (1 + ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) -
        ∫ t : ℝ in 0..(1 - ρ),
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * exp (π * I * (c - b - 1)) *
            (1 - z * t) ^ (-a) := (rfl)

private theorem loopOne_circ_eq_affineCircIntegrand (a b c z : ℂ) (ρ : ℝ) :
    (∫ θ : ℝ in (-π)..π,
        (1 + ρ * exp (θ * I)) ^ (b - 1) * ((ρ : ℂ) ^ (c - b - 1) * exp (θ * I * (c - b - 1))) *
          (1 - z * (1 + ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) =
      exp (-((c - b) * π * I)) *
        ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ φ := by
  have hsub := intervalIntegral.integral_comp_sub_right
    (fun φ : ℝ => (1 + ρ * exp (((φ - π : ℝ) : ℂ) * I)) ^ (b - 1) *
      ((ρ : ℂ) ^ (c - b - 1) * exp (((φ - π : ℝ) : ℂ) * I * (c - b - 1))) *
      (1 - z * (1 + ρ * exp (((φ - π : ℝ) : ℂ) * I))) ^ (-a) *
      (I * ρ * exp (((φ - π : ℝ) : ℂ) * I))) (-π) (a := -π) (b := π)
  have hlim1 : -π - -π = (0 : ℝ) := by ring
  have hlim2 : π - -π = 2 * π := by ring
  simp only [sub_neg_eq_add, add_sub_cancel_right, hlim1, hlim2] at hsub
  rw [hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  have hexpφ : exp (((φ - π : ℝ) : ℂ) * I) = -exp (φ * I) := by
    have h1 : ((φ - π : ℝ) : ℂ) * I = φ * I - π * I := by push_cast; ring
    rw [h1, exp_sub, exp_pi_mul_I, div_neg, div_one]
  have hexp_cb : exp (((φ - π : ℝ) : ℂ) * I * (c - b - 1)) =
      -exp (-((c - b) * π * I)) * exp (φ * I * (c - b - 1)) := by
    have h1 : ((φ - π : ℝ) : ℂ) * I * (c - b - 1) =
        -(((c - b) * π * I) - π * I) + φ * I * (c - b - 1) := by push_cast; ring
    rw [h1, exp_add, neg_sub, sub_eq_add_neg, exp_add, exp_pi_mul_I]; ring
  have hb1 : 1 + (ρ : ℂ) * -exp (φ * I) = 1 - ρ * exp (φ * I) := by ring
  have hb2 : 1 - z * (1 - (ρ : ℂ) * exp (φ * I)) = 1 - z - -z * (ρ * exp (φ * I)) := by ring
  simp only [affineCircIntegrand, hexpφ, hexp_cb, hb1, hb2]; ring

private theorem hypergeometricLoopOne_eq_affineLoopZero (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopOne a b c z ρ =
      exp (-((c - b) * π * I)) * affineLoopZero a (c - b) b (1 - z) (-z) 1 ρ := by
  have hseg (w : ℂ) :
      (∫ t : ℝ in 0..(1 - ρ),
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * exp w * (1 - z * t) ^ (-a)) =
        exp w * ∫ u : ℝ in ρ..1, affineSegIntegrand a (c - b) b (1 - z) (-z) u := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := 0) (b := 1 - ρ)
    rw [sub_sub_cancel, sub_zero] at hsub
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
    ring
  have he1 : exp (-(π * I * (c - b - 1))) = -exp (-((c - b) * π * I)) := by
    have h : -(π * I * (c - b - 1)) = -((c - b) * π * I) + π * I := by ring
    rw [h, exp_add, exp_pi_mul_I]; ring
  have he2 : exp (π * I * (c - b - 1)) =
      -exp (-((c - b) * π * I)) * exp (2 * π * I * (c - b - 1)) := by
    have h : π * I * (c - b - 1) = -((c - b) * π * I) + π * I + 2 * π * I * (c - b - 1) := by
      ring
    rw [h, exp_add, exp_add, exp_pi_mul_I]; ring
  rw [hypergeometricLoopOne_def, hseg (-(π * I * (c - b - 1))), hseg (π * I * (c - b - 1)),
    loopOne_circ_eq_affineCircIntegrand, he1, he2, affineLoopZero]
  ring

private theorem intervalIntegrable_loopOne_seg (a b c z : ℂ) (hb : 0 < b.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume ρ 1 := by
  have hweight : IntervalIntegrable (fun u : ℝ => (1 - (u : ℂ)) ^ (b - 1)) volume ρ 1 := by
    have h01 := betaIntegral_convergent (u := 1) (v := b) one_pos hb
    simp only [sub_self, cpow_zero, one_mul] at h01
    exact h01.mono_set (by
      rw [uIcc_of_le hρ1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left hρ.le)
  have hcont : ContinuousOn
      (fun u : ℝ => (u : ℂ) ^ (c - b - 1) * ((1 - z) - (-z) * u) ^ (-a)) (uIcc ρ 1) := by
    rw [uIcc_of_le hρ1.le]
    refine continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ?_ ?_
    · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
        (ofReal_mem_slitPlane.mpr (hρ.trans_le hu.1))
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (sub_neg_mul_mem_slitPlane hz (hρ.le.trans hu.1) hu.2)
  convert hweight.mul_continuousOn hcont using 1
  ext u; simp only [affineSegIntegrand]; ring

/-- **Radius independence of the `(1+)` loop integral.** Whenever `0 < re b` and the closed disks
around `1` of radii `ρ₁, ρ₂ ∈ (0, 1)` map into the slit plane under `u ↦ 1 - z u`, the loop
integral `Complex.hypergeometricLoopOne` takes the same value at `ρ₁` and `ρ₂`. -/
theorem hypergeometricLoopOne_eq (a b c z : ℂ) (hb : 0 < b.re) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane)
    (hz₂ : closedBall (1 - z) (‖z‖ * ρ₂) ⊆ slitPlane) :
    hypergeometricLoopOne a b c z ρ₁ = hypergeometricLoopOne a b c z ρ₂ := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  rw [hypergeometricLoopOne_eq_affineLoopZero, hypergeometricLoopOne_eq_affineLoopZero]
  congr 1
  exact affineLoopZero_eq_of_radius a (c - b) b (1 - z) (-z) hρ₁ hρ₁1 hρ₂ hρ₂1
    (by simpa only [norm_neg] using hz₁) (by simpa only [norm_neg] using hz₂)
    (intervalIntegrable_loopOne_seg a b c z hb hρ₁ hρ₁1 hz)
    (intervalIntegrable_loopOne_seg a b c z hb hρ₂ hρ₂1 hz)

/-- **Joint holomorphy of the `(1+)` loop integral.** For fixed `b` with `0 < re b` and
`ρ ∈ (0, 1)`, `Complex.hypergeometricLoopOne` is jointly analytic in `(a, c, z)` on the open set
where the closed disk of radius `‖z‖ ρ` around `1 - z` lies in the slit plane. -/
theorem analyticOnNhd_hypergeometricLoopOne {b : ℂ} (hb : 0 < b.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => hypergeometricLoopOne p.1 b p.2.1 p.2.2 ρ)
      {p | closedBall (1 - p.2.2) (‖p.2.2‖ * ρ) ⊆ slitPlane} := by
  intro p hp
  have hz : 1 - p.2.2 ∈ slitPlane := hp (mem_closedBall_self (by positivity))
  have hslit : ∀ u ∈ Icc ρ 1, (1 - p.2.2) - (-p.2.2) * (u : ℂ) ∈ slitPlane := fun u hu =>
    sub_neg_mul_mem_slitPlane hz (hρ.le.trans hu.1) hu.2
  have ha : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hc : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hz_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p := analyticAt_snd.comp analyticAt_snd
  have hcb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1 - b) p := hc.fun_sub analyticAt_const
  have hw₀ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p := analyticAt_const.fun_sub hz_an
  have hw₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => -q.2.2) p := hz_an.fun_neg
  have hseg := analyticAt_integral_affineSegIntegrand_unit hb ha hcb hw₀ hw₁ hρ hρ1 hslit
  have hcirc := analyticAt_integral_affineCircIntegrand (fγ := fun _ => b) ha hcb
    analyticAt_const hw₀ hw₁ hρ hρ1 (by simpa only [mem_ofPred_eq, norm_neg] using hp)
  have haff : AnalyticAt ℂ
      (fun q : ℂ × ℂ × ℂ => affineLoopZero q.1 (q.2.1 - b) b (1 - q.2.2) (-q.2.2) 1 ρ) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.1 - b - 1)) - 1) p).fun_mul hseg).fun_add hcirc
  have hpref : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => exp (-((q.2.1 - b) * π * I))) p := by fun_prop
  exact (hpref.fun_mul haff).congr (Eventually.of_forall fun q => by
    dsimp only
    exact (hypergeometricLoopOne_eq_affineLoopZero q.1 b q.2.1 q.2.2 ρ).symm)

/-- **Collapsing the `(1+)` loop onto `[0, 1]`.** When `0 < re b < re c`, the `(1+)` loop integral
equals `2 i sin(π (c - b))` times the unnormalized Euler integral over `[0, 1]`. -/
theorem hypergeometricLoopOne_eq_integral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hz : closedBall (1 - z) (‖z‖ * ρ) ⊆ slitPlane) :
    hypergeometricLoopOne a b c z ρ =
      2 * I * sin (π * (c - b)) *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := by
  have hz_slit : 1 - z ∈ slitPlane := hz (mem_closedBall_self (by positivity))
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hint : IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume 0 1 :=
    (betaIntegral_convergent hcb hb).mul_continuousOn (by
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_of_forall_continuousAt fun u hu =>
        ContinuousAt.cpow (by fun_prop) continuousAt_const
          (sub_neg_mul_mem_slitPlane hz_slit hu.1 hu.2))
  rw [hypergeometricLoopOne_eq_affineLoopZero,
    affineLoopZero_eq_integral a (c - b) b (1 - z) (-z) hcb hρ hρ1 hρ1.le
      (by simpa only [norm_neg] using hz) hint]
  have hcov : (∫ u : ℝ in 0..1, affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := 0) (b := 1)
    rw [sub_self, sub_zero] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
    ring
  rw [hcov, exp_two_pi_mul_I_sub_one, exp_two_pi_sub_one_eq_sin, ← mul_assoc]
  congr 1
  calc exp (-((c - b) * π * I)) * (2 * I * exp ((c - b) * π * I) * sin (π * (c - b)))
      = 2 * I * (exp (-((c - b) * π * I)) * exp ((c - b) * π * I)) * sin (π * (c - b)) := by ring
    _ = 2 * I * sin (π * (c - b)) := by rw [← exp_add, neg_add_cancel, exp_zero, mul_one]

/-- When `0 < re b < re c`, the `(1+)` loop integral is `(2πi Γ(b) / Γ(1 + b - c))` times
`Complex.eulerIntegral`, including at positive integer values of `c - b` where both sides
vanish. -/
theorem hypergeometricLoopOne_eq_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : closedBall (1 - z) (‖z‖ * ρ) ⊆ slitPlane) :
    hypergeometricLoopOne a b c z ρ =
      2 * π * I * Gamma b / Gamma (1 + b - c) * eulerIntegral a b c z := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hrefl := sin_mul_Gamma_eq_pi_div_Gamma_one_sub hcb
  have h1cb : 1 - (c - b) = 1 + b - c := by ring
  rw [h1cb] at hrefl
  rw [hypergeometricLoopOne_eq_integral a hb hbc hρ hρ1 hz, eulerIntegral_def]
  set E := ∫ t : ℝ in 0..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
  have hE : E = Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E) := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hGb hGcb), one_mul]
  conv_lhs => rw [hE]
  calc 2 * I * sin (π * (c - b)) * (Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E))
      = 2 * I * Gamma b * (sin (π * (c - b)) * Gamma (c - b)) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by ring
    _ = 2 * π * I * Gamma b / Gamma (1 + b - c) * ((Gamma b * Gamma (c - b))⁻¹ * E) := by
          rw [hrefl]; ring

/-- **DLMF 15.6.2 in the Euler convergence region.** For `0 < re b < re c` and
`c - b ∉ {1, 2, …}`, `Complex.eulerIntegral` is represented on the cut plane by the `(1+)` loop
integral around `1`. -/
theorem eulerIntegral_eq_hypergeometricLoopOne (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hcb : ∀ n : ℕ, c - b ≠ n + 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : closedBall (1 - z) (‖z‖ * ρ) ⊆ slitPlane) :
    eulerIntegral a b c z =
      Gamma (1 + b - c) / (2 * π * I * Gamma b) * hypergeometricLoopOne a b c z ρ := by
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hG1 : Gamma (1 + b - c) ≠ 0 := Gamma_ne_zero fun n hn => hcb n (by linear_combination -hn)
  rw [hypergeometricLoopOne_eq_eulerIntegral a hb hbc hρ hρ1 hz]
  field_simp

/-- At zero argument the `(1+)` loop integral evaluates in closed form for all complex `a` and `c`
whenever `0 < re b` and `ρ ∈ (0, 1)`. -/
@[simp]
theorem hypergeometricLoopOne_zero (a : ℂ) {b : ℂ} (hb : 0 < b.re) (c : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopOne a b c 0 ρ =
      2 * π * I * Gamma b / (Gamma (1 + b - c) * Gamma c) := by
  have h0 : closedBall (1 - (0 : ℂ)) (‖(0 : ℂ)‖ * ρ) ⊆ slitPlane := by simp [one_mem_slitPlane]
  have han₁ : AnalyticOnNhd ℂ (fun w : ℂ => hypergeometricLoopOne a b w 0 ρ) univ := fun w _ =>
    (analyticOnNhd_hypergeometricLoopOne hb hρ hρ1 (a, w, 0) h0).comp₂
      analyticAt_const (analyticAt_id.prod analyticAt_const)
  have hG (s : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt s
  have han₂ : AnalyticOnNhd ℂ
      (fun w : ℂ => 2 * π * I * Gamma b / (Gamma (1 + b - w) * Gamma w)) univ := fun w _ => by
    simp_rw [div_eq_mul_inv, mul_inv]
    exact analyticAt_const.mul (((hG _).comp (analyticAt_const.sub analyticAt_id)).mul (hG w))
  refine congrFun (han₁.eq_of_eventuallyEq han₂ (z₀ := b + 1) ?_) c
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
    (by simp : b.re < (b + 1).re)] with w hw
  rw [hypergeometricLoopOne_eq_eulerIntegral a hb hw hρ hρ1 h0, eulerIntegral_zero a hb hw,
    ← div_eq_mul_inv, div_div]

/-- With first parameter zero, the `(1+)` loop integral is independent of `z` and evaluates in
closed form for all complex `c` and `z` whenever `0 < re b` and `ρ ∈ (0, 1)`. -/
@[simp]
theorem hypergeometricLoopOne_zero_left {b : ℂ} (hb : 0 < b.re) (c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopOne 0 b c z ρ =
      2 * π * I * Gamma b / (Gamma (1 + b - c) * Gamma c) := by
  have heq : hypergeometricLoopOne 0 b c z ρ = hypergeometricLoopOne 0 b c 0 ρ := by
    simp only [hypergeometricLoopOne_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricLoopOne_zero 0 hb c hρ hρ1]

/-! ### The `(0+)` single-loop integral around `0` (DLMF 15.6.4) -/

/-- The `(0+)` single-loop hypergeometric integral (DLMF 15.6.4) over the keyhole contour of
radius `ρ` around `0`: from `1` to `ρ` with `ph t = 0` and `ph (1 - t) = 0`, counterclockwise
around `t = ρ e^{iθ}` (`θ ∈ [0, 2π]`) cutting the negative real axis with `ph t = π` and
`ph (1 - t) = 0`, and back from `ρ` to `1` with `ph t = 2π` and `ph (1 - t) = 0`. -/
def hypergeometricLoopZero (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (∫ t : ℝ in 1..ρ,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in 0..(2 * π),
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) +
    ∫ t : ℝ in ρ..1,
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)

/-- The explicit three-piece contour formula defining `Complex.hypergeometricLoopZero`. -/
theorem hypergeometricLoopZero_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopZero a b c z ρ =
      (∫ t : ℝ in 1..ρ,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in 0..(2 * π),
          ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
            (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
            (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) +
        ∫ t : ℝ in ρ..1,
          (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (1 - z * t) ^ (-a) := (rfl)

private theorem hypergeometricLoopZero_eq_affineLoopZero (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopZero a b c z ρ = affineLoopZero a b (c - b) 1 z 1 ρ := by
  have h1 : (∫ t : ℝ in 1..ρ,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      -∫ t : ℝ in ρ..1, affineSegIntegrand a b (c - b) 1 z t :=
    intervalIntegral.integral_symm ρ 1
  have h2 : (∫ t : ℝ in ρ..1,
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      exp (2 * π * I * (b - 1)) * ∫ t : ℝ in ρ..1, affineSegIntegrand a b (c - b) 1 z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  rw [hypergeometricLoopZero_def, h1, h2, affineLoopZero]
  dsimp only [affineCircIntegrand]; ring

private theorem closedBall_one_subset_slitPlane {r : ℝ} (hr : r < 1) :
    closedBall (1 : ℂ) r ⊆ slitPlane := fun _ hw =>
  mem_slitPlane_iff.mpr <| Or.inl <| TauCeti.re_pos_of_norm_sub_one_lt_one <|
    (mem_closedBall_iff_norm.mp hw).trans_lt hr

private theorem intervalIntegrable_loopZero_seg (a b c z : ℂ) (hcb : 0 < (c - b).re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume ρ 1 := by
  have hweight : IntervalIntegrable (fun u : ℝ => (1 - (u : ℂ)) ^ (c - b - 1)) volume ρ 1 := by
    have h01 := betaIntegral_convergent (u := 1) (v := c - b) one_pos hcb
    simp only [sub_self, cpow_zero, one_mul] at h01
    exact h01.mono_set (by
      rw [uIcc_of_le hρ1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left hρ.le)
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - z * u) ^ (-a)) (uIcc ρ 1) := by
    rw [uIcc_of_le hρ1.le]
    refine continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ?_ ?_
    · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
        (ofReal_mem_slitPlane.mpr (hρ.trans_le hu.1))
    · exact ContinuousAt.cpow
        (continuousAt_const.sub (continuousAt_const.mul continuous_ofReal.continuousAt))
        continuousAt_const (one_sub_mul_ofReal_mem_slitPlane hz ⟨hρ.le.trans hu.1, hu.2⟩)
  convert hweight.mul_continuousOn hcont using 1
  ext u; simp only [affineSegIntegrand]; ring

/-- **Radius independence of the `(0+)` loop integral.** Whenever `re b < re c`,
`1 - z ∈ Complex.slitPlane`, and `ρ₁, ρ₂ ∈ (0, 1)` satisfy `‖z‖ ρᵢ < 1`, the `(0+)` loop integral
`Complex.hypergeometricLoopZero` takes the same value at `ρ₁` and `ρ₂`. -/
theorem hypergeometricLoopZero_eq (a b c z : ℂ) (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1) :
    hypergeometricLoopZero a b c z ρ₁ = hypergeometricLoopZero a b c z ρ₂ := by
  have hcb : 0 < (c - b).re := by simpa only [sub_re, sub_pos] using hbc
  rw [hypergeometricLoopZero_eq_affineLoopZero, hypergeometricLoopZero_eq_affineLoopZero]
  exact affineLoopZero_eq_of_radius a b (c - b) 1 z hρ₁ hρ₁1 hρ₂ hρ₂1
    (closedBall_one_subset_slitPlane hz₁) (closedBall_one_subset_slitPlane hz₂)
    (intervalIntegrable_loopZero_seg a b c z hcb hρ₁ hρ₁1 hz)
    (intervalIntegrable_loopZero_seg a b c z hcb hρ₂ hρ₂1 hz)

/-- **Joint holomorphy of the `(0+)` loop integral along lines of fixed `c - b`.** For fixed `d`
with `0 < re d` and `ρ ∈ (0, 1)`, `(a, b, z) ↦ hypergeometricLoopZero a b (b + d) z ρ` is jointly
analytic on `{p | 1 - p.2.2 ∈ slitPlane ∧ ‖p.2.2‖ * ρ < 1}`. -/
theorem analyticOnNhd_hypergeometricLoopZero {d : ℂ} (hd : 0 < d.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => hypergeometricLoopZero p.1 p.2.1 (p.2.1 + d) p.2.2 ρ)
      {p | 1 - p.2.2 ∈ slitPlane ∧ ‖p.2.2‖ * ρ < 1} := by
  intro p hp
  have hslit : ∀ u ∈ Icc ρ 1, (1 : ℂ) - p.2.2 * (u : ℂ) ∈ slitPlane := fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hp.1 ⟨hρ.le.trans hu.1, hu.2⟩
  have ha : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p := analyticAt_snd.comp analyticAt_snd
  have hseg := analyticAt_integral_affineSegIntegrand_unit (fw₀ := fun _ => 1) hd ha hb
    analyticAt_const hz hρ hρ1 hslit
  have hcirc := analyticAt_integral_affineCircIntegrand (fγ := fun _ => d) (fw₀ := fun _ => 1)
    ha hb analyticAt_const analyticAt_const hz hρ hρ1 (closedBall_one_subset_slitPlane hp.2)
  have haff : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => affineLoopZero q.1 q.2.1 d 1 q.2.2 1 ρ) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.1 - 1)) - 1) p).fun_mul hseg).fun_add hcirc
  exact haff.congr (Eventually.of_forall fun q => by
    dsimp only
    rw [hypergeometricLoopZero_eq_affineLoopZero, add_sub_cancel_left])

/-- **Collapsing the `(0+)` loop onto `[0, 1]`.** When `0 < re b < re c`, the `(0+)` loop integral
equals `(e^{2πi b} - 1)` times the unnormalized Euler integral over `[0, 1]`. -/
theorem hypergeometricLoopZero_eq_integral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopZero a b c z ρ =
      (exp (2 * π * I * b) - 1) *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := by
  have hint : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume 0 1 :=
    intervalIntegrable_eulerIntegrand a hb hbc hz
  rw [hypergeometricLoopZero_eq_affineLoopZero,
    affineLoopZero_eq_integral a b (c - b) 1 z hb hρ hρ1 hρ1.le
      (closedBall_one_subset_slitPlane hzρ) hint,
    exp_two_pi_mul_I_sub_one]
  rfl

/-- When `0 < re b < re c`, the `(0+)` loop integral is
`(2πi e^{bπi} Γ(c - b) / Γ(1 - b))` times `Complex.eulerIntegral`, including at positive integer
values of `b` where both sides vanish. -/
theorem hypergeometricLoopZero_eq_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopZero a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) * eulerIntegral a b c z := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hrefl := sin_mul_Gamma_eq_pi_div_Gamma_one_sub hb
  rw [hypergeometricLoopZero_eq_integral a hb hbc hz hρ hρ1 hzρ, exp_two_pi_sub_one_eq_sin,
    eulerIntegral_def]
  set E := ∫ t : ℝ in 0..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
  have hE : E = Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E) := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hGb hGcb), one_mul]
  conv_lhs => rw [hE]
  calc 2 * I * exp (b * π * I) * sin (π * b) *
        (Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E))
      = 2 * I * exp (b * π * I) * Gamma (c - b) * (sin (π * b) * Gamma b) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by ring
    _ = 2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by rw [hrefl]; ring

/-- **DLMF 15.6.4 in the Euler convergence region.** For `0 < re b < re c` and `b ∉ {1, 2, …}`,
`Complex.eulerIntegral` is represented on the cut plane by the `(0+)` loop integral around `0`. -/
theorem eulerIntegral_eq_hypergeometricLoopZero (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    eulerIntegral a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopZero a b c z ρ := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hG1b : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun n hn => hb_int n (by linear_combination -hn)
  rw [hypergeometricLoopZero_eq_eulerIntegral a hb hbc hz hρ hρ1 hzρ]
  have hexp : exp (-(b * π * I)) * exp (b * π * I) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  field_simp
  linear_combination (eulerIntegral a b c z) * hexp.symm

/-- At zero argument the `(0+)` loop integral evaluates in closed form for all complex `a` and `b`
whenever `re b < re c` and `ρ ∈ (0, 1)`. -/
@[simp]
theorem hypergeometricLoopZero_zero (a : ℂ) {b c : ℂ} (hbc : b.re < c.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopZero a b c 0 ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  have hcb : 0 < (c - b).re := by simpa only [sub_re, sub_pos] using hbc
  set d := c - b
  have hc_eq : c = b + d := by simp [d]
  rw [hc_eq]
  have h0 : 1 - (0 : ℂ) ∈ slitPlane ∧ ‖(0 : ℂ)‖ * ρ < 1 := by simp [one_mem_slitPlane]
  have han₁ : AnalyticOnNhd ℂ (fun w : ℂ => hypergeometricLoopZero a w (w + d) 0 ρ) univ :=
    fun w _ => (analyticOnNhd_hypergeometricLoopZero hcb hρ hρ1 (a, w, 0) h0).comp₂
      analyticAt_const (analyticAt_id.prod analyticAt_const)
  have hG (s : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt s
  have han₂ : AnalyticOnNhd ℂ
      (fun w : ℂ => 2 * π * I * exp (w * π * I) * Gamma d /
        (Gamma (1 - w) * Gamma (w + d))) univ := fun w _ => by
    simp_rw [div_eq_mul_inv, mul_inv]
    exact ((analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).mul
      analyticAt_const).cexp).mul analyticAt_const).mul
      (((hG _).comp (analyticAt_const.sub analyticAt_id)).mul
        ((hG _).comp (analyticAt_id.add analyticAt_const)))
  refine congrFun (han₁.eq_of_eventuallyEq han₂ (z₀ := 1) ?_) b
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
    (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
  have hwd : w.re < (w + d).re := by simpa only [add_re, lt_add_iff_pos_right] using hcb
  rw [hypergeometricLoopZero_eq_eulerIntegral a hw hwd h0.1 hρ hρ1 h0.2,
    eulerIntegral_zero a hw hwd, add_sub_cancel_left, ← div_eq_mul_inv, div_div]

/-- With first parameter zero, the `(0+)` loop integral is independent of `z` and evaluates in
closed form for all complex `b` and `z` whenever `re b < re c` and `ρ ∈ (0, 1)`. -/
@[simp]
theorem hypergeometricLoopZero_zero_left {b c : ℂ} (hbc : b.re < c.re) (z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopZero 0 b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  have heq : hypergeometricLoopZero 0 b c z ρ = hypergeometricLoopZero 0 b c 0 ρ := by
    simp only [hypergeometricLoopZero_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricLoopZero_zero 0 hbc hρ hρ1]

/-! ### Pochhammer's `(0+, 1+, 0-, 1-)` double-loop integral (DLMF 15.6.5) -/

/-- Pochhammer's double-loop contour integral `(0+, 1+, 0-, 1-)` (DLMF 15.6.5) starting and
terminating at `A ∈ (0, 1)` where `ph t = 0` and `ph (1 - t) = 0`, with circle radii `ρ₀` around
`0` and `ρ₁` around `1`. -/
def hypergeometricPochhammerLoop (a b c z : ℂ) (A ρ₀ ρ₁ : ℝ) : ℂ :=
  (∫ t : ℝ in A..ρ₀,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in 0..(2 * π),
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
    (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) +
    (∫ φ : ℝ in 0..(2 * π),
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
        ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
    (∫ t : ℝ in (1 - ρ₁)..ρ₀,
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
        ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) * (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in (2 * π)..0,
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
    (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
        (1 - z * t) ^ (-a)) +
    (∫ φ : ℝ in (2 * π)..0,
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
        ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
    ∫ t : ℝ in (1 - ρ₁)..A,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)

/-- The explicit nine-piece contour formula defining `Complex.hypergeometricPochhammerLoop`. -/
theorem hypergeometricPochhammerLoop_def (a b c z : ℂ) (A ρ₀ ρ₁ : ℝ) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      (∫ t : ℝ in A..ρ₀,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in 0..(2 * π),
          ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
            (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
            (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
        (∫ t : ℝ in ρ₀..(1 - ρ₁),
          (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (1 - z * t) ^ (-a)) +
        (∫ φ : ℝ in 0..(2 * π),
          (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
            ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
            (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
        (∫ t : ℝ in (1 - ρ₁)..ρ₀,
          (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
            ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in (2 * π)..0,
          ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
            ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
        (∫ t : ℝ in ρ₀..(1 - ρ₁),
          (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * t) ^ (-a)) +
        (∫ φ : ℝ in (2 * π)..0,
          (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
            ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
            (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
        ∫ t : ℝ in (1 - ρ₁)..A,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := (rfl)

private theorem pochhammer_seg_split (a b c z : ℂ) (hz : 1 - z ∈ slitPlane)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    (∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t) =
      (∫ t : ℝ in ρ₀..A, affineSegIntegrand a b (c - b) 1 z t) +
        ∫ u : ℝ in ρ₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u := by
  have h1ρ₁ : 1 - ρ₁ < 1 := by linarith
  have hcont := continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hρ₀ h1ρ₁ fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hρ₀.le.trans hu.1, hu.2.trans h1ρ₁.le⟩
  have hint_left : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume ρ₀ A :=
    (hcont.mono (by
      rw [uIcc_of_le hρ₀A.le]; exact Icc_subset_Icc_right (by linarith))).intervalIntegrable
  have hint_right : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume A (1 - ρ₁) :=
    (hcont.mono (by
      rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc_left hρ₀A.le)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_left hint_right]
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left
    (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1 - ρ₁)
  rw [sub_sub_cancel] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
  ring

private theorem pochhammer_circ_sum (a b c z : ℂ) (ρ₀ ρ₁ : ℝ) :
    (∫ θ : ℝ in 0..(2 * π),
        ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
          (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
      (∫ φ : ℝ in 0..(2 * π),
        (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
          ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
          (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
      (∫ θ : ℝ in (2 * π)..0,
        ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
          ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
          (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
      (∫ φ : ℝ in (2 * π)..0,
        (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
          ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
          (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      (1 - exp (2 * π * I * (c - b - 1))) *
          (∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ) +
        (1 - exp (2 * π * I * (b - 1))) *
          ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
  set eb := exp (2 * π * I * (b - 1))
  set ecb := exp (2 * π * I * (c - b - 1))
  have hc2 : (∫ θ : ℝ in 0..(2 * π),
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) =
      ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ := rfl
  have hc4 : (∫ φ : ℝ in 0..(2 * π),
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * eb * ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      -eb * ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hb : (1 - z) - (-z) * ((ρ₁ : ℂ) * exp (φ * I)) = 1 - z * (1 - ρ₁ * exp (φ * I)) := by ring
    simp only [affineCircIntegrand, hb]; ring
  have hc6 : (∫ θ : ℝ in (2 * π)..0,
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * ecb) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) =
      -ecb * ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ := by
    rw [intervalIntegral.integral_symm, neg_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [affineCircIntegrand]; ring
  have hc8 : (∫ φ : ℝ in (2 * π)..0,
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hb : (1 - z) - (-z) * ((ρ₁ : ℂ) * exp (φ * I)) = 1 - z * (1 - ρ₁ * exp (φ * I)) := by ring
    simp only [affineCircIntegrand, hb]; ring
  rw [hc2, hc4, hc6, hc8]
  ring

private theorem hypergeometricPochhammerLoop_eq_affineLoopZero (a b c z : ℂ)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz : 1 - z ∈ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      (1 - exp (2 * π * I * (c - b - 1))) * affineLoopZero a b (c - b) 1 z A ρ₀ +
        (1 - exp (2 * π * I * (b - 1))) *
          affineLoopZero a (c - b) b (1 - z) (-z) (1 - A) ρ₁ := by
  set eb := exp (2 * π * I * (b - 1))
  set ecb := exp (2 * π * I * (c - b - 1))
  have hs1 : (∫ t : ℝ in A..ρ₀,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      -∫ t : ℝ in ρ₀..A, affineSegIntegrand a b (c - b) 1 z t :=
    intervalIntegral.integral_symm ρ₀ A
  have hs3 : (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * eb * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      eb * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs5 : (∫ t : ℝ in (1 - ρ₁)..ρ₀,
      (t : ℂ) ^ (b - 1) * eb * ((1 - (t : ℂ)) ^ (c - b - 1) * ecb) * (1 - z * t) ^ (-a)) =
      -(eb * ecb) * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [intervalIntegral.integral_symm, neg_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs7 : (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * ecb) * (1 - z * t) ^ (-a)) =
      ecb * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs9 : (∫ t : ℝ in (1 - ρ₁)..A,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      -∫ u : ℝ in ρ₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u := by
    rw [intervalIntegral.integral_symm]
    congr 1
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1 - ρ₁)
    rw [sub_sub_cancel] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
    ring
  have hcirc := pochhammer_circ_sum a b c z ρ₀ ρ₁
  rw [hypergeometricPochhammerLoop_def, hs1, hs3, hs5, hs7, hs9,
    pochhammer_seg_split a b c z hz hρ₀ hρ₀A hρ₁ hρ₁A, affineLoopZero, affineLoopZero]
  linear_combination hcirc

private theorem pochhammer_change_radii (a b c z : ℂ) {A ρ₀ ρ₀' ρ₁ ρ₁' : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₀' : 0 < ρ₀') (hρ₀'A : ρ₀' < A)
    (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) (hρ₁' : 0 < ρ₁') (hρ₁'A : ρ₁' < 1 - A)
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₀' : ‖z‖ * ρ₀' < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane)
    (hz₁' : closedBall (1 - z) (‖z‖ * ρ₁') ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop a b c z A ρ₀' ρ₁' := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  have hA1 : A < 1 := by linarith
  have h1A1 : 1 - A < 1 := by linarith
  have hint₀ (r : ℝ) (hr : 0 < r) (hrA : r < A) :
      IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume r A :=
    (continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hr hA1 fun u hu =>
      one_sub_mul_ofReal_mem_slitPlane hz
        ⟨hr.le.trans hu.1, hu.2.trans hA1.le⟩).intervalIntegrable_of_Icc hrA.le
  have hint₁ (r : ℝ) (hr : 0 < r) (hrA : r < 1 - A) :
      IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume r (1 - A) :=
    (continuousOn_affineSegIntegrand_Icc a (c - b) b (1 - z) (-z) hr h1A1 fun u hu =>
      sub_neg_mul_mem_slitPlane hz (hr.le.trans hu.1)
        (hu.2.trans h1A1.le)).intervalIntegrable_of_Icc hrA.le
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀ hρ₀A hρ₁ hρ₁A hz,
    hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀' hρ₀'A hρ₁' hρ₁'A hz,
    affineLoopZero_eq_of_radius a b (c - b) 1 z hρ₀ (hρ₀A.trans hA1) hρ₀' (hρ₀'A.trans hA1)
      (closedBall_one_subset_slitPlane hz₀) (closedBall_one_subset_slitPlane hz₀')
      (hint₀ ρ₀ hρ₀ hρ₀A) (hint₀ ρ₀' hρ₀' hρ₀'A),
    affineLoopZero_eq_of_radius a (c - b) b (1 - z) (-z) hρ₁ (hρ₁A.trans h1A1) hρ₁'
      (hρ₁'A.trans h1A1) (by simpa only [norm_neg] using hz₁)
      (by simpa only [norm_neg] using hz₁') (hint₁ ρ₁ hρ₁ hρ₁A) (hint₁ ρ₁' hρ₁' hρ₁'A)]

private theorem pochhammer_change_basepoint (a b c z : ℂ) (hz : 1 - z ∈ slitPlane)
    {A A' r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₀A : r₀ < A) (hr₀A' : r₀ < A')
    (hr₁ : 0 < r₁) (hr₁A : r₁ < 1 - A) (hr₁A' : r₁ < 1 - A') :
    hypergeometricPochhammerLoop a b c z A r₀ r₁ =
      hypergeometricPochhammerLoop a b c z A' r₀ r₁ := by
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hr₀ hr₀A hr₁ hr₁A hz,
    hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hr₀ hr₀A' hr₁ hr₁A' hz]
  have hAA' : max A A' < 1 := max_lt (by linarith) (by linarith)
  have h1AA' : max (1 - A) (1 - A') < 1 := max_lt (by linarith) (by linarith)
  have hcont₀ := continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hr₀ hAA' fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hr₀.le.trans hu.1, hu.2.trans hAA'.le⟩
  have hcont₁ := continuousOn_affineSegIntegrand_Icc a (c - b) b (1 - z) (-z) hr₁ h1AA'
    fun u hu => sub_neg_mul_mem_slitPlane hz (hr₁.le.trans hu.1) (hu.2.trans h1AA'.le)
  have hsplit₀ : (∫ u : ℝ in r₀..A', affineSegIntegrand a b (c - b) 1 z u) =
      (∫ u : ℝ in r₀..A, affineSegIntegrand a b (c - b) 1 z u) +
        ∫ u : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z u :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hcont₀.mono (by
        rw [uIcc_of_le hr₀A.le]
        exact Icc_subset_Icc_right (le_max_left A A'))).intervalIntegrable (μ := volume))
      ((hcont₀.mono (by
        rw [uIcc]
        exact Icc_subset_Icc (le_min hr₀A.le hr₀A'.le) le_rfl)).intervalIntegrable
          (μ := volume))).symm
  have hsplit₁ : (∫ u : ℝ in r₁..(1 - A'), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
      (∫ u : ℝ in r₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u) -
        ∫ u : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z u := by
    have hadj := (intervalIntegral.integral_add_adjacent_intervals
      ((hcont₁.mono (by
        rw [uIcc_of_le hr₁A.le]
        exact Icc_subset_Icc_right (le_max_left _ _))).intervalIntegrable (μ := volume))
      ((hcont₁.mono (by
        rw [uIcc]
        exact Icc_subset_Icc (le_min hr₁A.le hr₁A'.le) le_rfl)).intervalIntegrable
          (μ := volume))).symm
    rw [hadj]
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A') (b := A)
    have hcov : (∫ u : ℝ in (1 - A)..(1 - A'), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
        -∫ t : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z t := by
      rw [← hsub, intervalIntegral.integral_symm A A']
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
      ring
    rw [hcov]; ring
  simp only [affineLoopZero, hsplit₀, hsplit₁]
  ring

/-- **Independence of the basepoint and radii for Pochhammer's contour.** For all complex
parameters `a, b, c`, any basepoints `A, A'` and admissible loop radii `(ρ₀, ρ₁)`, `(ρ₀', ρ₁')`,
`Complex.hypergeometricPochhammerLoop` takes the same value. -/
theorem hypergeometricPochhammerLoop_eq (a b c z : ℂ) {A A' ρ₀ ρ₀' ρ₁ ρ₁' : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hρ₀' : 0 < ρ₀') (hρ₀'A : ρ₀' < A') (hρ₁' : 0 < ρ₁') (hρ₁'A : ρ₁' < 1 - A')
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₀' : ‖z‖ * ρ₀' < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane)
    (hz₁' : closedBall (1 - z) (‖z‖ * ρ₁') ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop a b c z A' ρ₀' ρ₁' := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  set r₀ := min ρ₀ ρ₀' / 2
  set r₁ := min ρ₁ ρ₁' / 2
  have hr₀ : 0 < r₀ := half_pos (lt_min hρ₀ hρ₀')
  have hr₁ : 0 < r₁ := half_pos (lt_min hρ₁ hρ₁')
  have hr₀_le : r₀ ≤ ρ₀ := (half_lt_self (lt_min hρ₀ hρ₀')).le.trans (min_le_left _ _)
  have hr₁_le : r₁ ≤ ρ₁ := (half_lt_self (lt_min hρ₁ hρ₁')).le.trans (min_le_left _ _)
  have hr₀A : r₀ < A := hr₀_le.trans_lt hρ₀A
  have hr₀A' : r₀ < A' :=
    ((half_lt_self (lt_min hρ₀ hρ₀')).le.trans (min_le_right _ _)).trans_lt hρ₀'A
  have hr₁A : r₁ < 1 - A := hr₁_le.trans_lt hρ₁A
  have hr₁A' : r₁ < 1 - A' :=
    ((half_lt_self (lt_min hρ₁ hρ₁')).le.trans (min_le_right _ _)).trans_lt hρ₁'A
  have hzr₀ : ‖z‖ * r₀ < 1 := (mul_le_mul_of_nonneg_left hr₀_le (norm_nonneg z)).trans_lt hz₀
  have hzr₁ : closedBall (1 - z) (‖z‖ * r₁) ⊆ slitPlane :=
    Subset.trans (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hr₁_le (norm_nonneg z)))
      hz₁
  rw [pochhammer_change_radii a b c z hρ₀ hρ₀A hr₀ hr₀A hρ₁ hρ₁A hr₁ hr₁A hz₀ hzr₀ hz₁ hzr₁,
    pochhammer_change_radii a b c z hρ₀' hρ₀'A hr₀ hr₀A' hρ₁' hρ₁'A hr₁ hr₁A' hz₀' hzr₀ hz₁' hzr₁]
  exact pochhammer_change_basepoint a b c z hz hr₀ hr₀A hr₀A' hr₁ hr₁A hr₁A'

/-- **Joint holomorphy of Pochhammer's contour integral.** For fixed admissible `A, ρ₀, ρ₁`,
`Complex.hypergeometricPochhammerLoop` is jointly analytic in all four variables `(a, b, c, z)` on
`{p | ‖p.2.2.2‖ * ρ₀ < 1 ∧ closedBall (1 - p.2.2.2) (‖p.2.2.2‖ * ρ₁) ⊆ slitPlane}`. -/
theorem analyticOnNhd_hypergeometricPochhammerLoop {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ × ℂ =>
        hypergeometricPochhammerLoop p.1 p.2.1 p.2.2.1 p.2.2.2 A ρ₀ ρ₁)
      {p | ‖p.2.2.2‖ * ρ₀ < 1 ∧ closedBall (1 - p.2.2.2) (‖p.2.2.2‖ * ρ₁) ⊆ slitPlane} := by
  intro p hp
  have hz : 1 - p.2.2.2 ∈ slitPlane := hp.2 (mem_closedBall_self (by positivity))
  have hA1 : A < 1 := by linarith
  have h1A1 : 1 - A < 1 := by linarith
  have ha : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hc : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hz_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  have hcb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1 - q.2.1) p := hc.fun_sub hb
  have hw₀ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => 1 - q.2.2.2) p := analyticAt_const.fun_sub hz_an
  have hw₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => -q.2.2.2) p := hz_an.fun_neg
  have hslit₀ : ∀ u ∈ Icc ρ₀ A, (1 : ℂ) - p.2.2.2 * (u : ℂ) ∈ slitPlane := fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hρ₀.le.trans hu.1, hu.2.trans hA1.le⟩
  have hslit₁ : ∀ u ∈ Icc ρ₁ (1 - A), (1 - p.2.2.2) - (-p.2.2.2) * (u : ℂ) ∈ slitPlane :=
    fun u hu => sub_neg_mul_mem_slitPlane hz (hρ₁.le.trans hu.1) (hu.2.trans h1A1.le)
  have haff₀ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      affineLoopZero q.1 q.2.1 (q.2.2.1 - q.2.1) 1 q.2.2.2 A ρ₀) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.1 - 1)) - 1) p).fun_mul
      (analyticAt_integral_affineSegIntegrand_compact (fw₀ := fun _ => 1) ha hb hcb
        analyticAt_const hz_an hρ₀ hρ₀A.le hA1 hslit₀)).fun_add
      (analyticAt_integral_affineCircIntegrand (fw₀ := fun _ => 1) ha hb hcb analyticAt_const
        hz_an hρ₀ (hρ₀A.trans hA1) (closedBall_one_subset_slitPlane hp.1))
  have haff₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      affineLoopZero q.1 (q.2.2.1 - q.2.1) q.2.1 (1 - q.2.2.2) (-q.2.2.2) (1 - A) ρ₁) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.2.1 - q.2.1 - 1)) - 1) p).fun_mul
      (analyticAt_integral_affineSegIntegrand_compact ha hcb hb hw₀ hw₁ hρ₁ hρ₁A.le h1A1
        hslit₁)).fun_add
      (analyticAt_integral_affineCircIntegrand ha hcb hb hw₀ hw₁ hρ₁ (hρ₁A.trans h1A1)
        (by simpa only [norm_neg] using hp.2))
  have htot :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      1 - exp (2 * π * I * (q.2.2.1 - q.2.1 - 1))) p).fun_mul haff₀).fun_add
      ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
        1 - exp (2 * π * I * (q.2.1 - 1))) p).fun_mul haff₁)
  have hopen : IsOpen {q : ℂ × ℂ × ℂ × ℂ | 1 - q.2.2.2 ∈ slitPlane} :=
    Complex.isOpen_slitPlane.preimage
      (continuous_const.sub (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  refine htot.congr ?_
  filter_upwards [hopen.mem_nhds hz] with q hq
  exact (hypergeometricPochhammerLoop_eq_affineLoopZero q.1 q.2.1 q.2.2.1 q.2.2.2 hρ₀ hρ₀A hρ₁
    hρ₁A hq).symm

/-- **Collapsing Pochhammer's contour onto `[0, 1]`.** When `0 < re b < re c`, Pochhammer's
double-loop integral equals `-(1 - e^{2πi b}) (1 - e^{2πi (c - b)})` times the unnormalized Euler
integral over `[0, 1]`. -/
theorem hypergeometricPochhammerLoop_eq_integral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁)
    (hρ₁A : ρ₁ < 1 - A) (hz₀ : ‖z‖ * ρ₀ < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      -(1 - exp (2 * π * I * b)) * (1 - exp (2 * π * I * (c - b))) *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hA0 : 0 < A := hρ₀.trans hρ₀A
  have hA1 : A < 1 := by linarith
  have hint_full : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume 0 1 :=
    intervalIntegrable_eulerIntegrand a hb hbc hz
  have hint₀ : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume 0 A :=
    hint_full.mono_set (by
      rw [uIcc_of_le hA0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right hA1.le)
  have hint₁ :
      IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume 0 (1 - A) := by
    refine ((betaIntegral_convergent hcb hb).mul_continuousOn ?_).mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right (by linarith))
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_of_forall_continuousAt fun u hu =>
      ContinuousAt.cpow (by fun_prop) continuousAt_const (sub_neg_mul_mem_slitPlane hz hu.1 hu.2)
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀ hρ₀A hρ₁ hρ₁A hz,
    affineLoopZero_eq_integral a b (c - b) 1 z hb hρ₀ (hρ₀A.trans hA1) hρ₀A.le
      (closedBall_one_subset_slitPlane hz₀) hint₀,
    affineLoopZero_eq_integral a (c - b) b (1 - z) (-z) hcb hρ₁ (hρ₁A.trans (by linarith))
      hρ₁A.le (by simpa only [norm_neg] using hz₁) hint₁]
  have hcov : (∫ u : ℝ in 0..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
      ∫ t : ℝ in A..1, affineSegIntegrand a b (c - b) 1 z t := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1)
    rw [sub_self] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand, ofReal_sub, ofReal_one, sub_sub_cancel, sub_neg_mul_one_sub]
    ring
  have hadj : (∫ t : ℝ in 0..A, affineSegIntegrand a b (c - b) 1 z t) +
      (∫ t : ℝ in A..1, affineSegIntegrand a b (c - b) 1 z t) =
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
    have h2 : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume A 1 :=
      hint_full.mono_set (by
        rw [uIcc_of_le hA1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left hA0.le)
    exact intervalIntegral.integral_add_adjacent_intervals hint₀ h2
  rw [hcov, exp_two_pi_mul_I_sub_one, exp_two_pi_mul_I_sub_one]
  linear_combination -(1 - exp (2 * π * I * b)) * (1 - exp (2 * π * I * (c - b))) * hadj

/-- When `0 < re b < re c`, Pochhammer's contour integral is
`(4π² e^{cπi} / (Γ(1 - b) Γ(1 + b - c)))` times `Complex.eulerIntegral`, including when `b` or
`c - b` is a positive integer where both sides vanish. -/
theorem hypergeometricPochhammerLoop_eq_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁)
    (hρ₁A : ρ₁ < 1 - A) (hz₀ : ‖z‖ * ρ₀ < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c)) *
        eulerIntegral a b c z := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hrefl_b := sin_mul_Gamma_eq_pi_div_Gamma_one_sub hb
  have hrefl_cb := sin_mul_Gamma_eq_pi_div_Gamma_one_sub hcb
  have h1cb : 1 - (c - b) = 1 + b - c := by ring
  rw [h1cb] at hrefl_cb
  have hm1 : 1 - exp (2 * π * I * b) = -(2 * I * exp (b * π * I) * sin (π * b)) := by
    rw [← neg_sub, exp_two_pi_sub_one_eq_sin]
  have hm2 : 1 - exp (2 * π * I * (c - b)) =
      -(2 * I * exp ((c - b) * π * I) * sin (π * (c - b))) := by
    rw [← neg_sub, exp_two_pi_sub_one_eq_sin]
  have hexpc : exp (b * π * I) * exp ((c - b) * π * I) = exp (c * π * I) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hypergeometricPochhammerLoop_eq_integral a hb hbc hρ₀ hρ₀A hρ₁ hρ₁A hz₀ hz₁,
    hm1, hm2, eulerIntegral_def]
  set E := ∫ t : ℝ in 0..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
  have hE : E = Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E) := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hGb hGcb), one_mul]
  conv_lhs => rw [hE]
  calc -(-(2 * I * exp (b * π * I) * sin (π * b))) *
        (-(2 * I * exp ((c - b) * π * I) * sin (π * (c - b)))) *
        (Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E))
      = -(4 * I ^ 2) * (exp (b * π * I) * exp ((c - b) * π * I)) *
          (sin (π * b) * Gamma b) * (sin (π * (c - b)) * Gamma (c - b)) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by ring
    _ = 4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c)) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by
          rw [I_sq, hexpc, hrefl_b, hrefl_cb]
          ring

/-- **DLMF 15.6.5 in the Euler convergence region.** For `0 < re b < re c` and
`b, c - b ∉ {1, 2, …}`, `Complex.eulerIntegral` is represented on the cut plane by Pochhammer's
double-loop contour integral. -/
theorem eulerIntegral_eq_hypergeometricPochhammerLoop (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hcb_int : ∀ n : ℕ, c - b ≠ n + 1)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    eulerIntegral a b c z =
      exp (-c * π * I) * Gamma (1 - b) * Gamma (1 + b - c) / (4 * π ^ 2) *
        hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ := by
  have hG1b : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun n hn => hb_int n (by linear_combination -hn)
  have hG1cb : Gamma (1 + b - c) ≠ 0 :=
    Gamma_ne_zero fun n hn => hcb_int n (by linear_combination -hn)
  have hexp : exp (-(c * π * I)) * exp (c * π * I) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [hypergeometricPochhammerLoop_eq_eulerIntegral a hb hbc hρ₀ hρ₀A hρ₁ hρ₁A hz₀ hz₁]
  field_simp
  linear_combination (eulerIntegral a b c z) * hexp.symm

/-- **Pochhammer's contour integral for Euler's Beta function (DLMF 5.12.12).** At zero argument,
`Complex.hypergeometricPochhammerLoop` evaluates in closed form for all complex `a`, `b`, and `c`
with no real-part restrictions. -/
@[simp]
theorem hypergeometricPochhammerLoop_zero (a b c : ℂ) {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    hypergeometricPochhammerLoop a b c 0 A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c) * Gamma c) := by
  have h0 : ‖(0 : ℂ)‖ * ρ₀ < 1 ∧ closedBall (1 - (0 : ℂ)) (‖(0 : ℂ)‖ * ρ₁) ⊆ slitPlane := by
    simp [one_mem_slitPlane]
  have han₁ : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => hypergeometricPochhammerLoop a p.1 p.2 0 A ρ₀ ρ₁) univ := fun p _ =>
    (analyticOnNhd_hypergeometricPochhammerLoop hρ₀ hρ₀A hρ₁ hρ₁A (a, p.1, p.2, 0) h0).comp₂
      analyticAt_const (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  have hG (s : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt s
  have han₂ : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => 4 * π ^ 2 * exp (p.2 * π * I) /
        (Gamma (1 - p.1) * Gamma (1 + p.1 - p.2) * Gamma p.2)) univ := fun p _ => by
    simp_rw [div_eq_mul_inv, mul_inv]
    exact (analyticAt_const.mul ((analyticAt_snd.mul analyticAt_const).mul
      analyticAt_const).cexp).mul
      ((((hG _).comp (analyticAt_const.sub analyticAt_fst)).mul
        ((hG _).comp ((analyticAt_const.add analyticAt_fst).sub analyticAt_snd))).mul
        ((hG _).comp analyticAt_snd))
  have hU : IsOpen {p : ℂ × ℂ | 0 < p.1.re ∧ p.1.re < p.2.re} :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst)
        (Complex.continuous_re.comp continuous_snd))
  have heq := han₁.eq_of_eventuallyEq han₂ (z₀ := (1, 2)) ?_
  · exact congrFun heq (b, c)
  · filter_upwards [hU.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re ∧ (1 : ℂ).re < (2 : ℂ).re)]
      with p hp
    rw [hypergeometricPochhammerLoop_eq_eulerIntegral a hp.1 hp.2 hρ₀ hρ₀A hρ₁ hρ₁A h0.1 h0.2,
      eulerIntegral_zero a hp.1 hp.2, ← div_eq_mul_inv, div_div]

/-- With first parameter zero, Pochhammer's contour integral is independent of `z` and evaluates in
closed form for all complex `b`, `c`, and `z` whenever `0 < ρ₀ < A` and `0 < ρ₁ < 1 - A`. -/
@[simp]
theorem hypergeometricPochhammerLoop_zero_left (b c z : ℂ) {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    hypergeometricPochhammerLoop 0 b c z A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c) * Gamma c) := by
  have heq : hypergeometricPochhammerLoop 0 b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop 0 b c 0 A ρ₀ ρ₁ := by
    simp only [hypergeometricPochhammerLoop_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricPochhammerLoop_zero 0 b c hρ₀ hρ₀A hρ₁ hρ₁A]

end Complex
