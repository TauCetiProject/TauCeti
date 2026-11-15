/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic

/-!
# Leading terms of Siegel functions at infinity

For `0 ≤ r₁ < 1`, the leading exponential of `g_r(τ)` is
`exp (π i B₂(r₁) τ)`. After removing it the limit is
`-exp (π i r₂ (r₁ - 1))`, except on the boundary `r₁ = 0`, where the additional factor
`1 - exp (2π i r₂)` remains. These limits hold as `Im τ → ∞`, uniformly with respect to the
unrestricted real part, and retain the exact complex phase.

For `r ∉ ℤ²` the leading coefficient is nonzero. Consequently the logarithmic `q`-order is
`B₂(r₁)/2`: `log ‖g_r(τ)‖ / log ‖exp (2π i τ)‖ → B₂(r₁)/2`.
This is the growth calculation underlying the orders of Siegel modular units at cusps;
it does not assert that an arbitrary real-indexed Siegel function has an integral Laurent
expansion in `q`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Filter
open UpperHalfPlane hiding I
open scoped Real Topology

namespace TauCeti.ModularForm

/-- The infinite-product part of `g_r` tends to `1` when `-1 < r₁ < 1`. -/
private theorem tendsto_siegelFunction_product {r : Fin 2 → ℝ}
    (hlo : -1 < r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦
      (∏' n : ℕ, (1 - cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) *
        cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1)))) *
      ∏' n : ℕ, (1 - cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) *
        cexp (-(2 * π * I * (r 0 * (τ : ℂ) + r 1))))) atImInfty (𝓝 1) := by
  have hq := UpperHalfPlane.tendsto_exp_two_pi_I_mul_add (by norm_num : (0 : ℝ) < 1) 0
  simp only [ofReal_one, one_mul, ofReal_zero, add_zero] at hq
  have hplus : Tendsto (fun τ : ℍ ↦ cexp (2 * π * I * (τ : ℂ)) *
      cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1))) atImInfty (𝓝 0) := by
    convert UpperHalfPlane.tendsto_exp_two_pi_I_mul_add
      (by linarith : 0 < 1 + r 0) (r 1) using 1
    funext τ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus : Tendsto (fun τ : ℍ ↦ cexp (2 * π * I * (τ : ℂ)) *
      cexp (-(2 * π * I * (r 0 * (τ : ℂ) + r 1)))) atImInfty (𝓝 0) := by
    convert UpperHalfPlane.tendsto_exp_two_pi_I_mul_add
      (by linarith : 0 < 1 - r 0) (-r 1) using 1
    funext τ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simpa only [one_mul] using
    (tendsto_tprod_one_sub_pow_mul hq hplus).mul (tendsto_tprod_one_sub_pow_mul hq hminus)

/-- **The exact leading coefficient of a Siegel function.** For `0 ≤ r₁ < 1`, removing
`exp (π i B₂(r₁) τ)` leaves `-exp (π i r₂ (r₁ - 1))`, with the extra factor
`1 - exp (2π i r₂)` when `r₁ = 0`. -/
theorem tendsto_siegelFunction_mul_exp_neg {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦ siegelFunction r τ * cexp (-(π * I * bernoulliFun 2 (r 0) * τ)))
      atImInfty (𝓝 (-cexp (π * I * r 1 * (r 0 - 1)) *
        (if r 0 = 0 then 1 - cexp (2 * π * I * r 1) else 1))) := by
  have hfirst : Tendsto (fun τ : ℍ ↦ 1 - cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1)))
      atImInfty (𝓝 (if r 0 = 0 then 1 - cexp (2 * π * I * r 1) else 1)) := by
    by_cases hzero : r 0 = 0
    · simp [hzero]
    · simpa [hzero] using tendsto_const_nhds.sub
        (UpperHalfPlane.tendsto_exp_two_pi_I_mul_add (lt_of_le_of_ne hlo (Ne.symm hzero)) (r 1))
  have h := (hfirst.mul (tendsto_siegelFunction_product (by linarith) hhi)).const_mul
    (-cexp (π * I * r 1 * (r 0 - 1)))
  simp only [mul_one] at h
  refine h.congr fun τ ↦ ?_
  rw [siegelFunction_eq_mul_tprod_mul_tprod r τ.im_pos]
  simp only [Complex.exp_neg]
  field_simp

/-- **The leading absolute value of a Siegel function.** For `0 ≤ r₁ < 1`, its norm divided by
`|q|^(B₂(r₁)/2)` tends to `1`, or to `|1 - exp (2π i r₂)|` on the boundary `r₁ = 0`. -/
theorem tendsto_norm_siegelFunction_div_rpow {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦ ‖siegelFunction r τ‖ /
      ‖cexp (2 * π * I * (τ : ℂ))‖ ^ (bernoulliFun 2 (r 0) / 2)) atImInfty
      (𝓝 (if r 0 = 0 then ‖1 - cexp (2 * π * I * r 1)‖ else 1)) := by
  have h := (tendsto_siegelFunction_mul_exp_neg hlo hhi).norm
  have hphase : ‖cexp (π * I * r 1 * (r 0 - 1))‖ = 1 := by simp [Complex.norm_exp]
  simp only [norm_mul, norm_neg, hphase, one_mul] at h
  simp only [apply_ite norm, norm_one] at h
  convert h using 1
  funext τ
  rw [UpperHalfPlane.norm_exp_two_pi_I_mul, ← Real.exp_mul, div_eq_mul_inv,
    ← Real.exp_neg, Complex.norm_exp]
  congr 2
  simp only [neg_re, mul_re, mul_im, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im,
    mul_zero, zero_add, add_zero, mul_one, coe_im]
  ring

/-- **The logarithmic `q`-order of a Siegel function.** For `0 ≤ r₁ < 1` and `r ∉ ℤ²`, the
logarithmic `q`-order of `g_r` is `B₂(r₁)/2`. The nonintegrality hypothesis excludes the
identically zero function at the corner of the strip. -/
theorem tendsto_log_norm_siegelFunction_div_log_norm_q {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1)
    (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) :
    Tendsto (fun τ : ℍ ↦ Real.log ‖siegelFunction r τ‖ /
      Real.log ‖cexp (2 * π * I * (τ : ℂ))‖) atImInfty
      (𝓝 (bernoulliFun 2 (r 0) / 2)) := by
  have hc : (if r 0 = 0 then ‖1 - cexp (2 * π * I * r 1)‖ else 1) ≠ 0 := by
    split_ifs with hz
    · apply norm_ne_zero_iff.mpr
      simpa only [ofReal_zero, zero_mul, zero_add] using
        UpperHalfPlane.one_sub_exp_two_pi_I_ne_zero (x := 0) (y := r 1)
          (τ := Complex.I) (by simp)
          (fun k _ hk ↦ hr ![0, k] (by ext i; fin_cases i <;> simp_all))
    · exact one_ne_zero
  have hlog := (tendsto_norm_siegelFunction_div_rpow hlo hhi).log hc
  have him : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop := tendsto_comap
  have hden : Tendsto (fun τ : ℍ ↦ Real.log ‖cexp (2 * π * I * (τ : ℂ))‖)
      atImInfty atBot := by
    simpa [UpperHalfPlane.norm_exp_two_pi_I_mul, Real.log_exp, coe_im, neg_mul] using
      him.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity : 0 < 2 * π))
  have hlim := hlog.div_atBot hden
  have h := hlim.add_const (bernoulliFun 2 (r 0) / 2)
  simp only [zero_add] at h
  refine h.congr fun τ ↦ ?_
  have hg := siegelFunction_ne_zero hr τ.im_pos
  have hq : 0 < ‖cexp (2 * π * I * (τ : ℂ))‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hq1 : ‖cexp (2 * π * I * (τ : ℂ))‖ ≠ 1 :=
    ne_of_lt (UpperHalfPlane.norm_exp_two_pi_I_lt_one τ)
  rw [Real.log_div (norm_ne_zero_iff.mpr hg) (ne_of_gt (Real.rpow_pos_of_pos hq _)),
    Real.log_rpow hq]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one hq hq1]
  ring

end TauCeti.ModularForm
