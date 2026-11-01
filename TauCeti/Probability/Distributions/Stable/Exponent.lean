/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Characteristic exponents of scalar stable laws

This file defines the characteristic exponent of a scalar stable law in Nolan's `S₀`
parameterization. This convention is continuous through shape one: away from shape one the
imaginary part contains
`sign u * |u| ^ α - u`, while at shape one its limiting logarithmic term is used explicitly.

The exponent has real part `-|u| ^ α`, is compatible with reflection and complex conjugation,
and is continuous at the origin for every positive shape. Its exponential therefore has modulus
`exp (-|u| ^ α)`. The Gaussian and symmetric Cauchy exponents occur at shapes two and one.

`stableS1Location` records the location parameter in Nolan's `S₁` convention. The final two
identities give the corresponding `S₁` characteristic exponent without introducing a second
family of stable measures.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open Filter Real
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The characteristic exponent of a standardized scalar stable law in Nolan's `S₀`
parameterization. Its value at zero is specified separately from the two displayed formulas. -/
def stableCharacteristicExponent (α β u : ℝ) : ℂ :=
  if u = 0 then 0
  else if α = 1 then
    (-|u| : ℂ) - ((2 * β / π * u * log |u| : ℝ) : ℂ) * Complex.I
  else
    (-|u| ^ α : ℝ) +
      ((β * Real.tan (π * α / 2) * (Real.sign u * |u| ^ α - u) : ℝ) : ℂ) * Complex.I

@[simp]
theorem stableCharacteristicExponent_zero (α β : ℝ) :
    stableCharacteristicExponent α β 0 = 0 := by
  simp [stableCharacteristicExponent]

/-- The logarithmic shape-one branch. -/
theorem stableCharacteristicExponent_one (β u : ℝ) :
    stableCharacteristicExponent 1 β u =
      (-|u| : ℂ) - ((2 * β / π * u * log |u| : ℝ) : ℂ) * Complex.I := by
  by_cases hu : u = 0
  · subst u
    simp [stableCharacteristicExponent]
  · simp [stableCharacteristicExponent, hu]

/-- The non-logarithmic branch away from shape one and the origin. -/
theorem stableCharacteristicExponent_of_ne_one_of_ne_zero {α : ℝ} (hα : α ≠ 1)
    (β : ℝ) {u : ℝ} (hu : u ≠ 0) :
    stableCharacteristicExponent α β u =
      (-|u| ^ α : ℝ) +
        ((β * Real.tan (π * α / 2) * (Real.sign u * |u| ^ α - u) : ℝ) : ℂ) * Complex.I := by
  simp [stableCharacteristicExponent, hu, hα]

/-- The real part of the stable exponent is the negative stable power. -/
@[simp]
theorem stableCharacteristicExponent_re {α : ℝ} (hα : α ≠ 0) (β u : ℝ) :
    (stableCharacteristicExponent α β u).re = -|u| ^ α := by
  by_cases hu : u = 0
  · subst u
    simp [stableCharacteristicExponent, Real.zero_rpow hα]
  · by_cases hα1 : α = 1
    · subst α
      rw [stableCharacteristicExponent_one β u]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.neg_re,
        Real.rpow_one]
    · rw [stableCharacteristicExponent_of_ne_one_of_ne_zero hα1 β hu]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- Reflection of the argument is complex conjugation of the exponent. -/
theorem stableCharacteristicExponent_neg (α β u : ℝ) :
    stableCharacteristicExponent α β (-u) =
      starRingEnd ℂ (stableCharacteristicExponent α β u) := by
  by_cases hu : u = 0
  · simp [hu]
  · by_cases hα : α = 1
    · subst α
      rw [stableCharacteristicExponent_one β (-u), stableCharacteristicExponent_one β u]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.conj_re, abs_neg]
      · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.conj_im, abs_neg,
          Complex.neg_im]
        ring
    · rw [stableCharacteristicExponent_of_ne_one_of_ne_zero hα β (neg_ne_zero.mpr hu),
        stableCharacteristicExponent_of_ne_one_of_ne_zero hα β hu]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.conj_re, abs_neg]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.conj_im, abs_neg,
          Real.sign_neg]
        ring

/-- Negating the skewness parameter has the same effect as reflecting the argument. -/
theorem stableCharacteristicExponent_neg_skew (α β u : ℝ) :
    stableCharacteristicExponent α (-β) u = stableCharacteristicExponent α β (-u) := by
  rw [stableCharacteristicExponent_neg]
  by_cases hu : u = 0
  · simp [hu]
  · by_cases hα : α = 1
    · subst α
      rw [stableCharacteristicExponent_one (-β) u, stableCharacteristicExponent_one β u]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.conj_re]
      · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.conj_im]
        simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]
        ring
    · rw [stableCharacteristicExponent_of_ne_one_of_ne_zero hα (-β) hu,
        stableCharacteristicExponent_of_ne_one_of_ne_zero hα β hu]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.conj_re]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.conj_im]
        ring

/-- The imaginary part of the stable exponent is linear in the skewness parameter: it is `β`
times the imaginary part of the totally skewed exponent. -/
theorem stableCharacteristicExponent_im_eq_mul (α β u : ℝ) :
    (stableCharacteristicExponent α β u).im =
      β * (stableCharacteristicExponent α 1 u).im := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rcases eq_or_ne α 1 with rfl | hα
  · simp only [stableCharacteristicExponent_one, Complex.sub_im, Complex.neg_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
    ring
  · simp only [stableCharacteristicExponent_of_ne_one_of_ne_zero hα _ hu, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
    ring

/-- Away from shape one, the imaginary part of the stable exponent is
`β tan (π α / 2) (u |u| ^ (α - 1) - u)`; this form also holds at the origin. -/
theorem stableCharacteristicExponent_im_of_ne_one {α : ℝ} (hα : α ≠ 1) (β u : ℝ) :
    (stableCharacteristicExponent α β u).im =
      β * Real.tan (π * α / 2) * (u * |u| ^ (α - 1) - u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hsign : Real.sign u * |u| ^ α = u * |u| ^ (α - 1) := by
    rw [Real.rpow_sub_one (abs_pos.mpr hu).ne']
    rcases hu.lt_or_gt with hu | hu
    · rw [Real.sign_of_neg hu, abs_of_neg hu]
      field_simp
    · rw [Real.sign_of_pos hu, abs_of_pos hu]
      field_simp
  simp only [stableCharacteristicExponent_of_ne_one_of_ne_zero hα _ hu, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, hsign]
  ring

/-- At shape two the exponent is the centered Gaussian exponent `-u²`, independently of
skewness. -/
@[simp]
theorem stableCharacteristicExponent_two (β u : ℝ) :
    stableCharacteristicExponent 2 β u = -(u ^ 2 : ℝ) := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [stableCharacteristicExponent_of_ne_one_of_ne_zero (by norm_num) β hu]
    apply Complex.ext
    · simp [sq_abs]
    · simp [Real.tan_eq_sin_div_cos]

/-- At shape one and zero skewness the exponent is the centered Cauchy exponent. -/
@[simp]
theorem stableCharacteristicExponent_one_zero (u : ℝ) :
    stableCharacteristicExponent 1 0 u = -|u| := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [stableCharacteristicExponent_one 0 u]
    simp

/-- The modulus of the exponential of a stable exponent is `exp (-|u| ^ α)`. -/
@[simp]
theorem norm_exp_stableCharacteristicExponent {α : ℝ} (hα : α ≠ 0) (β u : ℝ) :
    ‖Complex.exp (stableCharacteristicExponent α β u)‖ = exp (-|u| ^ α) := by
  rw [Complex.norm_exp, stableCharacteristicExponent_re hα]

/-- For positive shape, the stable characteristic exponent is continuous at the origin. -/
theorem continuousAt_stableCharacteristicExponent_zero {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ContinuousAt (stableCharacteristicExponent α β) 0 := by
  by_cases hα1 : α = 1
  · subst α
    have hmul : ContinuousAt (fun u : ℝ ↦ u * log |u|) 0 := by
      simpa only [Real.log_abs] using Real.continuous_mul_log.continuousAt
    have hc : ContinuousAt (fun _ : ℝ ↦ 2 * β / π) 0 := continuousAt_const
    have hI : ContinuousAt (fun _ : ℝ ↦ Complex.I) 0 := continuousAt_const
    have hcont : ContinuousAt (fun u : ℝ ↦
        (-|u| : ℂ) - (((2 * β / π) * (u * log |u|) : ℝ) : ℂ) * Complex.I) 0 :=
      by
        simpa only [ContinuousAt, Pi.mul_apply, Pi.neg_apply, Complex.ofReal_neg] using
          continuous_abs.continuousAt.neg.ofReal.sub (((hc.mul hmul).ofReal).mul hI)
    apply hcont.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · simpa [mul_assoc] using stableCharacteristicExponent_one β u
  · have hrpow : ContinuousAt (fun u : ℝ ↦ |u| ^ α) 0 := by
      exact continuous_abs.continuousAt.rpow_const (Or.inr hα.le)
    have hsignpow : Tendsto (fun u : ℝ ↦ Real.sign u * |u| ^ α) (𝓝 0) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero (g := fun u : ℝ ↦ ‖|u| ^ α‖)
        (fun u ↦ norm_nonneg (Real.sign u * |u| ^ α)) ?_ ?_
      · intro u
        rcases Real.sign_apply_eq u with h | h | h
        · rw [h]
          simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul]
          exact le_rfl
        · rw [h]
          simp only [zero_mul, norm_zero]
          exact norm_nonneg _
        · rw [h]
          simp only [norm_eq_abs, one_mul]
          exact le_rfl
      · simpa only [abs_zero, Real.zero_rpow hα.ne', norm_zero] using hrpow.norm.tendsto
    have hsignpow' : ContinuousAt (fun u : ℝ ↦ Real.sign u * |u| ^ α) 0 := by
      simpa only [ContinuousAt, Real.sign_zero, zero_mul] using hsignpow
    have him : ContinuousAt
        (fun u : ℝ ↦ β * Real.tan (π * α / 2) *
          (Real.sign u * |u| ^ α - u)) 0 :=
      continuousAt_const.mul (hsignpow'.sub continuousAt_id)
    have hcont : ContinuousAt (fun u : ℝ ↦
        ((-|u| ^ α : ℝ) : ℂ) +
          ((β * Real.tan (π * α / 2) * (Real.sign u * |u| ^ α - u) : ℝ) : ℂ) *
            Complex.I) 0 :=
      hrpow.neg.ofReal.add (him.ofReal.mul continuousAt_const)
    apply hcont.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u = 0
    · subst u
      simp [Real.zero_rpow hα.ne']
    · exact stableCharacteristicExponent_of_ne_one_of_ne_zero hα1 β hu

/-- The location in Nolan's `S₁` parameterization corresponding to an `S₀` location `m`. -/
def stableS1Location (α β : ℝ) (s : ℝ≥0) (m : ℝ) : ℝ :=
  m - if s = 0 then 0
    else if α = 1 then 2 / π * β * s * log s
    else β * s * Real.tan (π * α / 2)

@[simp]
theorem stableS1Location_zero_scale (α β m : ℝ) : stableS1Location α β 0 m = m := by
  simp [stableS1Location]

/-- The `S₁` location correction away from shape one. -/
theorem stableS1Location_of_ne_one {α : ℝ} (hα : α ≠ 1) (β : ℝ) {s : ℝ≥0}
    (m : ℝ) :
    stableS1Location α β s m = m - β * s * Real.tan (π * α / 2) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [stableS1Location]
  · simp [stableS1Location, hs, hα]

/-- The logarithmic `S₁` location correction at shape one. -/
theorem stableS1Location_one (β : ℝ) {s : ℝ≥0} (m : ℝ) :
    stableS1Location 1 β s m = m - 2 / π * β * s * log s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [stableS1Location]
  · simp [stableS1Location, hs]

/-- Away from shape one, adding an `S₀` location to the stable exponent gives the usual
`S₁` exponent with the corrected location. -/
theorem stableCharacteristicExponent_add_location_eq_s1_of_ne_one {α : ℝ} (hα : α ≠ 1)
    (hα0 : α ≠ 0) (β : ℝ) (s : ℝ≥0) (m t : ℝ) :
    ((m * t : ℝ) : ℂ) * Complex.I + stableCharacteristicExponent α β (s * t) =
      (-|s * t| ^ α : ℝ) +
        ((stableS1Location α β s m * t +
          β * Real.sign t * |s * t| ^ α * Real.tan (π * α / 2) : ℝ) : ℂ) * Complex.I := by
  by_cases hs : s = 0
  · subst s
    simp [Real.zero_rpow hα0]
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hs)
  have hsign : Real.sign ((s : ℝ) * t) = Real.sign t := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hspos ht), Real.sign_of_neg ht]
    · simp
    · rw [Real.sign_of_pos (mul_pos hspos ht), Real.sign_of_pos ht]
  by_cases ht : t = 0
  · simp [ht, Real.zero_rpow hα0]
  rw [stableCharacteristicExponent_of_ne_one_of_ne_zero hα β
      (mul_ne_zero (NNReal.coe_ne_zero.mpr hs) ht),
    stableS1Location_of_ne_one hα β m]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
    rw [hsign]
    ring

/-- At shape one, adding an `S₀` location to the stable exponent gives the logarithmic `S₁`
exponent with the corrected location. -/
theorem stableCharacteristicExponent_add_location_eq_s1_one (β : ℝ) (s : ℝ≥0)
    (m t : ℝ) :
    ((m * t : ℝ) : ℂ) * Complex.I + stableCharacteristicExponent 1 β (s * t) =
      (-|s * t| : ℂ) +
        ((stableS1Location 1 β s m * t - 2 / π * β * s * t * log |t| : ℝ) : ℂ) *
          Complex.I := by
  by_cases hs : s = 0
  · subst s
    simp
  have hs0 : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  by_cases ht : t = 0
  · simp [ht]
  have hsnonneg : 0 ≤ (s : ℝ) := s.property
  have hlog : log |(s : ℝ) * t| = log s + log |t| := by
    rw [abs_mul, abs_of_nonneg hsnonneg, Real.log_mul hs0 (abs_ne_zero.mpr ht)]
  rw [stableCharacteristicExponent_one β (s * t), stableS1Location_one β m]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
      Complex.sub_re, Complex.neg_re]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.sub_im]
    rw [hlog]
    ring

end TauCeti.Probability
