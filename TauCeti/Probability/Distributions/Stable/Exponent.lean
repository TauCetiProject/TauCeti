/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

/-- The logarithmic shape-one branch away from the origin. -/
theorem stableCharacteristicExponent_one_of_ne_zero (β : ℝ) {u : ℝ} (hu : u ≠ 0) :
    stableCharacteristicExponent 1 β u =
      (-|u| : ℂ) - ((2 * β / π * u * log |u| : ℝ) : ℂ) * Complex.I := by
  simp [stableCharacteristicExponent, hu]

/-- The non-logarithmic branch away from shape one and the origin. -/
theorem stableCharacteristicExponent_of_ne_one_of_ne_zero {α : ℝ} (hα : α ≠ 1)
    (β : ℝ) {u : ℝ} (hu : u ≠ 0) :
    stableCharacteristicExponent α β u =
      (-|u| ^ α : ℝ) +
        ((β * Real.tan (π * α / 2) * (Real.sign u * |u| ^ α - u) : ℝ) : ℂ) * Complex.I := by
  simp [stableCharacteristicExponent, hu, hα]

/-- The real part of the stable exponent is the negative stable power. -/
@[simp]
theorem stableCharacteristicExponent_re {α : ℝ} (hα : 0 < α) (β u : ℝ) :
    (stableCharacteristicExponent α β u).re = -|u| ^ α := by
  by_cases hu : u = 0
  · subst u
    simp [stableCharacteristicExponent, Real.zero_rpow hα.ne']
  · by_cases hα1 : α = 1
    · subst α
      rw [stableCharacteristicExponent_one_of_ne_zero β hu]
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
      rw [stableCharacteristicExponent_one_of_ne_zero β (neg_ne_zero.mpr hu),
        stableCharacteristicExponent_one_of_ne_zero β hu]
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
      rw [stableCharacteristicExponent_one_of_ne_zero (-β) hu,
        stableCharacteristicExponent_one_of_ne_zero β hu]
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
  · rw [stableCharacteristicExponent_one_of_ne_zero 0 hu]
    simp

/-- The modulus of the exponential of a stable exponent is `exp (-|u| ^ α)`. -/
@[simp]
theorem norm_exp_stableCharacteristicExponent {α : ℝ} (hα : 0 < α) (β u : ℝ) :
    ‖Complex.exp (stableCharacteristicExponent α β u)‖ = exp (-|u| ^ α) := by
  rw [Complex.norm_exp, stableCharacteristicExponent_re hα]

/-- For positive shape, the stable characteristic exponent is continuous at the origin. -/
theorem continuousAt_stableCharacteristicExponent_zero {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ContinuousAt (stableCharacteristicExponent α β) 0 := by
  by_cases hα1 : α = 1
  · subst α
    have habslog : ContinuousAt (fun u : ℝ ↦ |u| * log |u|) 0 :=
      (Real.continuous_mul_log.comp continuous_abs).continuousAt
    have hsignlog : Tendsto (fun u : ℝ ↦ Real.sign u * (|u| * log |u|)) (𝓝 0) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero (g := fun u : ℝ ↦ ‖|u| * log |u|‖)
        (fun u ↦ norm_nonneg (Real.sign u * (|u| * log |u|))) ?_ ?_
      · intro u
        rcases Real.sign_apply_eq u with h | h | h
        · rw [h]
          simp only [log_abs, norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, abs_abs]
          exact le_rfl
        · rw [h]
          simp only [zero_mul, norm_zero, norm_mul, norm_eq_abs, abs_abs]
          positivity
        · rw [h]
          simp only [log_abs, norm_mul, norm_eq_abs, one_mul, abs_abs]
          exact le_rfl
      · simpa only [abs_zero, Real.log_zero, zero_mul, norm_zero] using habslog.norm.tendsto
    have hsignlog' : ContinuousAt
        (fun u : ℝ ↦ Real.sign u * (|u| * log |u|)) 0 := by
      change Tendsto (fun u : ℝ ↦ Real.sign u * (|u| * log |u|)) (𝓝 0)
        (𝓝 (Real.sign 0 * (|(0 : ℝ)| * log |(0 : ℝ)|)))
      simpa using hsignlog
    have hmul : ContinuousAt (fun u : ℝ ↦ u * log |u|) 0 := by
      apply hsignlog'.congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro u
      rcases lt_trichotomy u 0 with hu | rfl | hu
      · simp [Real.sign_of_neg hu, abs_of_neg hu]
      · simp
      · simp [Real.sign_of_pos hu, abs_of_pos hu]
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
    · simpa [mul_assoc] using stableCharacteristicExponent_one_of_ne_zero β hu
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
      change Tendsto (fun u : ℝ ↦ Real.sign u * |u| ^ α) (𝓝 0)
        (𝓝 (Real.sign 0 * |(0 : ℝ)| ^ α))
      simpa using hsignpow
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
    (hs : s ≠ 0) (m : ℝ) :
    stableS1Location α β s m = m - β * s * Real.tan (π * α / 2) := by
  simp [stableS1Location, hs, hα]

/-- The logarithmic `S₁` location correction at shape one. -/
theorem stableS1Location_one (β : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (m : ℝ) :
    stableS1Location 1 β s m = m - 2 / π * β * s * log s := by
  simp [stableS1Location, hs]

/-- Away from shape one, adding an `S₀` location to the stable exponent gives the usual
`S₁` exponent with the corrected location. -/
theorem stableCharacteristicExponent_add_location_eq_s1_of_ne_one {α : ℝ} (hα : α ≠ 1)
    (hαpos : 0 < α) (β : ℝ) (s : ℝ≥0) (m t : ℝ) :
    ((m * t : ℝ) : ℂ) * Complex.I + stableCharacteristicExponent α β (s * t) =
      (-|s * t| ^ α : ℝ) +
        ((stableS1Location α β s m * t +
          β * Real.sign t * |s * t| ^ α * Real.tan (π * α / 2) : ℝ) : ℂ) * Complex.I := by
  by_cases hs : s = 0
  · subst s
    simp [Real.zero_rpow hαpos.ne']
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hs)
  have hsign : Real.sign ((s : ℝ) * t) = Real.sign t := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hspos ht), Real.sign_of_neg ht]
    · simp
    · rw [Real.sign_of_pos (mul_pos hspos ht), Real.sign_of_pos ht]
  by_cases ht : t = 0
  · simp [ht, Real.zero_rpow hαpos.ne']
  rw [stableCharacteristicExponent_of_ne_one_of_ne_zero hα β
      (mul_ne_zero (NNReal.coe_ne_zero.mpr hs) ht),
    stableS1Location_of_ne_one hα β hs m]
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
  rw [stableCharacteristicExponent_one_of_ne_zero β (mul_ne_zero hs0 ht),
    stableS1Location_one β hs m]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
      Complex.sub_re, Complex.neg_re]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, Complex.sub_im]
    rw [hlog]
    ring

end TauCeti.Probability
