/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Cauchy.Basic

/-!
# Affine transport and convolution of scalar stable laws

This file proves that Nolan's `S₀` stable family `stableMeasure α β s m` is closed under affine
maps and, at a common shape `α`, under convolution.

* **Affine transport.** `a + b * X` has skewness `Real.sign b * β`, scale `‖b‖₊ * s` and
  location `a + b * m`. For `b ≠ 0` this holds for all parameters, valid or not. For valid
  parameters it also covers `b = 0`, where both scale and skewness vanish and the law is the
  Dirac mass at `a`; this constant-map identity also follows directly from
  `MeasureTheory.Measure.map_const`. Invalid stable families and all their pushforwards are zero
  by `stableMeasure_of_invalid` and `MeasureTheory.Measure.map_zero`. Reflection is the case
  `b = -1`.
* **Convolution.** Two stable laws of common shape `α` convolve to a stable law of the same
  shape. Its scale `s` satisfies `s ^ α = s₁ ^ α + s₂ ^ α`, its skewness is the average of the
  skewnesses weighted by `sᵢ ^ α`, and its `S₁` location `stableS1Location α β s m` is the sum of
  the two input `S₁` locations. Two zero-scale laws convolve to the Dirac mass at `m₁ + m₂`.
  Independent sums give the corresponding `HasLaw` statement.
* **Cauchy specialization.** At shape one and skewness zero the stable law is the Cauchy law
  with the same location and scale. The Gaussian specialization at shape two is
  `TauCeti.Probability.stableMeasure_two`.

All identities are proved through `TauCeti.Probability.charFun_stableMeasure` and uniqueness of
characteristic functions. The convolution formula is additive in the `S₁` location, which is
why the `S₁` form of the exponent is used there.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {α β : ℝ}

/-! ### Affine transport -/

/-- An affine image of a stable law is stable with skewness `Real.sign b * β`, scale
`‖b‖₊ * s` and location `a + b * m`. For `b ≠ 0` no validity hypothesis is needed, since invalid
parameters give the zero measure on both sides. For valid parameters and `b = 0` this is the
Dirac mass at `a`. -/
@[simp]
theorem stableMeasure_map_affine {s : ℝ≥0} {m a b : ℝ}
    (h : b ≠ 0 ∨ (0 < α ∧ α ≤ 2) ∧ |β| ≤ 1) :
    (stableMeasure α β s m).map (fun x ↦ a + b * x) =
      stableMeasure α (Real.sign b * β) (‖b‖₊ * s) (a + b * m) := by
  by_cases hv : α ∈ Ioc 0 2 ∧ |β| ≤ 1
  swap
  · have hb : b ≠ 0 := h.resolve_right hv
    have hinv : α ≤ 0 ∨ 2 < α ∨ 1 < |β| := by
      simpa only [mem_Ioc, not_and_or, not_lt, not_le, or_assoc] using hv
    have hsβ : |Real.sign b * β| = |β| := by
      rcases Real.sign_apply_eq_of_ne_zero b hb with hs | hs <;> simp [hs]
    rw [stableMeasure_of_invalid hinv, stableMeasure_of_invalid (by rwa [hsβ]), Measure.map_zero]
  obtain ⟨hα, hβ⟩ := hv
  have hβ' : |Real.sign b * β| ≤ 1 := by
    rcases Real.sign_apply_eq b with h | h | h <;> simp [h, hβ]
  apply Measure.ext_of_charFun
  funext t
  have harg : ((‖b‖₊ * s : ℝ≥0) : ℝ) * t = |b| * (s * t) := by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
    ring
  rw [charFun_map_affine, charFun_stableMeasure hα hβ, charFun_stableMeasure hα hβ',
    ← Complex.exp_add, mul_left_comm (s : ℝ) b t, stableCharacteristicExponent_mul, harg]
  push_cast
  ring_nf

/-- Reflection of a stable law negates its skewness and location. This holds for all
parameters, since invalid shapes give the zero measure on both sides. -/
@[simp]
theorem stableMeasure_map_neg (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    (stableMeasure α β s m).map (fun x ↦ -x) = stableMeasure α (-β) s (-m) := by
  have hneg : (fun x : ℝ ↦ -x) = fun x ↦ 0 + -1 * x := by
    funext x
    ring
  rw [hneg, stableMeasure_map_affine (Or.inl (by norm_num))]
  simp [Real.sign_neg]

/-- Affine transport of a stable random variable. For `b ≠ 0` no validity hypothesis is
needed; for valid parameters this includes constant maps. -/
theorem hasLaw_affine_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {s : ℝ≥0} {m : ℝ} (a b : ℝ) (h : b ≠ 0 ∨ (0 < α ∧ α ≤ 2) ∧ |β| ≤ 1)
    (hX : HasLaw X (stableMeasure α β s m) P) :
    HasLaw (fun ω ↦ a + b * X ω)
      (stableMeasure α (Real.sign b * β) (‖b‖₊ * s) (a + b * m)) P :=
  (HasLaw.mk (by fun_prop) (stableMeasure_map_affine h)).fun_comp hX

/-- Reflection of a random variable with a scalar stable law. -/
theorem hasLaw_neg_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {α β : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (stableMeasure α β s m) P) :
    HasLaw (fun ω ↦ -X ω) (stableMeasure α (-β) s (-m)) P :=
  (HasLaw.mk (by fun_prop) (stableMeasure_map_neg α β s m)).fun_comp hX

/-! ### Convolution -/

/-- **Output shape validity.** The `sᵢ ^ α`-weighted average of two valid skewnesses is a valid
skewness. When both weights vanish the average is `0`. -/
theorem abs_stableConvSkew_le_one {β₁ β₂ : ℝ} (hβ₁ : |β₁| ≤ 1) (hβ₂ : |β₂| ≤ 1)
    (s₁ s₂ : ℝ≥0) :
    |(β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α) / ((s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α)| ≤ 1 := by
  have h₁ : 0 ≤ (s₁ : ℝ) ^ α := by positivity
  have h₂ : 0 ≤ (s₂ : ℝ) ^ α := by positivity
  rcases (add_nonneg h₁ h₂).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact zero_le_one
  · rw [abs_div, abs_of_pos h, div_le_one h]
    calc |β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α|
        ≤ |β₁| * (s₁ : ℝ) ^ α + |β₂| * (s₂ : ℝ) ^ α := by
          simpa only [abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂] using
            abs_add_le (β₁ * (s₁ : ℝ) ^ α) (β₂ * (s₂ : ℝ) ^ α)
      _ ≤ (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α := by nlinarith

/-- **Stable laws of a common shape are closed under convolution.** The output parameters are
characterized by `s ^ α = s₁ ^ α + s₂ ^ α`, `β * s ^ α = β₁ * s₁ ^ α + β₂ * s₂ ^ α`, and
additivity of the `S₁` locations. When `s ≠ 0` these equations determine `s`, `β` and `m`; when
`s₁ = s₂ = 0` they force `s = 0` and `m = m₁ + m₂`, so the conclusion is the Dirac identity. -/
theorem stableMeasure_conv_stableMeasure_of_eq (hα : α ∈ Ioc 0 2) {β₁ β₂ : ℝ}
    (hβ₁ : |β₁| ≤ 1) (hβ₂ : |β₂| ≤ 1) (hβ : |β| ≤ 1) {s₁ s₂ s : ℝ≥0} {m₁ m₂ m : ℝ}
    (hs : (s : ℝ) ^ α = (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α)
    (hskew : β * (s : ℝ) ^ α = β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α)
    (hm : stableS1Location α β s m =
      stableS1Location α β₁ s₁ m₁ + stableS1Location α β₂ s₂ m₂) :
    stableMeasure α β₁ s₁ m₁ ∗ stableMeasure α β₂ s₂ m₂ = stableMeasure α β s m := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_stableMeasure hα hβ₁, charFun_stableMeasure hα hβ₂,
    charFun_stableMeasure hα hβ, ← Complex.exp_add]
  congr 1
  rcases eq_or_ne α 1 with rfl | hα1
  · simp only [Real.rpow_one] at hs hskew
    rw [stableCharacteristicExponent_add_location_eq_s1_one β₁ s₁ m₁ t,
      stableCharacteristicExponent_add_location_eq_s1_one β₂ s₂ m₂ t,
      stableCharacteristicExponent_add_location_eq_s1_one β s m t, hm]
    simp only [abs_mul, NNReal.abs_eq]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, mul_one]
    · linear_combination |t| * hs
    · linear_combination (2 / Real.pi * t * Real.log |t|) * hskew
  · have hα0 : α ≠ 0 := hα.1.ne'
    rw [stableCharacteristicExponent_add_location_eq_s1_of_ne_one hα1 hα0 β₁ s₁ m₁ t,
      stableCharacteristicExponent_add_location_eq_s1_of_ne_one hα1 hα0 β₂ s₂ m₂ t,
      stableCharacteristicExponent_add_location_eq_s1_of_ne_one hα1 hα0 β s m t, hm]
    simp only [abs_mul, NNReal.abs_eq, Real.mul_rpow (NNReal.coe_nonneg _) (abs_nonneg t)]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        add_zero, mul_one, zero_add]
    · linear_combination |t| ^ α * hs
    · linear_combination (-(Real.sign t * |t| ^ α * Real.tan (Real.pi * α / 2))) * hskew

/-- **Explicit convolution parameters.** Two stable laws of common valid shape `α` convolve to
the stable law with scale `s = (s₁ ^ α + s₂ ^ α) ^ α⁻¹`, skewness
`β = (β₁ * s₁ ^ α + β₂ * s₂ ^ α) / (s₁ ^ α + s₂ ^ α)` and location `d₁ + d₂ + h`, where
`dᵢ = stableS1Location α βᵢ sᵢ mᵢ` are the `S₁` locations and
`h = -stableS1Location α β s 0` is the `S₀` correction at the output parameters. When both
scales vanish, `s = β = h = 0` and the law is the Dirac mass at `m₁ + m₂`. -/
theorem stableMeasure_conv_stableMeasure (hα : α ∈ Ioc 0 2) {β₁ β₂ : ℝ}
    (hβ₁ : |β₁| ≤ 1) (hβ₂ : |β₂| ≤ 1) (s₁ s₂ : ℝ≥0) (m₁ m₂ : ℝ) :
    stableMeasure α β₁ s₁ m₁ ∗ stableMeasure α β₂ s₂ m₂ =
      stableMeasure α
        ((β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α) / ((s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α))
        ((s₁ ^ α + s₂ ^ α) ^ α⁻¹)
        (stableS1Location α β₁ s₁ m₁ + stableS1Location α β₂ s₂ m₂ -
          stableS1Location α
            ((β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α) / ((s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α))
            ((s₁ ^ α + s₂ ^ α) ^ α⁻¹) 0) := by
  have hα0 : α ≠ 0 := hα.1.ne'
  have h₁ : 0 ≤ (s₁ : ℝ) ^ α := by positivity
  have h₂ : 0 ≤ (s₂ : ℝ) ^ α := by positivity
  have hs : (((s₁ ^ α + s₂ ^ α) ^ α⁻¹ : ℝ≥0) : ℝ) ^ α = (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α := by
    rw [← NNReal.coe_rpow, NNReal.rpow_inv_rpow hα0, NNReal.coe_add, NNReal.coe_rpow,
      NNReal.coe_rpow]
  refine stableMeasure_conv_stableMeasure_of_eq hα hβ₁ hβ₂
    (abs_stableConvSkew_le_one hβ₁ hβ₂ s₁ s₂) hs ?_ ?_
  · rw [hs]
    rcases (add_nonneg h₁ h₂).eq_or_lt with h | h
    · have h₁0 : (s₁ : ℝ) ^ α = 0 := by linarith
      have h₂0 : (s₂ : ℝ) ^ α = 0 := by linarith
      simp [h₁0, h₂0]
    · exact div_mul_cancel₀ _ h.ne'
  · rw [stableS1Location_eq_add]
    ring

/-! ### Specializations -/

/-- At shape one and skewness zero the stable law is the Cauchy law with the same location and
scale, including the Dirac case of zero scale. -/
@[simp]
theorem stableMeasure_one_zero (s : ℝ≥0) (m : ℝ) :
    stableMeasure 1 0 s m = cauchyMeasure m s := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stableMeasure ⟨one_pos, one_le_two⟩ (by simp), charFun_cauchyMeasure,
    stableCharacteristicExponent_one_zero, abs_mul, NNReal.abs_eq]
  push_cast
  ring_nf

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- The sum of independent stable variables of a common valid shape is stable, with parameters
characterized as in `TauCeti.Probability.stableMeasure_conv_stableMeasure_of_eq`. -/
theorem IndepFun.hasLaw_add_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {α β₁ β₂ β : ℝ} {s₁ s₂ s : ℝ≥0} {m₁ m₂ m : ℝ} (hXY : IndepFun X Y P)
    (hX : HasLaw X (stableMeasure α β₁ s₁ m₁) P) (hY : HasLaw Y (stableMeasure α β₂ s₂ m₂) P)
    (hα : α ∈ Ioc 0 2) (hβ₁ : |β₁| ≤ 1) (hβ₂ : |β₂| ≤ 1) (hβ : |β| ≤ 1)
    (hs : (s : ℝ) ^ α = (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α)
    (hskew : β * (s : ℝ) ^ α = β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α)
    (hm : stableS1Location α β s m =
      stableS1Location α β₁ s₁ m₁ + stableS1Location α β₂ s₂ m₂) :
    HasLaw (X + Y) (stableMeasure α β s m) P := by
  rw [← stableMeasure_conv_stableMeasure_of_eq hα hβ₁ hβ₂ hβ hs hskew hm]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
