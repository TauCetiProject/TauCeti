/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import TauCeti.Analysis.Fourier.AbsolutelyContinuous
public import TauCeti.Analysis.Green.Examples.CurveArea.SignedArea
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# The area–energy inequality for closed plane curves

For a plane curve `γ = x + i y : ℝ → ℂ` on `[a, b]`, its **signed area** is the boundary integral
`½ ∫ₐᵇ (x y' - y x')` (`TauCeti.signedArea`, defined in
`TauCeti.Analysis.Green.Examples.CurveArea.SignedArea`).

The main result is the sharp **area–energy inequality** for absolutely continuous closed curves
with square-integrable derivative,

`4π |signedArea γ a b| ≤ (b - a) ∫ₐᵇ ‖γ'‖²`
(`TauCeti.four_pi_mul_abs_signedArea_le`),

with its complete equality analysis: equality holds exactly when `γ` is constant or traces a
circle once at constant angular speed, in one of the two orientations
(`TauCeti.mul_integral_norm_sq_eq_four_pi_mul_abs_signedArea_iff`). The Wirtinger inequality
for the mean-zero part of `γ` admits every ellipse as an equality case; the area–energy
inequality does not.

For a closed curve of constant speed on `[a, b]`, in particular an arclength parametrization,
`(b - a) ∫ₐᵇ ‖γ'‖²` is the square of its length `L`, so the inequality becomes the isoperimetric
inequality `4π |signedArea γ a b| ≤ L²`
(`HasConstantSpeedOnWith.four_pi_mul_abs_signedArea_le_eVariationOn_toReal_sq`), with equality
exactly for constant curves and circles traversed once
(`HasConstantSpeedOnWith.eVariationOn_toReal_sq_eq_four_pi_mul_abs_signedArea_iff`).

The proof is Fourier-analytic and works directly at absolutely continuous regularity. Writing
`c n` for the Fourier coefficients of `γ` on `[a, b]`, Parseval's identity applied to `γ`, to
`γ'` and to `γ' - (2πi / (b - a)) γ` gives the classical formula
`signedArea γ a b = π ∑ n ‖c n‖²` (`TauCeti.hasSum_mul_sq_fourierCoeffOn_signedArea`), while
`(b - a) ∫ ‖γ'‖² = 4π² ∑ n² ‖c n‖²`. Since `n² ≥ ± n` for integers, with equality only at `0`
and `± 1`, both the inequality and its equality cases follow, since a continuous function on
`[a, b]` is determined by its Fourier coefficients.

## Main results

* `TauCeti.hasSum_mul_sq_fourierCoeffOn_signedArea`: the Fourier series of the signed area.
* `TauCeti.four_pi_mul_abs_signedArea_le`: the area–energy inequality.
* `TauCeti.mul_integral_norm_sq_eq_four_pi_mul_signedArea_iff`,
  `TauCeti.mul_integral_norm_sq_eq_neg_four_pi_mul_signedArea_iff`,
  `TauCeti.mul_integral_norm_sq_eq_four_pi_mul_abs_signedArea_iff`: its equality cases.
* `HasConstantSpeedOnWith.four_pi_mul_abs_signedArea_le_eVariationOn_toReal_sq`,
  `HasConstantSpeedOnWith.eVariationOn_toReal_sq_eq_four_pi_mul_abs_signedArea_iff`: the
  isoperimetric inequality in terms of length for constant-speed closed curves, and its equality
  case.

## References

* A. Hurwitz, *Sur le problème des isopérimètres*, C. R. Acad. Sci. Paris **132** (1901),
  401–403 (the Fourier-series proof of the isoperimetric inequality).
* A. Hurwitz, *Sur quelques applications géométriques des séries de Fourier*, Ann. Sci. École
  Norm. Sup. (3) **19** (1902), 357–408.
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

section AreaEnergy

variable {γ γ' : ℝ → ℂ}

/-- **The Fourier series of the signed area.** For an absolutely continuous closed curve with
square-integrable derivative, the signed area is `π ∑ n ‖c n‖²`, where `c n` are the Fourier
coefficients of the curve on `[a, b]`. -/
theorem hasSum_mul_sq_fourierCoeffOn_signedArea (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n : ℤ ↦ π * n * ‖fourierCoeffOn hab γ n‖ ^ 2) (signedArea γ a b) := by
  have hba : 0 < b - a := sub_pos.2 hab
  set k : ℝ := 2 * π / (b - a) with hk
  have hk0 : k ≠ 0 := by positivity
  have hγc : ContinuousOn γ [[a, b]] := hγ.continuousOn
  have hγL2 : MemLp γ 2 (volume.restrict (Ioc a b)) :=
    (hγc.memLp_top_restrict_of_subset_isCompact isCompact_uIcc measurableSet_Ioc
      (Ioc_subset_Icc_self.trans Icc_subset_uIcc)).mono_exponent le_top
  -- The auxiliary function `h = γ' - i k γ`, whose Fourier coefficients are those of `γ`
  -- shifted in frequency by one.
  set h : ℝ → ℂ := fun t ↦ γ' t - (k * I) * γ t with hh
  have hhL2 : MemLp h 2 (volume.restrict (Ioc a b)) := hL2.sub (hγL2.const_mul _)
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab h n‖ ^ 2 =
      (2 * π * ((n : ℝ) - 1) / (b - a)) ^ 2 * ‖fourierCoeffOn hab γ n‖ ^ 2 := by
    have heq : fourierCoeffOn hab h n =
        ((2 * π * ((n : ℝ) - 1) / (b - a) : ℝ) : ℂ) * I * fourierCoeffOn hab γ n := by
      rw [hh, fourierCoeffOn_sub hab (hγ.intervalIntegrable_of_ae_hasDerivAt hγ')
        (hγc.intervalIntegrable.const_mul _), fourierCoeffOn.const_mul,
        fourierCoeffOn_ae_derivative_of_eq_endpoints hab hγ hγ' hγab, smul_eq_mul, hk]
      push_cast
      ring
    rw [heq, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
  -- Pointwise, `‖h‖² = ‖γ'‖² + k² ‖γ‖² - 2 k (x y' - y x')`.
  have hpt (t : ℝ) : (γ t).re * (γ' t).im - (γ t).im * (γ' t).re =
      (‖γ' t‖ ^ 2 + k ^ 2 * ‖γ t‖ ^ 2 - ‖h t‖ ^ 2) / (2 * k) := by
    field_simp
    simp only [hh, Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hE := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
    (hL2.integrable_norm_pow two_ne_zero)
  have hG := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
    (hγL2.integrable_norm_pow two_ne_zero)
  have hH := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
    (hhL2.integrable_norm_pow two_ne_zero)
  have hS : (∫ t in a..b, ((γ t).re * (γ' t).im - (γ t).im * (γ' t).re)) =
      ((∫ t in a..b, ‖γ' t‖ ^ 2) + k ^ 2 * (∫ t in a..b, ‖γ t‖ ^ 2) -
        ∫ t in a..b, ‖h t‖ ^ 2) / (2 * k) := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hE.add (hG.const_mul _)) hH,
      intervalIntegral.integral_add hE (hG.const_mul _), intervalIntegral.integral_const_mul]
  -- Combine Parseval's identity for `γ'`, `γ` and `h`.
  have hsum := (((hasSum_sq_frequency_mul_sq_fourierCoeffOn hab hγ hγ' hγab hL2).add
    ((hasSum_sq_fourierCoeffOn hab hγL2).mul_left (k ^ 2))).sub
    ((hasSum_sq_fourierCoeffOn hab hhL2))).mul_left ((b - a) ^ 2 / (8 * π))
  simp only [hcoeff, smul_eq_mul] at hsum
  convert hsum using 1
  · funext n
    rw [hk]
    field_simp
    ring
  · rw [signedArea_eq_of_ae_hasDerivAt hγ', hS, hk]
    field_simp
    ring

/-- For every real `s`, the energy deficit `(b - a) ∫ ‖γ'‖² - 4π s A` is
`4π² ∑ (n² - s n) ‖c n‖²`. -/
private theorem hasSum_energy_sub_signedArea (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) (s : ℝ) :
    HasSum (fun n : ℤ ↦ 4 * π ^ 2 * ((n : ℝ) ^ 2 - s * n) * ‖fourierCoeffOn hab γ n‖ ^ 2)
      ((b - a) * (∫ t in a..b, ‖γ' t‖ ^ 2) - s * (4 * π * signedArea γ a b)) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hE := (hasSum_sq_frequency_mul_sq_fourierCoeffOn hab hγ hγ' hγab hL2).mul_left
    ((b - a) ^ 2)
  have hA := (hasSum_mul_sq_fourierCoeffOn_signedArea hab hγ hγ' hγab hL2).mul_left (4 * π * s)
  convert hE.sub hA using 1
  · funext n
    field_simp
    ring
  · field_simp

/-- The equality case of the area–energy inequality in orientation `s = ± 1`. -/
private theorem mul_integral_norm_sq_eq_iff (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (b - a) * (∫ t in a..b, ‖γ' t‖ ^ 2) = s * (4 * π * signedArea γ a b) ↔
      ∃ c w : ℂ, ∀ t ∈ Icc a b, γ t = c + w * fourier s (t : AddCircle (b - a)) := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  have hsum := hasSum_energy_sub_signedArea hab hγ hγ' hγab hL2 s
  have hnn (n : ℤ) :
      0 ≤ 4 * π ^ 2 * ((n : ℝ) ^ 2 - s * n) * ‖fourierCoeffOn hab γ n‖ ^ 2 := by
    have : s * n ≤ n ^ 2 := by
      rcases hs with rfl | rfl
      · simpa using Int.le_self_sq n
      · simpa using Int.le_self_sq (-n)
    have : 0 ≤ (n : ℝ) ^ 2 - s * n := sub_nonneg.2 (by exact_mod_cast this)
    positivity
  have hmodelc (c w : ℂ) :
      ContinuousOn (fun t : ℝ ↦ c + w * fourier s (t : AddCircle (b - a))) [[a, b]] :=
    (continuous_const.add (continuous_const.mul
      ((fourier s).continuous.comp (AddCircle.continuous_mk' (b - a))))).continuousOn
  constructor
  · intro heq
    rw [heq, sub_self] at hsum
    have hzero := (hasSum_zero_iff_of_nonneg hnn).1 hsum
    -- All Fourier coefficients of `γ` outside the frequencies `0` and `s` vanish, so `γ` has the
    -- coefficients of the circle `c + w e^{2πist/(b-a)}` with `c = c 0` and `w = c s`.
    refine ⟨fourierCoeffOn hab γ 0, fourierCoeffOn hab γ s,
      eqOn_Icc_of_fourierCoeffOn_eq hab hγ.continuousOn (hmodelc _ _) fun n ↦ ?_⟩
    rw [fourierCoeffOn_const_add_mul_fourier, Pi.single_apply, Pi.single_apply]
    split_ifs with h0 hs' hs'
    · exact absurd (hs'.symm.trans h0) hs0
    · rw [h0, add_zero]
    · rw [hs', zero_add]
    · have hne : (n : ℝ) ^ 2 - s * n ≠ 0 := by
        rw [sq, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hs')) (by exact_mod_cast h0)
      simpa [hne, Real.pi_ne_zero] using congr_fun hzero n
  · rintro ⟨c, w, hcw⟩
    -- The Fourier coefficients of `γ` are those of the circle, supported on `0` and `s`.
    have hcoef : fourierCoeffOn hab γ =
        fourierCoeffOn hab (fun t : ℝ ↦ c + w * fourier s (t : AddCircle (b - a))) :=
      fourierCoeffOn_congr_ae hab ((ae_restrict_mem measurableSet_Ioc).mono
        fun t ht ↦ hcw t (Ioc_subset_Icc_self ht))
    have hzero : (fun n : ℤ ↦
        4 * π ^ 2 * ((n : ℝ) ^ 2 - s * n) * ‖fourierCoeffOn hab γ n‖ ^ 2) = 0 := by
      funext n
      rw [hcoef, fourierCoeffOn_const_add_mul_fourier, Pi.zero_apply, Pi.single_apply,
        Pi.single_apply]
      split_ifs with h0 hs' hs'
      · exact absurd (hs'.symm.trans h0) hs0
      · simp [h0]
      · simp [hs', sq]
      · simp
    rw [hzero] at hsum
    exact sub_eq_zero.1 (hasSum_zero.unique hsum).symm

/-- **The area–energy inequality.** For an absolutely continuous closed plane curve on `[a, b]`
with square-integrable derivative, `4π |signedArea γ a b| ≤ (b - a) ∫ₐᵇ ‖γ'‖²`. For a curve
parametrized proportionally to arclength the right side is the square of its length. -/
theorem four_pi_mul_abs_signedArea_le (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    4 * π * |signedArea γ a b| ≤ (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 := by
  have h (s : ℤ) (hs : s = 1 ∨ s = -1) :
      s * (4 * π * signedArea γ a b) ≤ (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 :=
    sub_nonneg.1 ((hasSum_energy_sub_signedArea hab hγ hγ' hγab hL2 s).nonneg fun n ↦ by
      have : s * n ≤ n ^ 2 := by
        rcases hs with rfl | rfl
        · simpa using Int.le_self_sq n
        · simpa using Int.le_self_sq (-n)
      have : 0 ≤ (n : ℝ) ^ 2 - s * n := sub_nonneg.2 (by exact_mod_cast this)
      positivity)
  have h₁ := h 1 (Or.inl rfl)
  have h₂ := h (-1) (Or.inr rfl)
  push_cast at h₁ h₂
  rw [← abs_of_pos (by positivity : (0 : ℝ) < 4 * π), ← abs_mul]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Equality in the area–energy inequality, positive orientation.** For an absolutely
continuous closed plane curve with square-integrable derivative, `(b - a) ∫ₐᵇ ‖γ'‖²` equals
`4π signedArea γ a b` exactly when `γ` is constant or traverses a circle once counterclockwise
at constant angular speed. -/
theorem mul_integral_norm_sq_eq_four_pi_mul_signedArea_iff (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    (b - a) * (∫ t in a..b, ‖γ' t‖ ^ 2) = 4 * π * signedArea γ a b ↔
      ∃ c w : ℂ, ∀ t ∈ Icc a b, γ t = c + w * exp (2 * π * I * t / (b - a)) := by
  have h := mul_integral_norm_sq_eq_iff hab hγ hγ' hγab hL2 (s := 1) (Or.inl rfl)
  simp only [fourier_coe_apply, Int.cast_one, mul_one, one_mul, ofReal_sub] at h
  exact_mod_cast h

/-- **Equality in the area–energy inequality, negative orientation.** For an absolutely
continuous closed plane curve with square-integrable derivative, `(b - a) ∫ₐᵇ ‖γ'‖²` equals
`-4π signedArea γ a b` exactly when `γ` is constant or traverses a circle once clockwise at
constant angular speed. -/
theorem mul_integral_norm_sq_eq_neg_four_pi_mul_signedArea_iff (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    (b - a) * (∫ t in a..b, ‖γ' t‖ ^ 2) = -(4 * π * signedArea γ a b) ↔
      ∃ c w : ℂ, ∀ t ∈ Icc a b, γ t = c + w * exp (-(2 * π * I * t / (b - a))) := by
  have h := mul_integral_norm_sq_eq_iff hab hγ hγ' hγab hL2 (s := -1) (Or.inr rfl)
  simp only [fourier_coe_apply, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_mul, neg_div,
    one_mul, ofReal_sub] at h
  exact_mod_cast h

/-- **Equality in the area–energy inequality.** For an absolutely continuous closed plane curve
with square-integrable derivative, `(b - a) ∫ₐᵇ ‖γ'‖² = 4π |signedArea γ a b|` exactly when `γ`
is constant or traverses a circle once at constant angular speed, in either orientation. -/
theorem mul_integral_norm_sq_eq_four_pi_mul_abs_signedArea_iff (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hγab : γ a = γ b)
    (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    (b - a) * (∫ t in a..b, ‖γ' t‖ ^ 2) = 4 * π * |signedArea γ a b| ↔
      ∃ c w : ℂ, (∀ t ∈ Icc a b, γ t = c + w * exp (2 * π * I * t / (b - a))) ∨
        ∀ t ∈ Icc a b, γ t = c + w * exp (-(2 * π * I * t / (b - a))) := by
  have hle := four_pi_mul_abs_signedArea_le hab hγ hγ' hγab hL2
  have h4π : (0 : ℝ) ≤ 4 * π := by positivity
  simp only [exists_or]
  rw [← mul_integral_norm_sq_eq_four_pi_mul_signedArea_iff hab hγ hγ' hγab hL2,
    ← mul_integral_norm_sq_eq_neg_four_pi_mul_signedArea_iff hab hγ hγ' hγab hL2]
  constructor
  · intro h
    rcases abs_choice (signedArea γ a b) with h' | h' <;> rw [h'] at h
    · exact Or.inl h
    · exact Or.inr (by rw [h, mul_neg])
  · rintro (h | h)
    · exact le_antisymm (h ▸ mul_le_mul_of_nonneg_left (le_abs_self _) h4π) hle
    · refine le_antisymm ?_ hle
      rw [h, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) h4π

end AreaEnergy

section ConstantSpeed

open scoped NNReal

variable {γ : ℝ → ℂ} {l : ℝ≥0}

/-- A plane curve of constant speed on `[a, b]` satisfies the hypotheses of the area–energy
inequality for its canonical derivative, and its energy times `b - a` is the square of its
length. -/
private theorem areaEnergy_hypotheses_of_hasConstantSpeedOnWith
    (hγ : HasConstantSpeedOnWith γ (Icc a b) l) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval γ a b ∧
      (∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (deriv γ t) t) ∧
      MemLp (deriv γ) 2 (volume.restrict (Ioc a b)) ∧
      (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 = (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  rw [← uIcc_of_le hab] at hγ ⊢
  refine ⟨hγ.lipschitzOnWith.absolutelyContinuousOnInterval, ?_, ?_,
    hγ.mul_integral_norm_deriv_sq⟩
  · filter_upwards [(ae_restrict_iff' measurableSet_uIcc).1 hγ.ae_norm_deriv_eq] with t ht hmem
    exact (ht (uIoc_subset_uIcc hmem)).1.hasDerivAt
  · simpa only [uIoc_of_le hab] using hγ.memLp_deriv 2

/-- **The isoperimetric inequality for constant-speed closed curves.** A closed plane curve
traversed at constant speed on `[a, b]` has signed area at most `L² / (4π)` in absolute value,
where `L` is its length. This applies in particular to arclength parametrizations. -/
theorem _root_.HasConstantSpeedOnWith.four_pi_mul_abs_signedArea_le_eVariationOn_toReal_sq
    (hγ : HasConstantSpeedOnWith γ (Icc a b) l) (hab : a ≤ b) (hγab : γ a = γ b) :
    4 * π * |signedArea γ a b| ≤ (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨hAC, hderiv, hL2, henergy⟩ :=
    areaEnergy_hypotheses_of_hasConstantSpeedOnWith hγ hab.le
  exact henergy ▸ four_pi_mul_abs_signedArea_le hab hAC hderiv hγab hL2

/-- **Equality in the isoperimetric inequality for constant-speed closed curves.** For a closed
plane curve traversed at constant speed on `[a, b]`, the square of its length equals
`4π |signedArea γ a b|` exactly when the curve is constant or traverses a circle once, in either
orientation. -/
theorem _root_.HasConstantSpeedOnWith.eVariationOn_toReal_sq_eq_four_pi_mul_abs_signedArea_iff
    (hγ : HasConstantSpeedOnWith γ (Icc a b) l) (hab : a < b) (hγab : γ a = γ b) :
    (eVariationOn γ (Icc a b)).toReal ^ 2 = 4 * π * |signedArea γ a b| ↔
      ∃ c w : ℂ, (∀ t ∈ Icc a b, γ t = c + w * exp (2 * π * I * t / (b - a))) ∨
        ∀ t ∈ Icc a b, γ t = c + w * exp (-(2 * π * I * t / (b - a))) := by
  obtain ⟨hAC, hderiv, hL2, henergy⟩ :=
    areaEnergy_hypotheses_of_hasConstantSpeedOnWith hγ hab.le
  rw [← henergy]
  exact mul_integral_norm_sq_eq_four_pi_mul_abs_signedArea_iff hab hAC hderiv hγab hL2

end ConstantSpeed

end TauCeti
