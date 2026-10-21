/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Density

/-!
# Nakagami distributions

The Nakagami law with shape `m > 0` and spread `Ω > 0` is the square-root image of
`gammaMeasure m (m / Ω)`. The spread is the second moment, rather than the variance.
All positive shapes are allowed, including shapes below one half. Invalid parameters
give the zero measure and zero densities.

This file supplies the density interfaces, parameter measurability, exact support,
cdf, squaring law, and identification with a scaled chi law. The density calculation
reuses `map_sqrt_gammaMeasure` and the chi identification reuses Gamma scaling.

## References

* M. Nakagami, *The m-distribution — A general formula of intensity distribution of
  rapid fading*, Statistical Methods in Radio Wave Propagation, Pergamon, 1960, pp. 3–36.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {m Ω x c : ℝ}

/-- The Nakagami law is the square root of a Gamma variable of shape `m` and rate `m / Ω`.
It is zero unless both parameters are positive. -/
def nakagamiMeasure (m Ω : ℝ) : Measure ℝ :=
  if 0 < m ∧ 0 < Ω then (gammaMeasure m (m / Ω)).map Real.sqrt else 0

/-- The defining square-root pushforward in the probability range. -/
theorem nakagamiMeasure_of_pos (hm : 0 < m) (hΩ : 0 < Ω) :
    nakagamiMeasure m Ω = (gammaMeasure m (m / Ω)).map Real.sqrt := by
  simp [nakagamiMeasure, hm, hΩ]

/-- Invalid Nakagami parameters give the zero measure. -/
@[simp]
theorem nakagamiMeasure_of_not_pos (h : ¬ (0 < m ∧ 0 < Ω)) :
    nakagamiMeasure m Ω = 0 := by
  simp [nakagamiMeasure, h]

/-- Positive Nakagami parameters give a probability measure. -/
theorem isProbabilityMeasure_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) :
    IsProbabilityMeasure (nakagamiMeasure m Ω) := by
  rw [nakagamiMeasure_of_pos hm hΩ]
  let _ := isProbabilityMeasure_gammaMeasure hm (div_pos hm hΩ)
  infer_instance

/-- The probability range is exactly positive shape and positive spread. -/
@[simp]
theorem isProbabilityMeasure_nakagamiMeasure_iff :
    IsProbabilityMeasure (nakagamiMeasure m Ω) ↔ 0 < m ∧ 0 < Ω := by
  constructor
  · intro hp
    by_contra h
    exact IsProbabilityMeasure.ne_zero _ (nakagamiMeasure_of_not_pos h)
  · rintro ⟨hm, hΩ⟩
    exact isProbabilityMeasure_nakagamiMeasure hm hΩ

/-- The real Nakagami density on the positive half-line, zero at invalid parameters. -/
def nakagamiPDFReal (m Ω x : ℝ) : ℝ :=
  if 0 < m ∧ 0 < Ω ∧ 0 < x then
    2 * (m / Ω) ^ m / Real.Gamma m * x ^ (2 * m - 1) * exp (-(m / Ω * x ^ 2))
  else 0

/-- The extended nonnegative Nakagami density. -/
def nakagamiPDF (m Ω x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (nakagamiPDFReal m Ω x)

/-- The extended Nakagami density is obtained from the real density. -/
theorem nakagamiPDF_eq_ofReal (m Ω x : ℝ) :
    nakagamiPDF m Ω x = ENNReal.ofReal (nakagamiPDFReal m Ω x) :=
  nakagamiPDF.eq_def m Ω x

/-- The Nakagami density at positive parameters and coordinate. -/
@[simp]
theorem nakagamiPDFReal_of_pos (hm : 0 < m) (hΩ : 0 < Ω) (hx : 0 < x) :
    nakagamiPDFReal m Ω x =
      2 * (m / Ω) ^ m / Real.Gamma m * x ^ (2 * m - 1) * exp (-(m / Ω * x ^ 2)) := by
  simp [nakagamiPDFReal, hm, hΩ, hx]

/-- The real density vanishes off its valid positive domain. -/
@[simp]
theorem nakagamiPDFReal_of_not_pos (h : ¬ (0 < m ∧ 0 < Ω ∧ 0 < x)) :
    nakagamiPDFReal m Ω x = 0 := by
  simp [nakagamiPDFReal, h]

/-- The extended density vanishes off its valid positive domain. -/
@[simp]
theorem nakagamiPDF_of_not_pos (h : ¬ (0 < m ∧ 0 < Ω ∧ 0 < x)) :
    nakagamiPDF m Ω x = 0 := by
  simp [nakagamiPDF_eq_ofReal, nakagamiPDFReal_of_not_pos h]

/-- The real Nakagami density vanishes on the nonpositive half-line. -/
@[simp high]
theorem nakagamiPDFReal_of_nonpos (hx : x ≤ 0) : nakagamiPDFReal m Ω x = 0 :=
  nakagamiPDFReal_of_not_pos (by grind)

/-- The extended Nakagami density vanishes on the nonpositive half-line. -/
@[simp high]
theorem nakagamiPDF_of_nonpos (hx : x ≤ 0) : nakagamiPDF m Ω x = 0 :=
  nakagamiPDF_of_not_pos (by grind)

/-- The extended Nakagami density at positive parameters and coordinate. -/
@[simp]
theorem nakagamiPDF_of_pos (hm : 0 < m) (hΩ : 0 < Ω) (hx : 0 < x) :
    nakagamiPDF m Ω x = ENNReal.ofReal
      (2 * (m / Ω) ^ m / Real.Gamma m * x ^ (2 * m - 1) * exp (-(m / Ω * x ^ 2))) := by
  rw [nakagamiPDF_eq_ofReal, nakagamiPDFReal_of_pos hm hΩ hx]

/-- The real Nakagami density is nonnegative everywhere. -/
theorem nakagamiPDFReal_nonneg (m Ω x : ℝ) : 0 ≤ nakagamiPDFReal m Ω x := by
  by_cases h : 0 < m ∧ 0 < Ω ∧ 0 < x
  · obtain ⟨hm, hΩ, hx⟩ := h
    rw [nakagamiPDFReal_of_pos hm hΩ hx]
    positivity
  · simp [nakagamiPDFReal_of_not_pos h]

/-- A valid Nakagami density is strictly positive exactly on the positive half-line. -/
theorem nakagamiPDFReal_pos_iff (hm : 0 < m) (hΩ : 0 < Ω) :
    0 < nakagamiPDFReal m Ω x ↔ 0 < x := by
  by_cases hx : 0 < x
  · rw [nakagamiPDFReal_of_pos hm hΩ hx]
    exact iff_of_true (by positivity) hx
  · simp [hx]

/-- The real value of the extended density is the named real density. -/
@[simp]
theorem toReal_nakagamiPDF (m Ω x : ℝ) :
    (nakagamiPDF m Ω x).toReal = nakagamiPDFReal m Ω x := by
  exact ENNReal.toReal_ofReal (nakagamiPDFReal_nonneg m Ω x)

/-- The real density is jointly measurable in shape, spread, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_nakagamiPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ nakagamiPDFReal p.1.1 p.1.2 p.2 := by
  unfold nakagamiPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The real density is measurable in its coordinate. -/
@[fun_prop]
theorem measurable_nakagamiPDFReal (m Ω : ℝ) : Measurable (nakagamiPDFReal m Ω) := by
  exact measurable_uncurry_nakagamiPDFReal.comp
    (show Measurable fun x : ℝ ↦ ((m, Ω), x) by fun_prop)

/-- The extended density is jointly measurable in shape, spread, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_nakagamiPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ nakagamiPDF p.1.1 p.1.2 p.2 := by
  unfold nakagamiPDF
  fun_prop

/-- The Nakagami density is measurable in its coordinate. -/
@[fun_prop]
theorem measurable_nakagamiPDF (m Ω : ℝ) : Measurable (nakagamiPDF m Ω) := by
  exact measurable_uncurry_nakagamiPDF.comp
    (show Measurable fun x : ℝ ↦ ((m, Ω), x) by fun_prop)

/-- The Nakagami law has its named Lebesgue density, including its zero invalid branch. -/
theorem nakagamiMeasure_eq_withDensity (m Ω : ℝ) :
    nakagamiMeasure m Ω = volume.withDensity (nakagamiPDF m Ω) := by
  by_cases h : 0 < m ∧ 0 < Ω
  · rw [nakagamiMeasure_of_pos h.1 h.2, map_sqrt_gammaMeasure,
      ← withDensity_indicator measurableSet_Ioi]
    apply withDensity_congr_ae
    refine .of_forall fun x ↦ ?_
    by_cases hx : 0 < x
    · simp [hx, nakagamiPDF_eq_ofReal, nakagamiPDFReal_of_pos h.1 h.2 hx]
    · simp [hx]
  · rw [nakagamiMeasure_of_not_pos h]
    have hz : nakagamiPDF m Ω = 0 := by
      ext x
      exact nakagamiPDF_of_not_pos (by tauto)
    simp [hz]

/-- At positive parameters the extended Nakagami density integrates to one. -/
theorem lintegral_nakagamiPDF_eq_one (hm : 0 < m) (hΩ : 0 < Ω) :
    ∫⁻ x, nakagamiPDF m Ω x = 1 := by
  let _ := isProbabilityMeasure_nakagamiMeasure hm hΩ
  simpa [nakagamiMeasure_eq_withDensity, withDensity_apply] using
    (measure_univ (μ := nakagamiMeasure m Ω))

/-- At positive parameters the real Nakagami density integrates to one. -/
theorem integral_nakagamiPDFReal (hm : 0 < m) (hΩ : 0 < Ω) :
    ∫ x, nakagamiPDFReal m Ω x = 1 := by
  simp only [integral_eq_lintegral_of_nonneg_ae (.of_forall (nakagamiPDFReal_nonneg m Ω))
      (measurable_nakagamiPDFReal m Ω).aestronglyMeasurable,
    ← nakagamiPDF_eq_ofReal, lintegral_nakagamiPDF_eq_one hm hΩ, ENNReal.toReal_one]

/-- Joint Giry measurability includes all invalid parameter values. -/
@[fun_prop]
theorem measurable_nakagamiMeasure :
    Measurable fun p : ℝ × ℝ ↦ nakagamiMeasure p.1 p.2 := by
  simpa only [nakagamiMeasure_eq_withDensity] using
    measurable_withDensity (μ := volume) measurable_uncurry_nakagamiPDF

/-- The Radon–Nikodym derivative is the named density in every parameter regime. -/
theorem rnDeriv_nakagamiMeasure (m Ω : ℝ) :
    (nakagamiMeasure m Ω).rnDeriv volume =ᵐ[volume] nakagamiPDF m Ω := by
  rw [nakagamiMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_nakagamiPDF m Ω)

/-- Nakagami variables are almost surely strictly positive. The zero invalid law is included. -/
theorem ae_pos_nakagamiMeasure (m Ω : ℝ) : ∀ᵐ x ∂nakagamiMeasure m Ω, 0 < x := by
  by_cases h : 0 < m ∧ 0 < Ω
  · rw [nakagamiMeasure_of_pos h.1 h.2]
    apply (ae_map_iff (by fun_prop) measurableSet_Ioi).2
    filter_upwards [ae_pos_gammaMeasure m (m / Ω)] with x hx
    exact sqrt_pos.2 hx
  · simp [nakagamiMeasure_of_not_pos h]

/-- The exact topological support is the closed positive half-line for valid parameters,
and empty otherwise. -/
@[simp]
theorem support_nakagamiMeasure (m Ω : ℝ) :
    (nakagamiMeasure m Ω).support = if 0 < m ∧ 0 < Ω then Ici 0 else ∅ := by
  split_ifs with h
  · have hsupp : Function.support (nakagamiPDF m Ω) = Ioi 0 := by
      ext x
      rw [Function.mem_support]
      constructor
      · intro hx
        by_contra hpos
        exact hx (nakagamiPDF_of_nonpos (le_of_not_gt hpos))
      · intro hx
        rw [nakagamiPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
        exact (nakagamiPDFReal_pos_iff h.1 h.2).2 hx
    rw [nakagamiMeasure_eq_withDensity,
      Measure.support_withDensity_eq_closure (measurable_nakagamiPDF m Ω) isOpen_Ioi hsupp,
      closure_Ioi]
  · simp [nakagamiMeasure_of_not_pos h, Measure.support_zero]

/-- Squaring a Nakagami variable recovers its defining Gamma law. -/
@[simp]
theorem nakagamiMeasure_map_sq (hm : 0 < m) (hΩ : 0 < Ω) :
    (nakagamiMeasure m Ω).map (fun x ↦ x ^ 2) = gammaMeasure m (m / Ω) := by
  rw [nakagamiMeasure_of_pos hm hΩ]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  refine (Measure.map_congr ?_).trans Measure.map_id
  filter_upwards [ae_pos_gammaMeasure m (m / Ω)] with x hx
  exact sq_sqrt hx.le

/-- Nakagami shape `m` and spread `Ω` correspond to chi degree `2 * m` and scale
`√(Ω / (2 * m))`. -/
theorem nakagamiMeasure_eq_chiMeasure (hm : 0 < m) (hΩ : 0 < Ω) :
    nakagamiMeasure m Ω = chiMeasure (2 * m) (√(Ω / (2 * m))) := by
  have hk : 0 < 2 * m := by positivity
  have hs : 0 < √(Ω / (2 * m)) := by positivity
  have hsq : (chiMeasure (2 * m) (√(Ω / (2 * m)))).map (fun x ↦ x ^ 2) =
      gammaMeasure m (m / Ω) := by
    rw [chiMeasure_map_sq hs, chiSquaredMeasure_eq_gammaMeasure hk,
      gammaMeasure_map_const_mul (half_pos hk) one_half_pos (by positivity)]
    congr 1
    · ring
    · rw [sq_sqrt (by positivity)]
      field_simp
  rw [nakagamiMeasure_of_pos hm hΩ, ← hsq]
  exact Measure.map_sqrt_map_sq _ ((ae_pos_chiMeasure hk).mono fun _ hx ↦ hx.le)

/-- Positive scaling multiplies the Nakagami spread by the square of the scale,
including the zero laws at invalid parameters. -/
@[simp]
theorem nakagamiMeasure_map_const_mul (hc : 0 < c) :
    (nakagamiMeasure m Ω).map (fun x ↦ c * x) = nakagamiMeasure m (c ^ 2 * Ω) := by
  by_cases h : 0 < m ∧ 0 < Ω
  · obtain ⟨hm, hΩ⟩ := h
    rw [nakagamiMeasure_eq_chiMeasure hm hΩ, chiMeasure_map_const_mul hc,
      nakagamiMeasure_eq_chiMeasure hm (by positivity)]
    congr 1
    rw [show c ^ 2 * Ω / (2 * m) = c ^ 2 * (Ω / (2 * m)) by ring,
      sqrt_mul (sq_nonneg c), sqrt_sq hc.le]
  · have h' : ¬ (0 < m ∧ 0 < c ^ 2 * Ω) := by
      intro h'
      exact h ⟨h'.1, (mul_pos_iff_of_pos_left (sq_pos_of_pos hc)).1 h'.2⟩
    simp [nakagamiMeasure_of_not_pos h, nakagamiMeasure_of_not_pos h']

/-- The Nakagami cdf is the regularized Gamma function at `m * x² / Ω`, with a zero
branch below the support. -/
@[simp]
theorem cdf_nakagamiMeasure_eq (hm : 0 < m) (hΩ : 0 < Ω) (x : ℝ) :
    cdf (nakagamiMeasure m Ω) x =
      if x < 0 then 0 else regularizedGamma m (m / Ω * x ^ 2) := by
  let _ := isProbabilityMeasure_nakagamiMeasure hm hΩ
  let _ := isProbabilityMeasure_gammaMeasure hm (div_pos hm hΩ)
  rw [cdf_eq_real, nakagamiMeasure_of_pos hm hΩ,
    map_measureReal_apply (by fun_prop) measurableSet_Iic]
  by_cases hx : x < 0
  · have he : Real.sqrt ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (hx.trans_le (sqrt_nonneg y))
    simp [hx, he]
  · have he : Real.sqrt ⁻¹' Iic x = Iic (x ^ 2) := by
      ext y
      simp [sqrt_le_iff, le_of_not_gt hx]
    rw [he, ← cdf_eq_real, cdf_gammaMeasure_eq hm (div_pos hm hΩ), ite_eq_right hx]

variable {α : Type*} [MeasurableSpace α] {P : Measure α} {X : α → ℝ}

/-- A variable with a Nakagami law has a density, including any zero-law case. -/
theorem hasPDF_of_hasLaw_nakagamiMeasure (hX : HasLaw X (nakagamiMeasure m Ω) P) :
    HasPDF X P := by
  rw [nakagamiMeasure_eq_withDensity] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_nakagamiPDF m Ω).aemeasurable hX

/-- The canonical density of a Nakagami variable is the named density almost everywhere. -/
theorem pdf_eq_nakagamiPDF_of_hasLaw_nakagamiMeasure
    (hX : HasLaw X (nakagamiMeasure m Ω) P) : pdf X P =ᵐ[volume] nakagamiPDF m Ω := by
  rw [nakagamiMeasure_eq_withDensity] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_nakagamiPDF m Ω).aemeasurable hX

/-- Taking square roots of a Gamma variable gives a Nakagami variable. -/
theorem hasLaw_nakagamiMeasure_of_hasLaw_gammaMeasure (hm : 0 < m) (hΩ : 0 < Ω)
    (hX : HasLaw X (gammaMeasure m (m / Ω)) P) :
    HasLaw (fun ω ↦ √(X ω)) (nakagamiMeasure m Ω) P := by
  rw [nakagamiMeasure_of_pos hm hΩ]
  exact (hasLaw_map (X := Real.sqrt) (by fun_prop)).fun_comp hX

/-- The square of a Nakagami variable has the defining Gamma law. -/
theorem hasLaw_gammaMeasure_of_hasLaw_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω)
    (hX : HasLaw X (nakagamiMeasure m Ω) P) :
    HasLaw (fun ω ↦ X ω ^ 2) (gammaMeasure m (m / Ω)) P := by
  rw [← nakagamiMeasure_map_sq hm hΩ]
  exact (hasLaw_map (X := fun x : ℝ ↦ x ^ 2) (by fun_prop)).fun_comp hX

/-- Multiplying a Nakagami variable by a positive constant scales its spread quadratically. -/
theorem hasLaw_nakagamiMeasure_const_mul (hc : 0 < c)
    (hX : HasLaw X (nakagamiMeasure m Ω) P) :
    HasLaw (fun ω ↦ c * X ω) (nakagamiMeasure m (c ^ 2 * Ω)) P := by
  simpa only [nakagamiMeasure_map_const_mul hc] using
    (hasLaw_map (X := fun x : ℝ ↦ c * x) (by fun_prop)).fun_comp hX

end TauCeti.Probability
