/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Distributions.Gamma.Measurability

import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The inverse-gamma distribution: measure and density

The inverse-gamma law with shape `a` and scale `r` is the law of `X⁻¹` for
`X ∼ gammaMeasure a r`, where `r` is the Gamma rate. This file defines that pushforward
for positive parameters and uses the zero measure otherwise.  It derives the density

`r ^ a / Gamma a * x ^ (-a - 1) * exp (-r / x)`

on the positive half-line, proves its support and boundary behavior, identifies its
Radon--Nikodym derivative, and proves parameter measurability.

The density is derived from the pushforward definition.  On `(0, ∞)`, inversion is an involution
with absolute derivative `x⁻²`; the one-dimensional change of variables
`TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul` transports the Gamma density through this
map.

## Main declarations

* `TauCeti.Probability.inverseGammaMeasure`, `inverseGammaPDFReal`, and `inverseGammaPDF` define
  the law and its density;
* `inverseGammaMeasure_eq_withDensity`, `hasPDF_of_hasLaw_inverseGammaMeasure`, and
  `rnDeriv_inverseGammaMeasure` identify the density;
* `measurable_inverseGammaMeasure` makes the parameterized family available to kernels.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on inverse-gamma distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r x : ℝ}

/-! ### Definition and boundary behavior -/

/-- The inverse-gamma law with shape `a` and scale `r`.

For positive parameters it is the pushforward of `gammaMeasure a r` by inversion, where `r` is the
rate of the Gamma law.  It is the zero measure if either parameter is nonpositive. -/
def inverseGammaMeasure (a r : ℝ) : Measure ℝ :=
  if 0 < a ∧ 0 < r then (gammaMeasure a r).map Inv.inv else 0

/-- At positive parameters the inverse-gamma law is the inversion pushforward of the Gamma law.

This is not a `simp` lemma: `inverseGammaMeasure a r` is the simp-normal form, and unfolding it
would shadow every `simp` lemma stated about the law at positive parameters. -/
theorem inverseGammaMeasure_of_pos (ha : 0 < a) (hr : 0 < r) :
    inverseGammaMeasure a r = (gammaMeasure a r).map Inv.inv := by
  rw [inverseGammaMeasure, ite_eq_left ⟨ha, hr⟩]

/-- If the shape or scale is nonpositive, the inverse-gamma law is the zero measure. -/
@[simp]
theorem inverseGammaMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) :
    inverseGammaMeasure a r = 0 := by
  rw [inverseGammaMeasure, ite_eq_right h]

/-- A valid inverse-gamma law is a probability measure. -/
theorem isProbabilityMeasure_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (inverseGammaMeasure a r) := by
  rw [inverseGammaMeasure_of_pos ha hr]
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  infer_instance

/-- The inverse-gamma law assigns no mass to the nonpositive half-line. -/
@[simp]
theorem inverseGammaMeasure_Iic_zero (a r : ℝ) : inverseGammaMeasure a r (Iic 0) = 0 := by
  by_cases h : 0 < a ∧ 0 < r
  · rw [inverseGammaMeasure_of_pos h.1 h.2,
      Measure.map_apply measurable_inv measurableSet_Iic]
    have hpre : Inv.inv ⁻¹' Iic (0 : ℝ) = Iic 0 := by
      ext y
      simp only [mem_preimage, mem_Iic]
      exact inv_nonpos
    have hzero : gammaMeasure a r (Iic 0) = 0 := by
      have hpos := ae_pos_gammaMeasure a r
      rw [ae_iff] at hpos
      simpa only [not_lt, ← Iic_def] using hpos
    rw [hpre, hzero]
  · simp [inverseGammaMeasure_of_not_pos h]

/-- An inverse-gamma law is concentrated on the positive half-line, including in the zero-measure
invalid-parameter cases. -/
theorem ae_pos_inverseGammaMeasure (a r : ℝ) : ∀ᵐ x ∂inverseGammaMeasure a r, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using inverseGammaMeasure_Iic_zero a r

/-! ### Density -/

/-- The real-valued inverse-gamma density.  It vanishes unless both parameters and the sample
point are positive. -/
def inverseGammaPDFReal (a r x : ℝ) : ℝ :=
  if 0 < a ∧ 0 < r ∧ 0 < x then
    r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x)
  else 0

/-- The inverse-gamma density, valued in `ℝ≥0∞`. -/
def inverseGammaPDF (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseGammaPDFReal a r x)

/-- The `ℝ≥0∞`-valued inverse-gamma density is the coercion of the real-valued one. -/
theorem inverseGammaPDF_eq_ofReal (a r x : ℝ) :
    inverseGammaPDF a r x = ENNReal.ofReal (inverseGammaPDFReal a r x) := by
  rw [inverseGammaPDF]

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem inverseGammaPDFReal_of_pos (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDFReal a r x =
      r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x) := by
  simp [inverseGammaPDFReal, ha, hr, hx]

/-- The inverse-gamma density vanishes at a nonpositive point. -/
@[simp]
theorem inverseGammaPDFReal_of_nonpos (hx : x ≤ 0) (a r : ℝ) :
    inverseGammaPDFReal a r x = 0 := by
  simp [inverseGammaPDFReal, not_lt.mpr hx]

/-- The inverse-gamma density vanishes when its parameters are invalid. -/
@[simp]
theorem inverseGammaPDFReal_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) (x : ℝ) :
    inverseGammaPDFReal a r x = 0 := by
  rw [inverseGammaPDFReal, ite_eq_right]
  exact fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The inverse-gamma density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem inverseGammaPDF_of_pos (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDF a r x =
      ENNReal.ofReal (r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x)) := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_pos ha hr hx]

/-- The inverse-gamma density vanishes at a nonpositive point. -/
@[simp]
theorem inverseGammaPDF_of_nonpos (hx : x ≤ 0) (a r : ℝ) : inverseGammaPDF a r x = 0 := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The inverse-gamma density vanishes when its parameters are invalid. -/
@[simp]
theorem inverseGammaPDF_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) (x : ℝ) :
    inverseGammaPDF a r x = 0 := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The real-valued inverse-gamma density is nonnegative. -/
theorem inverseGammaPDFReal_nonneg (a r x : ℝ) : 0 ≤ inverseGammaPDFReal a r x := by
  rw [inverseGammaPDFReal]
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (Real.rpow_nonneg h.2.1.le _)
        (Real.Gamma_pos_of_pos h.1).le) (Real.rpow_nonneg h.2.2.le _))
      (Real.exp_pos _).le
  · exact le_rfl

/-- Converting the inverse-gamma density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_inverseGammaPDF (a r x : ℝ) :
    (inverseGammaPDF a r x).toReal = inverseGammaPDFReal a r x := by
  rw [inverseGammaPDF, ENNReal.toReal_ofReal (inverseGammaPDFReal_nonneg a r x)]

/-- The real inverse-gamma density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGammaPDFReal (a r : ℝ) : Measurable (inverseGammaPDFReal a r) := by
  by_cases hvalid : 0 < a ∧ 0 < r
  · have heq : inverseGammaPDFReal a r = fun x ↦
        if 0 < x then r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x) else 0 := by
      funext x
      by_cases hx : 0 < x
      · simp [inverseGammaPDFReal, hvalid, hx]
      · simp [inverseGammaPDFReal, hvalid, hx]
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
      measurable_const
  · have heq : inverseGammaPDFReal a r = 0 := by
      funext x
      rw [inverseGammaPDFReal_of_not_pos hvalid]
      rfl
    rw [heq]
    fun_prop

/-- The `ℝ≥0∞`-valued inverse-gamma density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGammaPDF (a r : ℝ) : Measurable (inverseGammaPDF a r) :=
  (measurable_inverseGammaPDFReal a r).ennreal_ofReal

/-- The inverse-gamma density is supported on the positive half-line. -/
theorem indicator_Ioi_inverseGammaPDF (a r : ℝ) :
    (Ioi (0 : ℝ)).indicator (inverseGammaPDF a r) = inverseGammaPDF a r := by
  ext y
  rcases le_or_gt y 0 with hy | hy
  · simp [hy, inverseGammaPDF]
  · simp [hy]

/-- The inverse-gamma density is the Gamma density at the inverse point multiplied by the
absolute Jacobian `x⁻²`. -/
theorem inverseGammaPDFReal_eq_inv_sq_mul_gammaPDFReal
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDFReal a r x = (x ^ 2)⁻¹ * gammaPDFReal a r x⁻¹ := by
  rw [inverseGammaPDFReal_of_pos ha hr hx, gammaPDFReal,
    ite_eq_left (inv_nonneg.mpr hx.le)]
  have hpow : x⁻¹ ^ (a - 1) = x ^ (1 - a) := by
    calc
      x⁻¹ ^ (a - 1) = (x ^ (a - 1))⁻¹ := Real.inv_rpow hx.le _
      _ = x ^ (-(a - 1)) := (Real.rpow_neg hx.le _).symm
      _ = x ^ (1 - a) := by congr 1; ring
  rw [hpow]
  have hcombine : (x ^ 2)⁻¹ * x ^ (1 - a) = x ^ (-a - 1) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  rw [← hcombine]
  simp only [div_eq_mul_inv]
  ring_nf

/-- The Jacobian identity used to transport the Gamma density through inversion. -/
private lemma ofReal_abs_inv_deriv_mul_inverseGammaPDF
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    ENNReal.ofReal (abs (-((x ^ 2)⁻¹))) * inverseGammaPDF a r x⁻¹ = gammaPDF a r x := by
  calc
    ENNReal.ofReal (abs (-((x ^ 2)⁻¹))) * inverseGammaPDF a r x⁻¹ =
        ENNReal.ofReal ((x ^ 2)⁻¹ * inverseGammaPDFReal a r x⁻¹) := by
      rw [abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hx)), inverseGammaPDF,
        ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg x))]
    _ = ENNReal.ofReal
        ((x ^ 2)⁻¹ * (((x⁻¹) ^ 2)⁻¹ * gammaPDFReal a r x)) := by
      rw [inverseGammaPDFReal_eq_inv_sq_mul_gammaPDFReal ha hr (inv_pos.mpr hx), inv_inv]
    _ = ENNReal.ofReal (gammaPDFReal a r x) := by
      simp only [inv_pow, inv_inv, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hx.ne'), one_mul]
    _ = gammaPDF a r x := by rw [gammaPDF]

/-- **The density of an inverse-gamma law**, including the zero density at invalid parameters. -/
theorem inverseGammaMeasure_eq_withDensity (a r : ℝ) :
    inverseGammaMeasure a r = volume.withDensity (inverseGammaPDF a r) := by
  by_cases h : 0 < a ∧ 0 < r
  · obtain ⟨ha, hr⟩ := h
    have himage : Inv.inv '' Ioi (0 : ℝ) = Ioi 0 := by
      ext y
      simp [Set.image_inv_eq_inv]
    have hweight : gammaPDF a r =ᵐ[volume.restrict (Ioi 0)]
        fun y ↦ ENNReal.ofReal |-(y ^ 2)⁻¹| * inverseGammaPDF a r y⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (ofReal_abs_inv_deriv_mul_inverseGammaPDF ha hr hy).symm
    rw [inverseGammaMeasure_of_pos ha hr, gammaMeasure_eq_withDensity_restrict_Ioi,
      withDensity_congr_ae hweight,
      MeasureTheory.map_withDensity_abs_deriv_mul measurableSet_Ioi measurable_inv
        (fun y hy ↦ (hasDerivAt_inv (ne_of_gt hy)).hasDerivWithinAt) inv_injective.injOn,
      himage, ← withDensity_indicator measurableSet_Ioi, indicator_Ioi_inverseGammaPDF]
  · rw [inverseGammaMeasure_of_not_pos h]
    ext s hs
    simp [withDensity_apply, hs, inverseGammaPDF_of_not_pos h]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with an inverse-gamma law has a density. -/
theorem hasPDF_of_hasLaw_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity a r] at hX)

/-- The density of a random variable with an inverse-gamma law is `inverseGammaPDF`. -/
theorem pdf_eq_inverseGammaPDF_of_hasLaw_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) :
    pdf X P volume =ᵐ[volume] inverseGammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity a r] at hX)

/-- The Radon–Nikodym derivative of an inverse-gamma law against Lebesgue measure. -/
theorem rnDeriv_inverseGammaMeasure (a r : ℝ) :
    (inverseGammaMeasure a r).rnDeriv volume =ᵐ[volume] inverseGammaPDF a r := by
  rw [inverseGammaMeasure_eq_withDensity a r]
  exact Measure.rnDeriv_withDensity volume (measurable_inverseGammaPDF a r)

/-! ### Parameter measurability -/

/-- The inverse-gamma family is jointly measurable in its parameters. -/
@[fun_prop]
theorem measurable_inverseGammaMeasure :
    Measurable fun p : ℝ × ℝ ↦ inverseGammaMeasure p.1 p.2 := by
  unfold inverseGammaMeasure
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact (Measure.measurable_map _ measurable_inv).comp measurable_gammaMeasure

end Probability

end TauCeti
