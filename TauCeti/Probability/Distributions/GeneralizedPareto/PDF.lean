/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic
public import TauCeti.Probability.Density
import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Generalized Pareto densities

The generalized Pareto law of scale `s > 0` and nonzero shape `ξ` has density
`(1 + ξ * x / s) ^ (-ξ⁻¹ - 1) / s` where `x > 0` and `1 + ξ * x / s > 0`.
At zero shape its density is `exp (-x / s) / s` on the positive half-line.
The densities are chosen to vanish at support endpoints and at nonpositive scales.

This file derives the density from the exponential pushforward defining the law, using
`TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul`. It supplies normalization, joint
measurability, the exact positivity region, the Radon–Nikodym derivative, and the density of
any random variable with this law. These interfaces allow integration against the law to be
reduced to its explicit density, including the bounded-support negative-shape case.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {s ξ x : ℝ}

/-- The real density of a generalized Pareto law, zero outside its open support and for
nonpositive scale. Shape zero uses the exponential density. -/
def generalizedParetoPDFReal (s ξ x : ℝ) : ℝ :=
  if 0 < s ∧ 0 < x ∧ 0 < 1 + ξ * x / s then
    if ξ = 0 then Real.exp (-x / s) / s else (1 + ξ * x / s) ^ (-ξ⁻¹ - 1) / s
  else 0

/-- The extended nonnegative density of a generalized Pareto law. -/
def generalizedParetoPDF (s ξ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedParetoPDFReal s ξ x)

/-- The extended density is obtained from the real density by `ENNReal.ofReal`. -/
theorem generalizedParetoPDF_eq_ofReal (s ξ x : ℝ) :
    generalizedParetoPDF s ξ x = ENNReal.ofReal (generalizedParetoPDFReal s ξ x) :=
  (rfl)

/-- The generalized Pareto density vanishes at nonpositive scale. -/
@[simp]
theorem generalizedParetoPDFReal_of_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, not_lt.mpr hs]

/-- The generalized Pareto density vanishes outside its open support. -/
theorem generalizedParetoPDFReal_of_notMem (hx : x ∉ {x | 0 < x ∧ 0 < 1 + ξ * x / s}) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp only [mem_ofPred_eq] at hx
  simp [generalizedParetoPDFReal, hx]

/-- The chosen density vanishes on the nonpositive half-line, including its lower endpoint. -/
@[simp]
theorem generalizedParetoPDFReal_of_nonpos_arg (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 :=
  generalizedParetoPDFReal_of_notMem (by grind)

/-- The extended density vanishes at nonpositive scale. -/
@[simp]
theorem generalizedParetoPDF_of_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  simp [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos hs]

/-- The extended density vanishes on the nonpositive half-line. -/
@[simp]
theorem generalizedParetoPDF_of_nonpos_arg (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  simp [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos_arg hx]

/-- On its open support, the nonzero-shape density has the power-law formula. -/
theorem generalizedParetoPDFReal_of_shape_ne_zero (hs : 0 < s) (hξ : ξ ≠ 0)
    (hx : 0 < x) (hb : 0 < 1 + ξ * x / s) :
    generalizedParetoPDFReal s ξ x = (1 + ξ * x / s) ^ (-ξ⁻¹ - 1) / s := by
  simp [generalizedParetoPDFReal, hs, hξ, hx, hb]

/-- At shape zero, the density is exponential on the positive half-line. -/
@[simp]
theorem generalizedParetoPDFReal_zero (hs : 0 < s) (x : ℝ) :
    generalizedParetoPDFReal s 0 x = if 0 < x then Real.exp (-x / s) / s else 0 := by
  simp [generalizedParetoPDFReal, hs]

/-- The real density is nonnegative at every parameter and argument. -/
theorem generalizedParetoPDFReal_nonneg (s ξ x : ℝ) : 0 ≤ generalizedParetoPDFReal s ξ x := by
  unfold generalizedParetoPDFReal
  split_ifs with h hξ
  · exact div_nonneg (Real.exp_pos _).le h.1.le
  · exact div_nonneg (Real.rpow_nonneg h.2.2.le _) h.1.le
  · exact le_rfl

/-- The density is positive exactly on its open support at positive scale. -/
@[simp]
theorem generalizedParetoPDFReal_pos_iff :
    0 < generalizedParetoPDFReal s ξ x ↔ 0 < s ∧ 0 < x ∧ 0 < 1 + ξ * x / s := by
  unfold generalizedParetoPDFReal
  split_ifs with h hξ
  · exact iff_of_true (div_pos (Real.exp_pos _) h.1) h
  · exact iff_of_true (div_pos (Real.rpow_pos_of_pos h.2.2 _) h.1) h
  · simp [h]

/-- The extended density is positive exactly on its open support at positive scale. -/
@[simp]
theorem generalizedParetoPDF_pos_iff :
    0 < generalizedParetoPDF s ξ x ↔ 0 < s ∧ 0 < x ∧ 0 < 1 + ξ * x / s := by
  rw [generalizedParetoPDF_eq_ofReal, ENNReal.ofReal_pos, generalizedParetoPDFReal_pos_iff]

/-- Converting the extended density back to `ℝ` recovers the real density. -/
@[simp]
theorem toReal_generalizedParetoPDF (s ξ x : ℝ) :
    (generalizedParetoPDF s ξ x).toReal = generalizedParetoPDFReal s ξ x := by
  rw [generalizedParetoPDF, ENNReal.toReal_ofReal (generalizedParetoPDFReal_nonneg s ξ x)]

/-- The extended density is finite everywhere. -/
@[simp]
theorem generalizedParetoPDF_ne_top (s ξ x : ℝ) : generalizedParetoPDF s ξ x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The real density is jointly measurable in scale, shape, and argument. -/
@[fun_prop]
theorem measurable_uncurry_generalizedParetoPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ generalizedParetoPDFReal p.1.1 p.1.2 p.2 := by
  unfold generalizedParetoPDFReal
  apply Measurable.ite (by measurability)
  · apply Measurable.ite (by measurability) <;> fun_prop
  · exact measurable_const

/-- The extended density is jointly measurable in scale, shape, and argument. -/
@[fun_prop]
theorem measurable_uncurry_generalizedParetoPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ generalizedParetoPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_generalizedParetoPDFReal.ennreal_ofReal

/-- The real density is measurable in its argument. -/
@[fun_prop]
theorem measurable_generalizedParetoPDFReal (s ξ : ℝ) : Measurable (generalizedParetoPDFReal s ξ) :=
  measurable_uncurry_generalizedParetoPDFReal.comp (measurable_prodMk_left (x := (s, ξ)))

/-- The extended density is measurable in its argument. -/
@[fun_prop]
theorem measurable_generalizedParetoPDF (s ξ : ℝ) : Measurable (generalizedParetoPDF s ξ) :=
  (measurable_generalizedParetoPDFReal s ξ).ennreal_ofReal

private theorem hasDerivAt_transform (s ξ e : ℝ) :
    HasDerivAt (generalizedParetoMap s ξ) (s * Real.exp (ξ * e)) e := by
  by_cases hξ : ξ = 0
  · subst ξ
    convert (hasDerivAt_id e).const_mul s using 1
    · exact funext (generalizedParetoMap_zero s)
    · simp
  · have hfun : generalizedParetoMap s ξ =
        fun e ↦ s * (Real.exp (ξ * e) - 1) / ξ :=
      funext (generalizedParetoMap_of_shape_ne_zero hξ s)
    rw [hfun]
    convert ((((hasDerivAt_id e).const_mul ξ).exp.sub_const 1).const_mul s).div_const ξ using 1 <;>
      simp only [id_eq, mul_one]
    field_simp

private theorem strictMono_transform (hs : 0 < s) (ξ : ℝ) :
    StrictMono (generalizedParetoMap s ξ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_transform s ξ)
    (fun _ ↦ mul_pos hs (Real.exp_pos _))

private theorem transform_pos (hs : 0 < s) (ξ : ℝ) {e : ℝ} (he : 0 < e) :
    0 < generalizedParetoMap s ξ e := by
  have hzero : generalizedParetoMap s ξ 0 = 0 := by
    by_cases hξ : ξ = 0
    · simp [hξ]
    · simp [generalizedParetoMap_of_shape_ne_zero hξ]
  simpa only [hzero] using strictMono_transform hs ξ he

private theorem transform_base (hs : 0 < s) (ξ e : ℝ) :
    1 + ξ * generalizedParetoMap s ξ e / s = Real.exp (ξ * e) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [generalizedParetoMap_of_shape_ne_zero hξ]
    field_simp
    ring

private theorem image_transform (hs : 0 < s) (ξ : ℝ) :
    generalizedParetoMap s ξ '' Ioi 0 = {x | 0 < x ∧ 0 < 1 + ξ * x / s} := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨transform_pos hs ξ he, by rw [transform_base hs]; exact Real.exp_pos _⟩
  · rintro ⟨hx, hb⟩
    by_cases hξ : ξ = 0
    · subst ξ
      exact ⟨x / s, div_pos hx hs, by rw [generalizedParetoMap_zero, mul_div_cancel₀ _ hs.ne']⟩
    · refine ⟨Real.log (1 + ξ * x / s) / ξ, ?_, ?_⟩
      · rcases lt_or_gt_of_ne hξ with hξ | hξ
        · exact div_pos_of_neg_of_neg (Real.log_neg hb (by
            have := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hξ hx) hs
            linarith)) hξ
        · exact div_pos (Real.log_pos (by
            have := div_pos (mul_pos hξ hx) hs
            linarith)) hξ
      · rw [generalizedParetoMap_of_shape_ne_zero hξ, mul_div_cancel₀ _ hξ,
          Real.exp_log hb]
        field_simp
        ring

private theorem transform_weight (hs : 0 < s) (ξ : ℝ) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal |s * Real.exp (ξ * e)| *
        generalizedParetoPDF s ξ (generalizedParetoMap s ξ e) = exponentialPDF 1 e := by
  have hb := transform_base hs ξ e
  have hx := transform_pos hs ξ he
  rw [generalizedParetoPDF_eq_ofReal, abs_of_pos (mul_pos hs (Real.exp_pos _)),
    exponentialPDF_of_nonneg he.le]
  by_cases hξ : ξ = 0
  · subst ξ
    rw [generalizedParetoPDFReal_zero hs, ite_eq_left hx,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [generalizedParetoMap_zero, zero_mul, Real.exp_zero,
      mul_one, one_mul]
    have hquot : -(s * e) / s = -e := by field_simp
    rw [hquot]
    field_simp
  · rw [generalizedParetoPDFReal_of_shape_ne_zero hs hξ hx (hb ▸ Real.exp_pos _),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hb, ← Real.exp_mul]
    have hexp : ξ * e + ξ * e * (-ξ⁻¹ - 1) = -e := by field_simp; ring
    calc
      s * Real.exp (ξ * e) * (Real.exp (ξ * e * (-ξ⁻¹ - 1)) / s) =
          Real.exp (ξ * e) * Real.exp (ξ * e * (-ξ⁻¹ - 1)) := by field_simp
      _ = Real.exp (-e) := by rw [← Real.exp_add, hexp]
      _ = 1 * Real.exp (-(1 * e)) := by simp

/-- The generalized Pareto law is Lebesgue measure weighted by its density, at every scale
and shape, including the invalid zero-measure branch. -/
theorem generalizedParetoMeasure_eq_withDensity (s ξ : ℝ) :
    generalizedParetoMeasure s ξ = volume.withDensity (generalizedParetoPDF s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hzero : generalizedParetoPDF s ξ = 0 := by
      ext x
      simp [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos hs]
    rw [generalizedParetoMeasure_of_nonpos hs, hzero, withDensity_zero]
  · let A : Set ℝ := {x | 0 < x ∧ 0 < 1 + ξ * x / s}
    have hA : MeasurableSet A := by dsimp [A]; measurability
    have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
      (s := Ioi (0 : ℝ)) (φ := generalizedParetoMap s ξ)
      (φ' := fun e ↦ s * Real.exp (ξ * e)) (f := generalizedParetoPDF s ξ)
      measurableSet_Ioi (measurable_generalizedParetoMap_right s ξ)
      (fun e _ ↦ (hasDerivAt_transform s ξ e).hasDerivWithinAt)
      (strictMono_transform hs ξ).injective.injOn
    have hw : (fun e ↦ ENNReal.ofReal |s * Real.exp (ξ * e)| *
        generalizedParetoPDF s ξ (generalizedParetoMap s ξ e)) =ᵐ[volume.restrict (Ioi 0)]
          exponentialPDF 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
      exact transform_weight hs ξ he
    rw [withDensity_congr_ae hw, image_transform hs] at hmap
    rw [generalizedParetoMeasure_of_pos hs, expMeasure_eq_withDensity_restrict_Ioi, hmap,
      ← withDensity_indicator hA]
    congr 1
    ext x
    by_cases hx : x ∈ A
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, generalizedParetoPDF,
        generalizedParetoPDFReal_of_notMem hx, ENNReal.ofReal_zero]

/-- The extended generalized Pareto density has integral one at positive scale. -/
theorem lintegral_generalizedParetoPDF_eq_one (hs : 0 < s) (ξ : ℝ) :
    ∫⁻ x, generalizedParetoPDF s ξ x = 1 := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  have h : generalizedParetoMeasure s ξ univ = 1 := measure_univ
  rwa [generalizedParetoMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The real generalized Pareto density has integral one at positive scale. -/
theorem integral_generalizedParetoPDFReal_eq_one (hs : 0 < s) (ξ : ℝ) :
    ∫ x, generalizedParetoPDFReal s ξ x = 1 := by
  simp_rw [← toReal_generalizedParetoPDF]
  rw [integral_toReal (measurable_generalizedParetoPDF s ξ).aemeasurable
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    lintegral_generalizedParetoPDF_eq_one hs ξ, ENNReal.toReal_one]

/-- The real density is integrable for every scale and shape. -/
theorem integrable_generalizedParetoPDFReal (s ξ : ℝ) :
    Integrable (generalizedParetoPDFReal s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hzero : generalizedParetoPDFReal s ξ = 0 :=
      funext (generalizedParetoPDFReal_of_nonpos hs ξ)
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  · apply Integrable.of_integral_ne_zero
    rw [integral_generalizedParetoPDFReal_eq_one hs ξ]
    exact one_ne_zero

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrability against a generalized Pareto law is equivalent to Lebesgue integrability of
the density-weighted function, at every scale and shape. -/
theorem integrable_generalizedParetoMeasure_iff (s ξ : ℝ) {g : ℝ → E} :
    Integrable g (generalizedParetoMeasure s ξ) ↔
      Integrable fun y ↦ generalizedParetoPDFReal s ξ y • g y := by
  rw [generalizedParetoMeasure_eq_withDensity, funext (generalizedParetoPDF_eq_ofReal s ξ)]
  exact integrable_withDensity_ofReal_iff (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ))

/-- An integral against a generalized Pareto law equals the density-weighted Lebesgue integral,
at every scale and shape. -/
theorem integral_generalizedParetoMeasure_eq (s ξ : ℝ) (g : ℝ → E) :
    ∫ y, g y ∂generalizedParetoMeasure s ξ = ∫ y, generalizedParetoPDFReal s ξ y • g y := by
  rw [generalizedParetoMeasure_eq_withDensity, funext (generalizedParetoPDF_eq_ofReal s ξ)]
  exact integral_withDensity_ofReal (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ)) g

end Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with generalized Pareto law has a density. -/
theorem hasPDF_of_hasLaw_generalizedParetoMeasure
    (hX : HasLaw X (generalizedParetoMeasure s ξ) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_generalizedParetoPDF s ξ).aemeasurable
    (by rwa [generalizedParetoMeasure_eq_withDensity] at hX)

/-- The canonical density of a variable with generalized Pareto law is its named density. -/
theorem pdf_eq_generalizedParetoPDF_of_hasLaw_generalizedParetoMeasure
    (hX : HasLaw X (generalizedParetoMeasure s ξ) P) :
    pdf X P volume =ᵐ[volume] generalizedParetoPDF s ξ :=
  pdf_eq_of_hasLaw_withDensity (measurable_generalizedParetoPDF s ξ).aemeasurable
    (by rwa [generalizedParetoMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a generalized Pareto law is its named density. -/
theorem rnDeriv_generalizedParetoMeasure (s ξ : ℝ) :
    (generalizedParetoMeasure s ξ).rnDeriv volume =ᵐ[volume] generalizedParetoPDF s ξ := by
  rw [generalizedParetoMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_generalizedParetoPDF s ξ)

end TauCeti.Probability
