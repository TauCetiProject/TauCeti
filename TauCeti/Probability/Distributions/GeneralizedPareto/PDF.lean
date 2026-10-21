/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic
public import TauCeti.Probability.Density
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity

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
theorem generalizedParetoPDFReal_of_scale_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, not_lt.mpr hs]

/-- The generalized Pareto density vanishes outside its open support. -/
theorem generalizedParetoPDFReal_of_not_pos (hx : ¬ (0 < x ∧ 0 < 1 + ξ * x / s)) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, hx]

/-- The chosen density vanishes on the nonpositive half-line, including its lower endpoint. -/
@[simp]
theorem generalizedParetoPDFReal_of_nonpos (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 :=
  generalizedParetoPDFReal_of_not_pos (by grind)

/-- The extended density vanishes at nonpositive scale. -/
@[simp]
theorem generalizedParetoPDF_of_scale_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  simp [generalizedParetoPDF, generalizedParetoPDFReal_of_scale_nonpos hs]

/-- The extended density vanishes on the nonpositive half-line. -/
@[simp]
theorem generalizedParetoPDF_of_nonpos (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  simp [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos hx]

/-- At negative shape, the real density vanishes at and above the finite upper endpoint. -/
@[simp]
theorem generalizedParetoPDFReal_of_neg_of_le (hs : 0 < s) (hξ : ξ < 0)
    (hx : -s / ξ ≤ x) : generalizedParetoPDFReal s ξ x = 0 := by
  apply generalizedParetoPDFReal_of_not_pos
  have hcut : ξ * x ≤ -s := by
    have := (div_le_iff_of_neg hξ).mp hx
    linarith
  have hquot : ξ * x / s ≤ -1 := (div_le_iff₀ hs).mpr (by linarith)
  grind

/-- At negative shape, the extended density vanishes at and above the finite upper endpoint. -/
@[simp]
theorem generalizedParetoPDF_of_neg_of_le (hs : 0 < s) (hξ : ξ < 0)
    (hx : -s / ξ ≤ x) : generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_neg_of_le hs hξ hx,
    ENNReal.ofReal_zero]

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

/-- On its open support, the nonzero-shape extended density has the power-law formula. -/
theorem generalizedParetoPDF_of_shape_ne_zero (hs : 0 < s) (hξ : ξ ≠ 0)
    (hx : 0 < x) (hb : 0 < 1 + ξ * x / s) :
    generalizedParetoPDF s ξ x = ENNReal.ofReal ((1 + ξ * x / s) ^ (-ξ⁻¹ - 1) / s) := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_shape_ne_zero hs hξ hx hb]

/-- At shape zero, the extended density is exponential on the positive half-line. -/
@[simp]
theorem generalizedParetoPDF_zero (hs : 0 < s) (x : ℝ) :
    generalizedParetoPDF s 0 x =
      if 0 < x then ENNReal.ofReal (Real.exp (-x / s) / s) else 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_zero hs]
  split_ifs <;> simp

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

private theorem transform_weight (hs : 0 < s) (ξ : ℝ) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal |s * Real.exp (ξ * e)| *
        generalizedParetoPDF s ξ (generalizedParetoMap s ξ e) = exponentialPDF 1 e := by
  have hb := one_add_mul_generalizedParetoMap_div hs.ne' ξ e
  have hx := generalizedParetoMap_pos hs ξ he
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
      simp [generalizedParetoPDF, generalizedParetoPDFReal_of_scale_nonpos hs]
    rw [generalizedParetoMeasure_of_nonpos hs, hzero, withDensity_zero]
  · let A : Set ℝ := {x | 0 < x ∧ 0 < 1 + ξ * x / s}
    have hA : MeasurableSet A := by dsimp [A]; measurability
    have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
      (s := Ioi (0 : ℝ)) (φ := generalizedParetoMap s ξ)
      (φ' := fun e ↦ s * Real.exp (ξ * e)) (f := generalizedParetoPDF s ξ)
      measurableSet_Ioi (measurable_generalizedParetoMap_right s ξ)
      (fun e _ ↦ (hasDerivAt_generalizedParetoMap s ξ e).hasDerivWithinAt)
      (strictMono_generalizedParetoMap hs ξ).injective.injOn
    have hw : (fun e ↦ ENNReal.ofReal |s * Real.exp (ξ * e)| *
        generalizedParetoPDF s ξ (generalizedParetoMap s ξ e)) =ᵐ[volume.restrict (Ioi 0)]
          exponentialPDF 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
      exact transform_weight hs ξ he
    rw [withDensity_congr_ae hw, image_generalizedParetoMap_Ioi hs] at hmap
    rw [generalizedParetoMeasure_of_pos hs, expMeasure_eq_withDensity_restrict_Ioi, hmap,
      ← withDensity_indicator hA]
    congr 1
    ext x
    by_cases hx : x ∈ A
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, generalizedParetoPDF,
        generalizedParetoPDFReal_of_not_pos hx, ENNReal.ofReal_zero]

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
      funext (generalizedParetoPDFReal_of_scale_nonpos hs ξ)
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

/-! ### Topological support -/

/-- At positive scale and nonnegative shape, the interior of the generalized Pareto support is
the positive half-line. -/
theorem setOf_generalizedPareto_eq_Ioi (hs : 0 < s) (hξ : 0 ≤ ξ) :
    {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s} = Ioi 0 := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_Ioi]
  exact and_iff_left_of_imp fun hx => by positivity

/-- At positive scale and negative shape, the interior of the generalized Pareto support is the
interval from zero to its finite upper endpoint. -/
theorem setOf_generalizedPareto_eq_Ioo (hs : 0 < s) (hξ : ξ < 0) :
    {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s} = Ioo 0 (-s / ξ) := by
  ext x
  rw [Set.mem_ofPred_eq, mem_Ioo, one_add_div hs.ne',
    div_pos_iff_of_pos_right hs, lt_div_iff_of_neg hξ]
  constructor <;> rintro ⟨hx, hbound⟩ <;> refine ⟨hx, ?_⟩ <;> nlinarith

/-- At positive scale, the function support of the generalized Pareto density is the interior of
the law's support. -/
@[simp]
theorem support_generalizedParetoPDF (hs : 0 < s) (ξ : ℝ) :
    Function.support (generalizedParetoPDF s ξ) =
      {x | 0 < x ∧ 0 < 1 + ξ * x / s} := by
  ext x
  rw [Function.mem_support, generalizedParetoPDF, ENNReal.ofReal_ne_zero_iff,
    generalizedParetoPDFReal_pos_iff, and_iff_right hs]
  rfl

/-- A positive-scale generalized Pareto law has support `[0, ∞)` at nonnegative shape and
`[0, -s / ξ]` at negative shape. -/
theorem support_generalizedParetoMeasure (hs : 0 < s) (ξ : ℝ) :
    (generalizedParetoMeasure s ξ).support =
      if 0 ≤ ξ then Ici 0 else Icc 0 (-s / ξ) := by
  have hopen : IsOpen {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s} :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const
        (continuous_const.add ((continuous_const.mul continuous_id).div_const s)))
  rw [generalizedParetoMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_generalizedParetoPDF s ξ) hopen
      (support_generalizedParetoPDF hs ξ)]
  split_ifs with hξ
  · rw [setOf_generalizedPareto_eq_Ioi hs hξ, closure_Ioi]
  · have hξneg : ξ < 0 := lt_of_not_ge hξ
    have hend : (0 : ℝ) ≠ -s / ξ := (div_pos_of_neg_of_neg (neg_neg_of_pos hs) hξneg).ne
    rw [setOf_generalizedPareto_eq_Ioo hs hξneg, closure_Ioo hend]

/-- A nonpositive scale gives the zero measure and hence empty topological support. -/
theorem support_generalizedParetoMeasure_of_nonpos (hs : s ≤ 0) (ξ : ℝ) :
    (generalizedParetoMeasure s ξ).support = ∅ := by
  rw [generalizedParetoMeasure_of_nonpos hs, Measure.support_zero]

end TauCeti.Probability
