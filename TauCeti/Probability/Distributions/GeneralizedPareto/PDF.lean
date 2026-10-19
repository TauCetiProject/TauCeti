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
# Density of the generalized Pareto distribution

For positive scale `s`, the generalized Pareto law with shape `ξ` has density

`s⁻¹ * (1 + ξ * x / s) ^ (-1 / ξ - 1)`

on `x > 0` and `1 + ξ * x / s > 0`. At shape zero this expression is understood as
`s⁻¹ * exp (-x / s)`. The density is zero outside the open support and when the scale is
nonpositive.

The measure identity is derived from the defining rate-one exponential pushforward. This also
identifies the topological support: `[0, ∞)` for nonnegative shape, and `[0, -s / ξ]` for
negative shape.

## Main results

* `TauCeti.Probability.generalizedParetoPDFReal` and
  `TauCeti.Probability.generalizedParetoPDF` are the real- and `ℝ≥0∞`-valued densities.
* `TauCeti.Probability.generalizedParetoMeasure_eq_withDensity` identifies the law with
  Lebesgue measure weighted by its density.
* `TauCeti.Probability.hasPDF_of_hasLaw_generalizedParetoMeasure`,
  `TauCeti.Probability.pdf_eq_generalizedParetoPDF_of_hasLaw_generalizedParetoMeasure`, and
  `TauCeti.Probability.rnDeriv_generalizedParetoMeasure` provide the standard density API.
* `TauCeti.Probability.support_generalizedParetoMeasure` gives the exact topological support.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

variable {s ξ x : ℝ}

/-! ### Densities -/

/-- The real-valued density of the generalized Pareto law.

It is zero outside the open support and for nonpositive scale. The separate shape-zero branch
is the continuous limiting exponential density. -/
def generalizedParetoPDFReal (s ξ x : ℝ) : ℝ :=
  if 0 < s ∧ 0 < x ∧ 0 < 1 + ξ * x / s then
    if ξ = 0 then Real.exp (-x / s) / s
    else s⁻¹ * (1 + ξ * x / s) ^ (-1 / ξ - 1)
  else 0

/-- The `ℝ≥0∞`-valued density of the generalized Pareto law. -/
def generalizedParetoPDF (s ξ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedParetoPDFReal s ξ x)

/-- The extended nonnegative density is `ENNReal.ofReal` of the real-valued density. -/
theorem generalizedParetoPDF_eq_ofReal (s ξ x : ℝ) :
    generalizedParetoPDF s ξ x = ENNReal.ofReal (generalizedParetoPDFReal s ξ x) :=
  (rfl)

/-- The generalized Pareto density is finite. -/
@[simp]
theorem generalizedParetoPDF_ne_top (s ξ x : ℝ) : generalizedParetoPDF s ξ x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- A nonpositive scale gives the zero real-valued density. -/
@[simp]
theorem generalizedParetoPDFReal_of_scale_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, not_lt.mpr hs]

/-- The real-valued density vanishes at nonpositive points. -/
@[simp]
theorem generalizedParetoPDFReal_of_nonpos (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, not_lt.mpr hx]

/-- The real-valued density vanishes beyond the finite endpoint of a negative-shape law. -/
@[simp]
theorem generalizedParetoPDFReal_of_one_add_nonpos (h : 1 + ξ * x / s ≤ 0) :
    generalizedParetoPDFReal s ξ x = 0 := by
  rw [generalizedParetoPDFReal, ite_eq_right]
  exact fun hsupp => (not_lt.mpr h) hsupp.2.2

/-- At positive scale and on the positive half-line, the shape-zero density is exponential. -/
theorem generalizedParetoPDFReal_zero (hs : 0 < s) (hx : 0 < x) :
    generalizedParetoPDFReal s 0 x = Real.exp (-x / s) / s := by
  simp [generalizedParetoPDFReal, hs, hx]

/-- The real-valued density has its power-law formula in the interior of its support. -/
theorem generalizedParetoPDFReal_of_shape_ne_zero (hs : 0 < s) (hx : 0 < x)
    (hsupp : 0 < 1 + ξ * x / s) (hξ : ξ ≠ 0) :
    generalizedParetoPDFReal s ξ x = s⁻¹ * (1 + ξ * x / s) ^ (-1 / ξ - 1) := by
  simp [generalizedParetoPDFReal, hs, hx, hsupp, hξ]

/-- The real-valued generalized Pareto density is nonnegative for all parameters. -/
theorem generalizedParetoPDFReal_nonneg (s ξ x : ℝ) :
    0 ≤ generalizedParetoPDFReal s ξ x := by
  simp only [generalizedParetoPDFReal]
  split_ifs with hvalid hξ
  · exact div_nonneg (Real.exp_pos _).le hvalid.1.le
  · exact mul_nonneg (inv_nonneg.mpr hvalid.1.le) (Real.rpow_nonneg hvalid.2.2.le _)
  · exact le_rfl

/-- The generalized Pareto density is positive exactly in the interior of its support, provided
the scale is positive. -/
theorem generalizedParetoPDFReal_pos_iff (hs : 0 < s) :
    0 < generalizedParetoPDFReal s ξ x ↔ 0 < x ∧ 0 < 1 + ξ * x / s := by
  rw [generalizedParetoPDFReal]
  simp only [hs, true_and]
  constructor
  · split_ifs <;> simp_all
  · intro h
    rw [ite_eq_left h]
    split_ifs
    · positivity
    · exact mul_pos (inv_pos.mpr hs) (Real.rpow_pos_of_pos h.2 _)

/-- A nonpositive scale gives the zero `ℝ≥0∞`-valued density. -/
@[simp]
theorem generalizedParetoPDF_of_scale_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_scale_nonpos hs,
    ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes at nonpositive points. -/
@[simp]
theorem generalizedParetoPDF_of_nonpos (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_nonpos hx,
    ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes beyond the finite endpoint of a negative-shape law. -/
@[simp]
theorem generalizedParetoPDF_of_one_add_nonpos (h : 1 + ξ * x / s ≤ 0) :
    generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_one_add_nonpos h,
    ENNReal.ofReal_zero]

/-- At positive scale and on the positive half-line, the shape-zero extended density is
exponential. -/
theorem generalizedParetoPDF_zero (hs : 0 < s) (hx : 0 < x) :
    generalizedParetoPDF s 0 x = ENNReal.ofReal (Real.exp (-x / s) / s) := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_zero hs hx]

/-- The extended density has its power-law formula in the interior of its support. -/
theorem generalizedParetoPDF_of_shape_ne_zero (hs : 0 < s) (hx : 0 < x)
    (hsupp : 0 < 1 + ξ * x / s) (hξ : ξ ≠ 0) :
    generalizedParetoPDF s ξ x =
      ENNReal.ofReal (s⁻¹ * (1 + ξ * x / s) ^ (-1 / ξ - 1)) := by
  rw [generalizedParetoPDF_eq_ofReal,
    generalizedParetoPDFReal_of_shape_ne_zero hs hx hsupp hξ]

/-- The extended generalized Pareto density is positive exactly in the interior of its support,
provided the scale is positive. -/
theorem generalizedParetoPDF_pos_iff (hs : 0 < s) :
    0 < generalizedParetoPDF s ξ x ↔ 0 < x ∧ 0 < 1 + ξ * x / s := by
  rw [generalizedParetoPDF_eq_ofReal, ENNReal.ofReal_pos, generalizedParetoPDFReal_pos_iff hs]

/-- Converting the extended nonnegative density to `ℝ` recovers the real-valued density. -/
@[simp]
theorem toReal_generalizedParetoPDF (s ξ x : ℝ) :
    (generalizedParetoPDF s ξ x).toReal = generalizedParetoPDFReal s ξ x := by
  rw [generalizedParetoPDF, ENNReal.toReal_ofReal (generalizedParetoPDFReal_nonneg s ξ x)]

/-- The real-valued generalized Pareto density is jointly measurable in scale, shape, and the
evaluation point. -/
@[fun_prop]
theorem measurable_uncurry_generalizedParetoPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ => generalizedParetoPDFReal q.1.1 q.1.2 q.2 := by
  unfold generalizedParetoPDFReal
  exact Measurable.ite (by measurability)
    (Measurable.ite (by measurability) (by fun_prop) (by fun_prop)) measurable_const

/-- The `ℝ≥0∞`-valued generalized Pareto density is jointly measurable. -/
@[fun_prop]
theorem measurable_uncurry_generalizedParetoPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => generalizedParetoPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_generalizedParetoPDFReal.ennreal_ofReal

/-- The real-valued generalized Pareto density is measurable. -/
@[fun_prop]
theorem measurable_generalizedParetoPDFReal (s ξ : ℝ) :
    Measurable (generalizedParetoPDFReal s ξ) :=
  measurable_uncurry_generalizedParetoPDFReal.comp (measurable_prodMk_left (x := (s, ξ)))

/-- The `ℝ≥0∞`-valued generalized Pareto density is measurable. -/
@[fun_prop]
theorem measurable_generalizedParetoPDF (s ξ : ℝ) : Measurable (generalizedParetoPDF s ξ) :=
  (measurable_generalizedParetoPDFReal s ξ).ennreal_ofReal

/-! ### Density of the measure -/

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
    generalizedParetoPDFReal_pos_iff hs]
  rfl

private theorem generalizedParetoMap_weight (hs : 0 < s) (hξ : ξ ≠ 0) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal |s * Real.exp (ξ * e)| *
        generalizedParetoPDF s ξ (generalizedParetoMap s ξ e) = exponentialPDF 1 e := by
  have hmap_pos := generalizedParetoMap_pos hs hξ he
  have hbase := generalizedParetoMap_base hs hξ e
  rw [generalizedParetoPDF, generalizedParetoPDFReal_of_shape_ne_zero hs hmap_pos
    (hbase ▸ Real.exp_pos _) hξ, exponentialPDF_of_nonneg he.le, abs_of_pos
    (mul_pos hs (Real.exp_pos _)), ← ENNReal.ofReal_mul
    (mul_nonneg hs.le (Real.exp_pos _).le)]
  congr 1
  have hexponent : ξ * e * (-1 / ξ - 1) = -e + -(ξ * e) := by
    field_simp [hξ]
    ring
  rw [hbase, ← Real.exp_mul, hexponent, Real.exp_add, Real.exp_neg]
  field_simp [hs.ne']
  calc
    Real.exp (ξ * e) * Real.exp (-(ξ * e)) = Real.exp (ξ * e + -(ξ * e)) :=
      (Real.exp_add _ _).symm
    _ = Real.exp (e + -e) := by ring_nf
    _ = Real.exp e * Real.exp (-e) := Real.exp_add _ _

/-- The generalized Pareto law is Lebesgue measure weighted by its density, for every parameter
value. -/
theorem generalizedParetoMeasure_eq_withDensity (s ξ : ℝ) :
    generalizedParetoMeasure s ξ = volume.withDensity (generalizedParetoPDF s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hpdf : generalizedParetoPDF s ξ = 0 :=
      funext (generalizedParetoPDF_of_scale_nonpos hs ξ)
    rw [generalizedParetoMeasure_of_nonpos hs, hpdf, withDensity_zero]
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · rw [generalizedParetoMeasure_zero hs, expMeasure_eq_withDensity]
      apply withDensity_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := volume) (0 : ℝ))] with x hx
      have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.mp hx
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · rw [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos hxneg.le,
          exponentialPDF_of_neg hxneg, ENNReal.ofReal_zero]
      · rw [generalizedParetoPDF, generalizedParetoPDFReal_zero hs hxpos,
          exponentialPDF_of_nonneg hxpos.le]
        apply congrArg ENNReal.ofReal
        rw [div_eq_mul_inv]
        ring_nf
    · have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
        (s := Ioi (0 : ℝ)) (φ := generalizedParetoMap s ξ)
        (φ' := fun e => s * Real.exp (ξ * e)) (f := generalizedParetoPDF s ξ)
        measurableSet_Ioi (measurable_generalizedParetoMap_right s ξ)
        (fun e _ => (generalizedParetoMap_deriv hξ e).hasDerivWithinAt)
        (strictMono_generalizedParetoMap hs ξ).injective.injOn
      have hweight :
          (fun e : ℝ => ENNReal.ofReal |s * Real.exp (ξ * e)| *
            generalizedParetoPDF s ξ (generalizedParetoMap s ξ e))
            =ᵐ[volume.restrict (Ioi 0)] exponentialPDF 1 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
        exact generalizedParetoMap_weight hs hξ he
      rw [withDensity_congr_ae hweight, image_generalizedParetoMap_Ioi hs hξ] at hmap
      rw [generalizedParetoMeasure_of_pos hs, expMeasure_eq_withDensity_restrict_Ioi, hmap,
        ← withDensity_indicator (by measurability : MeasurableSet
          {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s}),
        Set.indicator_eq_self.2 (support_generalizedParetoPDF hs ξ).subset]

/-- The `ℝ≥0∞`-valued generalized Pareto density has total mass `1` at positive scale. -/
theorem lintegral_generalizedParetoPDF_eq_one (hs : 0 < s) (ξ : ℝ) :
    ∫⁻ x, generalizedParetoPDF s ξ x = 1 := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  have h : generalizedParetoMeasure s ξ Set.univ = 1 := measure_univ
  rwa [generalizedParetoMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The real-valued generalized Pareto density has integral `1` at positive scale. -/
theorem integral_generalizedParetoPDFReal_eq_one (hs : 0 < s) (ξ : ℝ) :
    ∫ x, generalizedParetoPDFReal s ξ x = 1 := by
  simp_rw [← toReal_generalizedParetoPDF]
  rw [integral_toReal (measurable_generalizedParetoPDF s ξ).aemeasurable
      (ae_of_all _ fun x => lt_top_iff_ne_top.mpr (generalizedParetoPDF_ne_top s ξ x)),
    lintegral_generalizedParetoPDF_eq_one hs ξ, ENNReal.toReal_one]

/-- The real-valued generalized Pareto density is integrable for every scale and shape. -/
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

/-! ### Transfer to the density -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is integrable against a generalized Pareto measure exactly when its
density-weighted version is Lebesgue integrable. This includes the zero-measure branch. -/
theorem integrable_generalizedParetoMeasure_iff (s ξ : ℝ) {g : ℝ → E} :
    Integrable g (generalizedParetoMeasure s ξ) ↔
      Integrable fun y => generalizedParetoPDFReal s ξ y • g y := by
  rw [generalizedParetoMeasure_eq_withDensity, funext (generalizedParetoPDF_eq_ofReal s ξ)]
  exact integrable_withDensity_ofReal_iff (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ))

/-- An integral against a generalized Pareto measure is the corresponding density-weighted
Lebesgue integral. This includes the zero-measure branch. -/
theorem integral_generalizedParetoMeasure_eq (s ξ : ℝ) (g : ℝ → E) :
    ∫ y, g y ∂generalizedParetoMeasure s ξ =
      ∫ y, generalizedParetoPDFReal s ξ y • g y := by
  rw [generalizedParetoMeasure_eq_withDensity, funext (generalizedParetoPDF_eq_ofReal s ξ)]
  exact integral_withDensity_ofReal (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ)) g

end Transfer

/-! ### Standard density API -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a generalized Pareto law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_generalizedParetoMeasure
    (hX : HasLaw X (generalizedParetoMeasure s ξ) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_generalizedParetoPDF s ξ).aemeasurable
    (by rwa [generalizedParetoMeasure_eq_withDensity] at hX)

/-- The canonical density of a generalized Pareto random variable is
`generalizedParetoPDF`. -/
theorem pdf_eq_generalizedParetoPDF_of_hasLaw_generalizedParetoMeasure
    (hX : HasLaw X (generalizedParetoMeasure s ξ) P) :
    pdf X P volume =ᵐ[volume] generalizedParetoPDF s ξ :=
  pdf_eq_of_hasLaw_withDensity (measurable_generalizedParetoPDF s ξ).aemeasurable
    (by rwa [generalizedParetoMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a generalized Pareto law against Lebesgue measure is its
density. -/
theorem rnDeriv_generalizedParetoMeasure (s ξ : ℝ) :
    (generalizedParetoMeasure s ξ).rnDeriv volume =ᵐ[volume] generalizedParetoPDF s ξ := by
  rw [generalizedParetoMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_generalizedParetoPDF s ξ)

/-! ### Topological support -/

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
