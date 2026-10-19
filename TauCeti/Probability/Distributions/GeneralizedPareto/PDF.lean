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
theorem generalizedParetoPDFReal_of_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDFReal s ξ x = 0 := by
  simp [generalizedParetoPDFReal, not_lt.mpr hs]

/-- The real-valued density vanishes at nonpositive points. -/
@[simp]
theorem generalizedParetoPDFReal_of_nonpos_argument (hx : x ≤ 0) (s ξ : ℝ) :
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
theorem generalizedParetoPDF_of_nonpos (hs : s ≤ 0) (ξ x : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_nonpos hs, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes at nonpositive points. -/
@[simp]
theorem generalizedParetoPDF_of_nonpos_argument (hx : x ≤ 0) (s ξ : ℝ) :
    generalizedParetoPDF s ξ x = 0 := by
  rw [generalizedParetoPDF_eq_ofReal, generalizedParetoPDFReal_of_nonpos_argument hx,
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

private theorem generalizedParetoMap_deriv (hξ : ξ ≠ 0) (e : ℝ) :
    HasDerivAt (generalizedParetoMap s ξ) (s * Real.exp (ξ * e)) e := by
  have hraw : HasDerivAt (fun y => s * (Real.exp (ξ * y) - 1) / ξ)
      (s * (Real.exp (ξ * e) * ξ) / ξ) e := by
    simpa only [Function.comp_apply] using
      ((((Real.hasDerivAt_exp (ξ * e)).comp e (hasDerivAt_const_mul ξ)).sub_const 1).const_mul
        s).div_const ξ
  convert hraw using 1
  · funext y
    rw [generalizedParetoMap_of_shape_ne_zero hξ]
  · field_simp [hξ]

private theorem generalizedParetoMap_base (hs : 0 < s) (hξ : ξ ≠ 0) (e : ℝ) :
    1 + ξ * generalizedParetoMap s ξ e / s = Real.exp (ξ * e) := by
  rw [generalizedParetoMap_of_shape_ne_zero hξ]
  field_simp
  ring

private theorem generalizedParetoMap_pos (hs : 0 < s) (hξ : ξ ≠ 0) {e : ℝ} (he : 0 < e) :
    0 < generalizedParetoMap s ξ e := by
  rw [generalizedParetoMap_of_shape_ne_zero hξ]
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hs (sub_neg.mpr
      ((Real.exp_lt_one_iff).mpr (mul_neg_of_neg_of_pos hξ he)))) hξ
  · exact div_pos (mul_pos hs (sub_pos.mpr ((Real.one_lt_exp_iff).mpr (mul_pos hξ he)))) hξ

private theorem image_generalizedParetoMap_Ioi (hs : 0 < s) (hξ : ξ ≠ 0) :
    generalizedParetoMap s ξ '' Ioi 0 = {x | 0 < x ∧ 0 < 1 + ξ * x / s} := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨generalizedParetoMap_pos hs hξ he,
      generalizedParetoMap_base hs hξ e ▸ Real.exp_pos _⟩
  · rintro ⟨hx, hsupp⟩
    let e := Real.log (1 + ξ * x / s) / ξ
    have he : 0 < e := by
      rcases lt_or_gt_of_ne hξ with hξneg | hξpos
      · have hbase_lt : 1 + ξ * x / s < 1 := by
          have : ξ * x / s < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hξneg hx) hs
          linarith
        exact div_pos_of_neg_of_neg (Real.log_neg hsupp hbase_lt) hξneg
      · have hbase : 1 < 1 + ξ * x / s := by
          have : 0 < ξ * x / s := div_pos (mul_pos hξpos hx) hs
          linarith
        exact div_pos (Real.log_pos hbase) hξpos
    refine ⟨e, he, ?_⟩
    have hξe : ξ * e = Real.log (1 + ξ * x / s) := by
      dsimp [e]
      field_simp
    rw [generalizedParetoMap_of_shape_ne_zero hξ, hξe, Real.exp_log hsupp]
    field_simp
    ring

private theorem generalizedParetoMap_injOn (hs : 0 < s) (hξ : ξ ≠ 0) :
    InjOn (generalizedParetoMap s ξ) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro a _ha b _hb hab
  rw [generalizedParetoMap_of_shape_ne_zero hξ,
    generalizedParetoMap_of_shape_ne_zero hξ]
  rcases lt_or_gt_of_ne hξ with hξneg | hξpos
  · apply (div_lt_div_right_of_neg hξneg).2
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right (Real.exp_lt_exp.mpr
      (mul_lt_mul_of_neg_left hab hξneg)) 1) hs
  · exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (sub_lt_sub_right (Real.exp_lt_exp.mpr
        (mul_lt_mul_of_pos_left hab hξpos)) 1) hs) hξpos

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
  rw [hbase, ← Real.exp_mul]
  field_simp [hs.ne']
  rw [← Real.exp_add]
  congr 1
  field_simp [hξ]
  ring

private theorem indicator_generalizedParetoPDF :
    {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s}.indicator (generalizedParetoPDF s ξ) =
      generalizedParetoPDF s ξ := by
  ext x
  by_cases hx : x ∈ {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s}
  · simp [hx]
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hx
    rcases hx with hx | hx
    · rw [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos_argument hx]
      exact ENNReal.ofReal_zero.symm
    · rw [generalizedParetoPDF, generalizedParetoPDFReal_of_one_add_nonpos hx]
      exact ENNReal.ofReal_zero.symm

/-- The generalized Pareto law is Lebesgue measure weighted by its density, for every parameter
value. -/
theorem generalizedParetoMeasure_eq_withDensity (s ξ : ℝ) :
    generalizedParetoMeasure s ξ = volume.withDensity (generalizedParetoPDF s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hpdf : generalizedParetoPDF s ξ = 0 := funext fun x => by
      simp [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos hs]
    rw [generalizedParetoMeasure_of_nonpos hs, hpdf, withDensity_zero]
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · rw [generalizedParetoMeasure_zero hs, expMeasure_eq_withDensity]
      apply withDensity_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := volume) (0 : ℝ))] with x hx
      have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.mp hx
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · rw [generalizedParetoPDF, generalizedParetoPDFReal_of_nonpos_argument hxneg.le,
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
        (generalizedParetoMap_injOn hs hξ)
      have hweight :
          (fun e : ℝ => ENNReal.ofReal |s * Real.exp (ξ * e)| *
            generalizedParetoPDF s ξ (generalizedParetoMap s ξ e))
            =ᵐ[volume.restrict (Ioi 0)] exponentialPDF 1 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
        exact generalizedParetoMap_weight hs hξ he
      rw [withDensity_congr_ae hweight, image_generalizedParetoMap_Ioi hs hξ] at hmap
      rw [generalizedParetoMeasure_of_pos hs, expMeasure_eq_withDensity_restrict_Ioi, hmap,
        ← withDensity_indicator (by measurability : MeasurableSet
          {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s}), indicator_generalizedParetoPDF]

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
  · have hset : {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s} = Ioi 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_Ioi]
      exact and_iff_left_of_imp fun hx => by positivity
    rw [hset, closure_Ioi]
  · have hξneg : ξ < 0 := lt_of_not_ge hξ
    have hset : {x : ℝ | 0 < x ∧ 0 < 1 + ξ * x / s} = Ioo 0 (-s / ξ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨hx, hsupp⟩
        refine ⟨hx, ?_⟩
        rw [lt_div_iff_of_neg hξneg]
        have := (mul_pos hs hsupp)
        field_simp at this ⊢
        linarith
      · rintro ⟨hx, hupper⟩
        refine ⟨hx, ?_⟩
        have hrewrite : 1 + ξ * x / s = (s + ξ * x) / s := by field_simp
        rw [hrewrite]
        apply div_pos
        · rw [lt_div_iff_of_neg hξneg] at hupper
          nlinarith
        · exact hs
    have hend : (0 : ℝ) ≠ -s / ξ := (div_pos_of_neg_of_neg (neg_neg_of_pos hs) hξneg).ne
    rw [hset, closure_Ioo hend]

/-- A nonpositive scale gives the zero measure and hence empty topological support. -/
theorem support_generalizedParetoMeasure_of_nonpos (hs : s ≤ 0) (ξ : ℝ) :
    (generalizedParetoMeasure s ξ).support = ∅ := by
  rw [generalizedParetoMeasure_of_nonpos hs, Measure.support_zero]

end TauCeti.Probability
