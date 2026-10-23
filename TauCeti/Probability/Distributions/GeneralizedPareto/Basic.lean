/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
import TauCeti.MeasureTheory.Measure.Atom
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# The generalized Pareto distribution

The generalized Pareto law with scale `s > 0` and shape `ξ` is obtained from a rate-one
exponential variable `E`. For nonzero shape, the transformation is

`s * (exp (ξ * E) - 1) / ξ`,

while at shape zero it is `s * E`. Thus the zero-shape law is the exponential law with rate
`s⁻¹`. A nonpositive scale gives the zero measure.

This file provides the construction, its probability and parameter-measurability interfaces,
and closure under positive scaling. These are the measure-level foundations for the density,
cdf, quantile, moment, threshold-stability, and exponential-integrability theory of the family.

## Main definitions

* `TauCeti.Probability.generalizedParetoMap` is the transformation of a rate-one exponential
  variable.
* `TauCeti.Probability.generalizedParetoMeasure` is its pushforward law.

## Main results

* `generalizedParetoMeasure_zero` identifies the zero-shape law with an exponential law.
* `generalizedParetoMap_log_div` gives the logarithmic inverse at nonzero shape.
* `isProbabilityMeasure_generalizedParetoMeasure` proves normalization at positive scale.
* `hasLaw_generalizedParetoMeasure_of_hasLaw_expMeasure` gives the random-variable construction.
* `map_mul_generalizedParetoMeasure` gives positive scaling.
* `measurable_generalizedParetoMeasure` proves joint parameter measurability.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The exponential-variable transformation defining the generalized Pareto family.

At shape zero this is multiplication by the scale. At nonzero shape it is
`e ↦ s * (exp (ξ * e) - 1) / ξ`. -/
def generalizedParetoMap (s ξ e : ℝ) : ℝ :=
  if ξ = 0 then s * e else s * (Real.exp (ξ * e) - 1) / ξ

/-- At shape zero, the generalized Pareto transformation is multiplication by its scale. -/
@[simp]
theorem generalizedParetoMap_zero (s e : ℝ) :
    generalizedParetoMap s 0 e = s * e := by
  simp [generalizedParetoMap]

/-- At nonzero shape, the generalized Pareto transformation uses its exponential formula. -/
theorem generalizedParetoMap_of_shape_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) (s e : ℝ) :
    generalizedParetoMap s ξ e = s * (Real.exp (ξ * e) - 1) / ξ := by
  simp [generalizedParetoMap, hξ]

/-- The generalized Pareto transformation sends input zero to zero at every scale and shape. -/
@[simp]
theorem generalizedParetoMap_apply_zero (s ξ : ℝ) : generalizedParetoMap s ξ 0 = 0 := by
  simp [generalizedParetoMap]

/-- The generalized Pareto transformation is measurable jointly in scale, shape, and input. -/
@[fun_prop]
theorem measurable_generalizedParetoMap :
    Measurable fun p : (ℝ × ℝ) × ℝ => generalizedParetoMap p.1.1 p.1.2 p.2 := by
  simp only [generalizedParetoMap]
  exact Measurable.ite (measurableSet_eq_fun measurable_fst.snd measurable_const) (by fun_prop)
    (by fun_prop)

/-- The generalized Pareto transformation is measurable in its exponential input. -/
@[fun_prop]
theorem measurable_generalizedParetoMap_right (s ξ : ℝ) :
    Measurable (generalizedParetoMap s ξ) :=
  measurable_generalizedParetoMap.comp
    ((measurable_const.prodMk measurable_const).prodMk measurable_id)

/-- The generalized Pareto transformation is continuous in its exponential input. -/
@[fun_prop]
theorem continuous_generalizedParetoMap_right (s ξ : ℝ) :
    Continuous (generalizedParetoMap s ξ) := by
  unfold generalizedParetoMap
  split_ifs <;> fun_prop

/-- At positive scale the generalized Pareto transformation is strictly increasing, for every
real shape. -/
theorem strictMono_generalizedParetoMap {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    StrictMono (generalizedParetoMap s ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    intro a b hab
    simpa only [generalizedParetoMap_zero] using mul_lt_mul_of_pos_left hab hs
  intro a b hab
  simp only [generalizedParetoMap_of_shape_ne_zero hξ]
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · apply (div_lt_div_right_of_neg hξ).2
    exact mul_lt_mul_of_pos_left
      (sub_lt_sub_right (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hab hξ)) 1) hs
  · apply (div_lt_div_iff_of_pos_right hξ).2
    exact mul_lt_mul_of_pos_left
      (sub_lt_sub_right (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hξ)) 1) hs

/-- At positive scale the generalized Pareto transformation preserves nonnegativity. -/
@[simp]
theorem generalizedParetoMap_nonneg_iff {s : ℝ} (hs : 0 < s) (ξ e : ℝ) :
    0 ≤ generalizedParetoMap s ξ e ↔ 0 ≤ e := by
  simpa only [generalizedParetoMap_apply_zero] using
    (strictMono_generalizedParetoMap hs ξ).le_iff_le (a := 0) (b := e)

/-- At nonzero scale and shape, the logarithmic formula inverts the generalized Pareto
transformation wherever its logarithm has positive argument. -/
@[simp]
theorem generalizedParetoMap_log_div {s ξ x : ℝ} (hs : s ≠ 0) (hξ : ξ ≠ 0)
    (hw : 0 < 1 + ξ * x / s) :
    generalizedParetoMap s ξ (Real.log (1 + ξ * x / s) / ξ) = x := by
  rw [generalizedParetoMap_of_shape_ne_zero hξ, mul_div_cancel₀ _ hξ, Real.exp_log hw]
  field_simp
  ring

/-- The generalized Pareto transformation has derivative `s * exp (ξ * e)` at every input. -/
theorem hasDerivAt_generalizedParetoMap (s ξ e : ℝ) :
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

/-- At positive scale, the generalized Pareto transformation sends positive inputs to positive
values. -/
theorem generalizedParetoMap_pos {s : ℝ} (hs : 0 < s) (ξ : ℝ) {e : ℝ} (he : 0 < e) :
    0 < generalizedParetoMap s ξ e := by
  simpa only [generalizedParetoMap_apply_zero] using strictMono_generalizedParetoMap hs ξ he

/-- The affine support factor of the generalized Pareto transformation is exponential at nonzero
scale. -/
theorem one_add_mul_generalizedParetoMap_div {s : ℝ} (hs : s ≠ 0) (ξ e : ℝ) :
    1 + ξ * generalizedParetoMap s ξ e / s = Real.exp (ξ * e) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [generalizedParetoMap_of_shape_ne_zero hξ]
    field_simp
    ring

/-- At positive scale, the image of the positive half-line is the open generalized Pareto
support. -/
theorem image_generalizedParetoMap_Ioi {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    generalizedParetoMap s ξ '' Ioi 0 = {x | 0 < x ∧ 0 < 1 + ξ * x / s} := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨generalizedParetoMap_pos hs ξ he, ?_⟩
    rw [one_add_mul_generalizedParetoMap_div hs.ne']
    exact Real.exp_pos _
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
      · exact generalizedParetoMap_log_div hs.ne' hξ hb

/-- At nonzero scale and shape, the image of the whole line is the generalized Pareto domain
where the affine support factor is positive. -/
theorem image_generalizedParetoMap_univ {s ξ : ℝ} (hs : s ≠ 0) (hξ : ξ ≠ 0) :
    generalizedParetoMap s ξ '' univ = {x | 0 < 1 + ξ * x / s} := by
  ext x
  constructor
  · rintro ⟨e, -, rfl⟩
    rw [Set.mem_ofPred_eq, one_add_mul_generalizedParetoMap_div hs]
    exact Real.exp_pos _
  · intro hx
    exact ⟨_, mem_univ _, generalizedParetoMap_log_div hs hξ hx⟩

/-- The generalized Pareto measure with scale `s` and shape `ξ`.

For positive scale this is the pushforward of a rate-one exponential law by
`generalizedParetoMap`. For nonpositive scale it is the zero measure. -/
def generalizedParetoMeasure (s ξ : ℝ) : Measure ℝ :=
  if 0 < s then (expMeasure 1).map (generalizedParetoMap s ξ) else 0

/-- For positive scale, the generalized Pareto law is its prescribed exponential pushforward. -/
theorem generalizedParetoMeasure_of_pos {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    generalizedParetoMeasure s ξ = (expMeasure 1).map (generalizedParetoMap s ξ) := by
  simp [generalizedParetoMeasure, hs]

/-- A nonpositive scale gives the zero generalized Pareto measure. -/
@[simp]
theorem generalizedParetoMeasure_of_nonpos {s : ℝ} (hs : s ≤ 0) (ξ : ℝ) :
    generalizedParetoMeasure s ξ = 0 := by
  simp [generalizedParetoMeasure, not_lt.mpr hs]

/-- The zero-shape generalized Pareto law with positive scale is the exponential law with rate
`s⁻¹`. -/
@[simp]
theorem generalizedParetoMeasure_zero {s : ℝ} (hs : 0 < s) :
    generalizedParetoMeasure s 0 = expMeasure s⁻¹ := by
  calc
    generalizedParetoMeasure s 0 = (expMeasure 1).map (s * ·) := by
      rw [generalizedParetoMeasure_of_pos hs]
      congr 1
      funext e
      exact generalizedParetoMap_zero s e
    _ = expMeasure s⁻¹ := by
      simpa only [expMeasure, one_div] using gammaMeasure_map_const_mul one_pos one_pos hs

/-- For nonzero shape and positive scale, the generalized Pareto law is the pushforward of a
rate-one exponential law under `e ↦ s * (exp (ξ * e) - 1) / ξ`. -/
theorem generalizedParetoMeasure_of_shape_ne_zero {s ξ : ℝ} (hs : 0 < s) (hξ : ξ ≠ 0) :
    generalizedParetoMeasure s ξ =
      (expMeasure 1).map fun e => s * (Real.exp (ξ * e) - 1) / ξ := by
  rw [generalizedParetoMeasure_of_pos hs]
  congr 1
  funext e
  exact generalizedParetoMap_of_shape_ne_zero hξ s e

/-- A generalized Pareto law with positive scale is a probability measure. -/
theorem isProbabilityMeasure_generalizedParetoMeasure {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    IsProbabilityMeasure (generalizedParetoMeasure s ξ) := by
  rw [generalizedParetoMeasure_of_pos hs]
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  infer_instance

/-- A generalized Pareto variable lies almost surely in its open positive support.
The statement includes the zero law at nonpositive scale. -/
theorem ae_pos_and_one_add_mul_div_pos_generalizedParetoMeasure (s ξ : ℝ) :
    ∀ᵐ x ∂generalizedParetoMeasure s ξ, 0 < x ∧ 0 < 1 + ξ * x / s := by
  rcases le_or_gt s 0 with hs | hs
  · simp [generalizedParetoMeasure_of_nonpos hs]
  rw [generalizedParetoMeasure_of_pos hs,
    ae_map_iff (measurable_generalizedParetoMap_right s ξ).aemeasurable (by measurability)]
  filter_upwards [ae_pos_expMeasure 1] with e he
  refine ⟨generalizedParetoMap_pos hs ξ he, ?_⟩
  rw [one_add_mul_generalizedParetoMap_div hs.ne']
  exact Real.exp_pos _

/-- Every singleton has zero generalized Pareto measure at positive scale. -/
theorem nullSingletonClass_generalizedParetoMeasure {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    NullSingletonClass (generalizedParetoMeasure s ξ) := by
  rw [generalizedParetoMeasure_of_pos hs]
  exact Measure.nullSingletonClass_map_of_injective
    (measurable_generalizedParetoMap_right s ξ) (strictMono_generalizedParetoMap hs ξ).injective

/-- A variable obtained from a rate-one exponential variable by the generalized Pareto
transformation has the corresponding generalized Pareto law. -/
theorem hasLaw_generalizedParetoMeasure_of_hasLaw_expMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℝ}
    {s : ℝ} (hs : 0 < s) (ξ : ℝ) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => generalizedParetoMap s ξ (E ω))
      (generalizedParetoMeasure s ξ) P := by
  rw [generalizedParetoMeasure_of_pos hs]
  exact (hasLaw_map (measurable_generalizedParetoMap_right s ξ).aemeasurable).comp hE

/-- If `E` has the rate-one exponential law, then its nonzero-shape exponential transformation
has the corresponding generalized Pareto law. -/
theorem hasLaw_generalizedParetoMeasure_of_hasLaw_expMeasure_of_shape_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℝ}
    {s ξ : ℝ} (hs : 0 < s) (hξ : ξ ≠ 0) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => s * (Real.exp (ξ * E ω) - 1) / ξ)
      (generalizedParetoMeasure s ξ) P := by
  rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ]
  exact (hasLaw_map (by fun_prop : Measurable fun e : ℝ =>
    s * (Real.exp (ξ * e) - 1) / ξ).aemeasurable).comp hE

/-- Multiplication by a positive constant rescales a generalized Pareto law and leaves its shape
fixed. The equality also respects the nonpositive-scale zero branch. -/
theorem map_mul_generalizedParetoMeasure {c : ℝ} (hc : 0 < c) (s ξ : ℝ) :
    (generalizedParetoMeasure s ξ).map (c * ·) = generalizedParetoMeasure (c * s) ξ := by
  rcases le_or_gt s 0 with hs | hs
  · rw [generalizedParetoMeasure_of_nonpos hs,
      generalizedParetoMeasure_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc.le hs),
      Measure.map_zero]
  · rw [generalizedParetoMeasure_of_pos hs,
      generalizedParetoMeasure_of_pos (mul_pos hc hs),
      Measure.map_map (by fun_prop) (measurable_generalizedParetoMap_right s ξ)]
    congr 1
    funext e
    simp only [Function.comp_apply, generalizedParetoMap]
    split_ifs <;> ring

/-- The random-variable form of positive scaling for generalized Pareto laws. -/
theorem hasLaw_mul_generalizedParetoMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {s ξ c : ℝ} (hc : 0 < c) (hX : HasLaw X (generalizedParetoMeasure s ξ) P) :
    HasLaw (fun ω => c * X ω) (generalizedParetoMeasure (c * s) ξ) P := by
  rw [← map_mul_generalizedParetoMeasure hc]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ => c * x).aemeasurable).comp hX

/-- The generalized Pareto family is jointly measurable in scale and shape, including the
nonpositive-scale zero-measure branch. -/
@[fun_prop]
theorem measurable_generalizedParetoMeasure :
    Measurable fun p : ℝ × ℝ => generalizedParetoMeasure p.1 p.2 := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
  · exact TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
      (ν := expMeasure 1) (f := fun p : ℝ × ℝ => generalizedParetoMap p.1 p.2)
      measurable_generalizedParetoMap
  · exact measurable_const

end TauCeti.Probability
