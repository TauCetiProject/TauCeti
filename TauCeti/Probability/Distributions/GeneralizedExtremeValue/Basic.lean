/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The generalized extreme-value distribution

The generalized extreme-value law in the maximum convention is obtained from a rate-one
exponential variable `E`. For nonzero shape `ξ`, the transformation is

`m + s * (E ^ (-ξ) - 1) / ξ`,

while at shape zero it is the Gumbel transformation `m - s * log E`. The latter branch makes
the family agree exactly with `gumbelMeasure m s` at `ξ = 0`. As for the Gumbel law, a
nonpositive scale gives the zero measure.

This file provides the construction, its probability and parameter-measurability interfaces,
and closure under positive affine maps. These are the measure-level foundations for the cdf,
quantile, moment, and maximum-stability theory of the family.

## Main definitions

* `TauCeti.Probability.generalizedExtremeValueMap` is the transformation of a rate-one
  exponential variable.
* `TauCeti.Probability.generalizedExtremeValueMeasure` is its pushforward law.

## Main results

* `generalizedExtremeValueMeasure_zero` identifies the zero-shape law with Gumbel.
* `isProbabilityMeasure_generalizedExtremeValueMeasure` proves normalization at positive scale.
* `hasLaw_generalizedExtremeValueMeasure_of_hasLaw_expMeasure` gives the random-variable
  construction.
* `map_affine_generalizedExtremeValueMeasure` gives positive affine transport.
* `measurable_generalizedExtremeValueMeasure` proves joint parameter measurability.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The exponential-variable transformation defining the generalized extreme-value family.

At shape zero this is the Gumbel transformation. For nonzero shape, the exponential expression
is `e ^ (-ξ)` whenever `e > 0`; writing it as `exp (-ξ * log e)` gives a jointly measurable
totalization on all real inputs. -/
def generalizedExtremeValueMap (m s ξ e : ℝ) : ℝ :=
  if ξ = 0 then m - s * Real.log e
  else m + s * (Real.exp (-ξ * Real.log e) - 1) / ξ

/-- At shape zero, the generalized extreme-value transformation is the Gumbel transformation. -/
@[simp]
theorem generalizedExtremeValueMap_zero (m s e : ℝ) :
    generalizedExtremeValueMap m s 0 e = m - s * Real.log e := by
  simp [generalizedExtremeValueMap]

/-- At nonzero shape, the generalized extreme-value transformation is
`m + s * (exp (-ξ * log e) - 1) / ξ`. -/
theorem generalizedExtremeValueMap_of_shape_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) (m s e : ℝ) :
    generalizedExtremeValueMap m s ξ e =
      m + s * (Real.exp (-ξ * Real.log e) - 1) / ξ := by
  simp [generalizedExtremeValueMap, hξ]

/-- On positive inputs, the generalized extreme-value transformation uses the usual real power
`e ^ (-ξ)`. -/
theorem generalizedExtremeValueMap_eq_rpow {e : ℝ} (he : 0 < e) (m s ξ : ℝ) :
    generalizedExtremeValueMap m s ξ e =
      if ξ = 0 then m - s * Real.log e else m + s * (e ^ (-ξ) - 1) / ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [generalizedExtremeValueMap_of_shape_ne_zero hξ]
    rw [ite_eq_right hξ, Real.rpow_def_of_pos he]
    have hexp : -ξ * Real.log e = Real.log e * -ξ := mul_comm _ _
    rw [hexp]

/-- The generalized extreme-value transformation is measurable jointly in its four inputs. -/
@[fun_prop]
theorem measurable_generalizedExtremeValueMap :
    Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      generalizedExtremeValueMap p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  simp only [generalizedExtremeValueMap]
  exact Measurable.ite (measurableSet_eq_fun measurable_fst.snd measurable_const) (by fun_prop)
    (by fun_prop)

/-- The generalized extreme-value transformation is measurable in its exponential input. -/
@[fun_prop]
theorem measurable_generalizedExtremeValueMap_right (m s ξ : ℝ) :
    Measurable (generalizedExtremeValueMap m s ξ) :=
  measurable_generalizedExtremeValueMap.comp
    (((measurable_const.prodMk measurable_const).prodMk measurable_const).prodMk measurable_id)

/-- The generalized extreme-value measure in the maximum convention.

For positive scale this is the pushforward of a rate-one exponential law by
`generalizedExtremeValueMap`. For nonpositive scale it is the zero measure. -/
def generalizedExtremeValueMeasure (m s ξ : ℝ) : Measure ℝ :=
  if 0 < s then (expMeasure 1).map (generalizedExtremeValueMap m s ξ) else 0

/-- For positive scale, the generalized extreme-value law is its prescribed exponential
pushforward. -/
theorem generalizedExtremeValueMeasure_of_pos {s : ℝ} (hs : 0 < s) (m ξ : ℝ) :
    generalizedExtremeValueMeasure m s ξ =
      (expMeasure 1).map (generalizedExtremeValueMap m s ξ) := by
  simp [generalizedExtremeValueMeasure, hs]

/-- A nonpositive scale gives the zero generalized extreme-value measure. -/
@[simp]
theorem generalizedExtremeValueMeasure_of_nonpos {s : ℝ} (hs : s ≤ 0) (m ξ : ℝ) :
    generalizedExtremeValueMeasure m s ξ = 0 := by
  simp [generalizedExtremeValueMeasure, not_lt.mpr hs]

/-- The zero-shape generalized extreme-value law is the Gumbel law, at every scale parameter. -/
@[simp]
theorem generalizedExtremeValueMeasure_zero (m s : ℝ) :
    generalizedExtremeValueMeasure m s 0 = gumbelMeasure m s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [generalizedExtremeValueMeasure_of_nonpos hs, gumbelMeasure_of_nonpos hs]
  · rw [generalizedExtremeValueMeasure_of_pos hs, gumbelMeasure_of_pos hs]
    congr 1
    funext e
    exact generalizedExtremeValueMap_zero m s e

/-- For nonzero shape and positive scale, the generalized extreme-value law is the pushforward of
a rate-one exponential law under `e ↦ m + s * (e ^ (-ξ) - 1) / ξ`. -/
theorem generalizedExtremeValueMeasure_of_shape_ne_zero {s ξ : ℝ} (hs : 0 < s) (hξ : ξ ≠ 0)
    (m : ℝ) :
    generalizedExtremeValueMeasure m s ξ =
      (expMeasure 1).map (fun e => m + s * (e ^ (-ξ) - 1) / ξ) := by
  rw [generalizedExtremeValueMeasure_of_pos hs]
  refine Measure.map_congr ?_
  filter_upwards [ae_pos_expMeasure 1] with e he
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ]

/-- A generalized extreme-value law with positive scale is a probability measure. -/
theorem isProbabilityMeasure_generalizedExtremeValueMeasure {s : ℝ} (hs : 0 < s) (m ξ : ℝ) :
    IsProbabilityMeasure (generalizedExtremeValueMeasure m s ξ) := by
  rw [generalizedExtremeValueMeasure_of_pos hs]
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  infer_instance

/-- A variable obtained from a rate-one exponential variable by the generalized extreme-value
transformation has the corresponding generalized extreme-value law. -/
theorem hasLaw_generalizedExtremeValueMeasure_of_hasLaw_expMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℝ}
    {s : ℝ} (hs : 0 < s) (m ξ : ℝ) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => generalizedExtremeValueMap m s ξ (E ω))
      (generalizedExtremeValueMeasure m s ξ) P := by
  rw [generalizedExtremeValueMeasure_of_pos hs]
  exact (hasLaw_map (measurable_generalizedExtremeValueMap_right m s ξ).aemeasurable).comp hE

/-- If `E` has the rate-one exponential law, then its nonzero-shape power transformation has the
corresponding generalized extreme-value law. -/
theorem hasLaw_generalizedExtremeValueMeasure_of_hasLaw_expMeasure_of_shape_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℝ}
    {s ξ : ℝ} (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => m + s * (E ω ^ (-ξ) - 1) / ξ)
      (generalizedExtremeValueMeasure m s ξ) P := by
  rw [generalizedExtremeValueMeasure_of_shape_ne_zero hs hξ]
  exact (hasLaw_map
    (by fun_prop : Measurable fun e : ℝ => m + s * (e ^ (-ξ) - 1) / ξ).aemeasurable).comp hE

/-- A positive affine map changes the location and scale of a generalized extreme-value law and
leaves its shape fixed. The equality also respects the nonpositive-scale zero branch. -/
theorem map_affine_generalizedExtremeValueMeasure {b : ℝ} (hb : 0 < b) (a m s ξ : ℝ) :
    (generalizedExtremeValueMeasure m s ξ).map (fun x => a + b * x) =
      generalizedExtremeValueMeasure (a + b * m) (b * s) ξ := by
  rcases le_or_gt s 0 with hs | hs
  · rw [generalizedExtremeValueMeasure_of_nonpos hs,
      generalizedExtremeValueMeasure_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hb.le hs), Measure.map_zero]
  · rw [generalizedExtremeValueMeasure_of_pos hs,
      generalizedExtremeValueMeasure_of_pos (mul_pos hb hs),
      Measure.map_map (by fun_prop) (measurable_generalizedExtremeValueMap_right m s ξ)]
    congr 1
    funext e
    simp only [Function.comp_apply, generalizedExtremeValueMap]
    split_ifs <;> ring

/-- The random-variable form of positive affine transport for generalized extreme-value laws. -/
theorem hasLaw_affine_generalizedExtremeValueMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m s ξ b : ℝ} (hb : 0 < b) (a : ℝ)
    (hX : HasLaw X (generalizedExtremeValueMeasure m s ξ) P) :
    HasLaw (fun ω => a + b * X ω)
      (generalizedExtremeValueMeasure (a + b * m) (b * s) ξ) P := by
  rw [← map_affine_generalizedExtremeValueMeasure hb]
  exact (hasLaw_map (by fun_prop : Measurable (fun x : ℝ => a + b * x)).aemeasurable).comp hX

/-- The generalized extreme-value family is jointly measurable in location, scale, and shape,
including the nonpositive-scale zero-measure branch. -/
@[fun_prop]
theorem measurable_generalizedExtremeValueMeasure :
    Measurable fun p : (ℝ × ℝ) × ℝ =>
      generalizedExtremeValueMeasure p.1.1 p.1.2 p.2 := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd)
  · exact TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
      (ν := expMeasure 1) (f := fun p : (ℝ × ℝ) × ℝ =>
        generalizedExtremeValueMap p.1.1 p.1.2 p.2)
      measurable_generalizedExtremeValueMap
  · exact measurable_const

end TauCeti.Probability
