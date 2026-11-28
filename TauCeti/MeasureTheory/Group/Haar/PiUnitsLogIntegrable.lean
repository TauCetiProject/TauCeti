/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units

/-!
# Integrability of log-norm functions on `(ι → ℂ)ˣ` under Haar measure

For a finite index type `ι`, pushing forward a left-invariant Haar measure `μ` on the unit group
`(ι → ℂ)ˣ` along the coordinatewise log-norm map `L : a ↦ (x ↦ Real.log ‖a.val x‖)` produces an
additively left-invariant measure on `ι → ℝ` that is finite on compact sets, hence a nonnegative
scalar multiple of Lebesgue measure. Consequently, any Lebesgue-integrable function on `ι → ℝ`
pulls back along `L` to a `μ`-integrable function on `(ι → ℂ)ˣ`, and in particular
`a ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹` is `μ`-integrable.

## Main statements

* `TauCeti.isAddLeftInvariant_map_logNorm`: the pushforward of a left-invariant measure on
  `(ι → ℂ)ˣ` under `a ↦ (x ↦ Real.log ‖a.val x‖)` is additively left-invariant on `ι → ℝ`.
* `TauCeti.integrable_comp_logNorm`: pullback of Lebesgue-integrable functions on `ι → ℝ` to
  `(ι → ℂ)ˣ` under any Haar measure `μ`.
* `TauCeti.integrable_prod_inv_one_add_log_sq`: Haar-integrability of
  `a ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹` on `(ι → ℂ)ˣ`.

## Provenance

Adapted from `New.integrable_prod_inv_one_add_log_sq` in
`grh/src/Lib/SiegelWeil/Tower/PrincipalIdeles.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
generalized to an arbitrary Haar measure `μ` and arbitrary Lebesgue-integrable functions on
`ι → ℝ`.
-/

@[expose] public section

open Complex MeasureTheory Real

namespace TauCeti

variable {ι : Type*} [MeasurableSpace (ι → ℂ)ˣ] [BorelSpace (ι → ℂ)ˣ]

/-- Pushing forward a multiplicatively left-invariant measure `μ` on `(ι → ℂ)ˣ` along the
coordinatewise log-norm map `a ↦ (x ↦ Real.log ‖a.val x‖)` yields an additively left-invariant
measure on `ι → ℝ`. -/
theorem isAddLeftInvariant_map_logNorm (μ : Measure (ι → ℂ)ˣ) [μ.IsMulLeftInvariant] :
    (μ.map fun a : (ι → ℂ)ˣ ↦ fun x : ι ↦ Real.log ‖a.val x‖).IsAddLeftInvariant := by
  let L (a : (ι → ℂ)ˣ) (x : ι) : ℝ := Real.log ‖a.val x‖
  have hL : Measurable L := measurable_pi_iff.2 fun x ↦
    .log (.norm ((continuous_apply x).comp Units.continuous_val).measurable)
  refine ⟨fun t ↦ ?_⟩
  let scale : (ι → ℂ)ˣ :=
    (by simp [Pi.isUnit_iff] : IsUnit fun x : ι ↦ (Real.exp (t x) : ℂ)).unit
  exact ((hL.measurePreserving μ).of_semiconj (measurePreserving_mul_left μ scale)
    (by
      intro a
      ext x
      have hne : a.val x ≠ 0 := (a.isUnit.apply x).ne_zero
      simp [L, scale, Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.2 hne)])
    (by fun_prop)).map_eq

/-- If `f : (ι → ℝ) → E` is integrable with respect to Lebesgue measure, then
`a ↦ f (fun x ↦ Real.log ‖a.val x‖)` is integrable on `(ι → ℂ)ˣ` with respect to any Haar
measure `μ`. -/
theorem integrable_comp_logNorm [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (ι → ℂ)ˣ) [μ.IsHaarMeasure] {f : (ι → ℝ) → E} (hf : Integrable f volume) :
    Integrable (fun a : (ι → ℂ)ˣ ↦ f (fun x : ι ↦ Real.log ‖a.val x‖)) μ := by
  let L (a : (ι → ℂ)ˣ) (x : ι) : ℝ := Real.log ‖a.val x‖
  let polar (p : (ι → ℝ) × (ι → Circle)) : (ι → ℂ)ˣ :=
    (by simp [Pi.isUnit_iff] :
      IsUnit fun x : ι ↦ (Real.exp (p.fst x) : ℂ) * (p.snd x : ℂ)).unit
  have hL : Measurable L := measurable_pi_iff.2 fun x ↦
    .log (.norm ((continuous_apply x).comp Units.continuous_val).measurable)
  have h_polar : Continuous polar := by
    rw [Units.isOpenEmbedding_val.isInducing.continuous_iff]
    simp only [polar, Function.comp_def, IsUnit.unit_spec]
    fun_prop
  have : (μ.map L).IsAddLeftInvariant := isAddLeftInvariant_map_logNorm μ
  have : IsFiniteMeasureOnCompacts (μ.map L) := ⟨fun K hK ↦ by
    rw [Measure.map_apply hL hK.measurableSet]
    refine (measure_mono fun a ha ↦ ?_).trans_lt
      ((hK.prod isCompact_univ).image h_polar).measure_lt_top
    refine ⟨(L a, fun x ↦ Circle.exp (Complex.arg (a.val x))), ⟨ha, trivial⟩, ?_⟩
    ext x
    have hne : a.val x ≠ 0 := (a.isUnit.apply x).ne_zero
    simp only [polar, L, IsUnit.unit_spec, Circle.coe_exp, Real.exp_log (norm_pos_iff.2 hne),
      Complex.norm_mul_exp_arg_mul_I]⟩
  refine (?_ : Integrable f (μ.map L)).comp_measurable hL
  rw [(μ.map L).isAddLeftInvariant_eq_smul volume]
  exact hf.smul_measure_nnreal

/-- For a finite index type `ι`, the function `a ↦ ∏ x : ι, (1 + (Real.log ‖a.val x‖) ^ 2)⁻¹` on
`(ι → ℂ)ˣ` is integrable with respect to any Haar measure `μ`. -/
theorem integrable_prod_inv_one_add_log_sq [Fintype ι] (μ : Measure (ι → ℂ)ˣ) [μ.IsHaarMeasure] :
    Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹) μ :=
  integrable_comp_logNorm μ (Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq)

end TauCeti
