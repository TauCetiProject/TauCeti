/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Measure
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Translated renewal measures

The renewal measure `U` of a measure `F` on `ℝ≥0`, regarded as a measure on the real line and
translated by `-t`, is the measure `Uₜ = U.map (s ↦ s - t)`. It sees the renewals near time `t`.
The renewal equation `U = δ₀ + F ∗ U` translates to `Uₜ = δ_{-t} + F ∗ Uₜ`.

## Main definitions

* `MeasureTheory.Measure.translatedRenewalMeasure`: the renewal measure on the real line,
  translated by `-t`.

## Main results

* `MeasureTheory.Measure.translatedRenewalMeasure_eq_dirac_add_conv`: the translated renewal
  equation `Uₜ = δ_{-t} + F ∗ Uₜ`.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory.Measure

/-- The renewal measure on the real line, translated by `-t`. -/
def translatedRenewalMeasure (F : Measure ℝ≥0) (t : ℝ) : Measure ℝ :=
  F.renewalMeasure.map fun s : ℝ≥0 ↦ (s : ℝ) - t

/-- The translated renewal measure is the pushforward of the half-line renewal measure. -/
theorem translatedRenewalMeasure_def (F : Measure ℝ≥0) (t : ℝ) :
    F.translatedRenewalMeasure t =
      F.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t) := (rfl)

/-- Evaluation of a translated renewal measure on a measurable set. -/
theorem translatedRenewalMeasure_apply (F : Measure ℝ≥0) (t : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    F.translatedRenewalMeasure t s = F.renewalMeasure ((fun u : ℝ≥0 ↦ (u : ℝ) - t) ⁻¹' s) := by
  exact Measure.map_apply (by fun_prop) hs

/-- The renewal equation `U = δ₀ + μ ∗ U`, translated by `-t` on the real line: the translated
renewal measure `Uₜ` satisfies `Uₜ = δ_{-t} + μ ∗ Uₜ`. -/
theorem translatedRenewalMeasure_eq_dirac_add_conv (μ : Measure ℝ≥0) [SFinite μ] (t : ℝ) :
    μ.translatedRenewalMeasure t =
      dirac (-t) + μ.map ((↑) : ℝ≥0 → ℝ) ∗ μ.translatedRenewalMeasure t := by
  have hcomp : (fun s : ℝ≥0 ↦ (s : ℝ) - t) = (fun x : ℝ ↦ x + -t) ∘ ((↑) : ℝ≥0 → ℝ) := by
    funext s
    simp [sub_eq_add_neg]
  have hcoe : (μ ∗ μ.renewalMeasure).map ((↑) : ℝ≥0 → ℝ) =
      μ.map ((↑) : ℝ≥0 → ℝ) ∗ μ.renewalMeasure.map ((↑) : ℝ≥0 → ℝ) :=
    map_conv_addMonoidHom NNReal.toRealHom.toAddMonoidHom measurable_coe_nnreal_real
  rw [translatedRenewalMeasure_def, hcomp, ← map_map (by fun_prop) measurable_coe_nnreal_real]
  conv_lhs => rw [renewalMeasure_eq_dirac_add_conv]
  rw [Measure.map_add _ _ measurable_coe_nnreal_real, Measure.map_add _ _ (by fun_prop),
    map_dirac' measurable_coe_nnreal_real, map_dirac' (by fun_prop), hcoe, ← conv_dirac,
    ← conv_dirac, conv_assoc]
  simp

end MeasureTheory.Measure
