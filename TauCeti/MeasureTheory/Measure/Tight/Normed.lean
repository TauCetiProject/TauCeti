/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Tightness from bounded moments

Uniformly bounded positive-order norm moments imply tightness on a proper seminormed group.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- Measures on a proper seminormed group with uniformly bounded positive-order norm moments
are tight. -/
theorem isTightMeasureSet_of_integral_norm_rpow_le {E : Type*} [MeasurableSpace E]
    [SeminormedAddCommGroup E] [ProperSpace E] {S : Set (Measure E)} {p B : ℝ} (hp : 0 < p)
    (hS : ∀ ρ ∈ S, Integrable (fun x : E => ‖x‖ ^ p) ρ ∧
      ∫ x, ‖x‖ ^ p ∂ρ ≤ B) : IsTightMeasureSet S := by
  have htail : Tendsto (fun R : ℝ => ⨆ ρ ∈ S, ρ {x | R < ‖x‖}) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => B / R ^ p) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp)
    have hlim' : Tendsto (fun R : ℝ => ENNReal.ofReal (B / R ^ p)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    refine iSup_le fun ρ => iSup_le fun hρ => ?_
    obtain ⟨hint, hB⟩ := hS ρ hρ
    have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR _
    calc
      ρ {x | R < ‖x‖} ≤ ρ {x | ENNReal.ofReal (R ^ p) ≤ ENNReal.ofReal (‖x‖ ^ p)} :=
        measure_mono fun x hx => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hR.le hx.le hp.le)
      _ ≤ (∫⁻ x, ENNReal.ofReal (‖x‖ ^ p) ∂ρ) / ENNReal.ofReal (R ^ p) :=
        meas_ge_le_lintegral_div hint.aemeasurable.ennreal_ofReal
          (ENNReal.ofReal_pos.2 hRp).ne' ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((∫ x, ‖x‖ ^ p ∂ρ) / R ^ p) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg x) _), ENNReal.ofReal_div_of_pos hRp]
      _ ≤ ENNReal.ofReal (B / R ^ p) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hB hRp.le)
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := (0 : E)) ?_
  convert! htail using 6 with R
  ext x
  simp

/-- Measures on a proper seminormed group with uniformly bounded second norm moment are tight. -/
theorem isTightMeasureSet_of_integral_norm_sq_le {E : Type*} [MeasurableSpace E]
    [SeminormedAddCommGroup E] [ProperSpace E] {S : Set (Measure E)} {B : ℝ}
    (hS : ∀ ρ ∈ S, Integrable (fun x : E => ‖x‖ ^ 2) ρ ∧
      ∫ x, ‖x‖ ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  apply isTightMeasureSet_of_integral_norm_rpow_le (p := ((2 : ℕ) : ℝ)) (B := B) (by norm_num)
  simpa only [Real.rpow_natCast] using hS

/-- A set of measures on `ℝ` with uniformly bounded second moment is tight. -/
theorem isTightMeasureSet_of_integral_sq_le {S : Set (Measure ℝ)} {B : ℝ}
    (hS : ∀ ρ ∈ S, Integrable (fun x : ℝ => x ^ 2) ρ ∧
      ∫ x, x ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  refine isTightMeasureSet_of_integral_norm_sq_le (B := B) ?_
  intro ρ hρ
  simpa only [Real.norm_eq_abs, sq_abs] using hS ρ hρ

end TauCeti

end
