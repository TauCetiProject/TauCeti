/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.TypeTags
public import TauCeti.RepresentationTheory.Continuous.LpKoopman.Measurable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Checks: strong continuity of the pullback representation of a measurable action

Checks for `TauCeti.continuous_lpKoopman_apply_of_measurableSMul₂` and
`TauCeti.tendsto_measure_preimage_inv_smul_symmDiff`, on the translations `x ↦ t + x` of `ℝ` with
Lebesgue measure, read as the action of `Multiplicative ℝ`:

* for `1 ≤ p < ∞` the orbit `t ↦ π(t) 1_[0,1]` is continuous in `Lᵖ`, although in `L^∞` it is not
  continuous at `0` (`TauCeti.Examples.LpKoopman.not_continuousAt_lpKoopman_unitIcc_top`);
* `volume ([t, t + 1] ∆ [0, 1]) → 0` as `t → 0`.
-/

public section

open MeasureTheory TauCeti Set Filter Topology
open scoped ENNReal symmDiff

namespace TauCeti.Examples.LpKoopmanMeasurable

/-- The translations of `ℝ`, as the action of `Multiplicative ℝ`, preserve Lebesgue measure. -/
theorem measurePreserving_translate (t : Multiplicative ℝ) :
    MeasurePreserving (t • · : ℝ → ℝ) volume volume :=
  measurePreserving_multiplicative_smul volume t

/-- **Check.** For `1 ≤ p < ∞`, the orbit `t ↦ π(t) 1_[0,1]` of the translations of `ℝ` is
continuous in `Lᵖ`. -/
theorem continuous_lpKoopman_indicator_Icc (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Continuous fun t : ℝ ↦ lpKoopman ℂ ℂ p volume measurePreserving_translate
      (Multiplicative.ofAdd t)
      (indicatorConstLp p (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) (by simp) (1 : ℂ)) :=
  (continuous_lpKoopman_apply_of_measurableSMul₂ measurePreserving_translate hp _).comp
    continuous_ofAdd

/-- **Check.** The measure of `[t, t + 1] ∆ [0, 1]` tends to `0` as `t → 0`. -/
theorem tendsto_volume_Icc_symmDiff :
    Tendsto (fun t : ℝ ↦ volume (Icc t (t + 1) ∆ Icc 0 1)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_measure_preimage_inv_smul_symmDiff measurePreserving_translate
    (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) (by simp) 1).comp
    (continuous_ofAdd.tendsto (0 : ℝ))
  refine h.congr fun t ↦ congrArg volume ?_
  ext x
  simp only [inv_one, one_smul, preimage_id', mem_symmDiff, mem_preimage, mem_Icc]
  rw [← ofAdd_neg, ofAdd_smul, vadd_eq_add]
  constructor <;> rintro (⟨⟨h₁, h₂⟩, h₃⟩ | ⟨⟨h₁, h₂⟩, h₃⟩) <;>
    [left; right; left; right] <;> refine ⟨⟨by linarith, by linarith⟩, fun h ↦ h₃ ⟨?_, ?_⟩⟩ <;>
    linarith [h.1, h.2]

end TauCeti.Examples.LpKoopmanMeasurable
