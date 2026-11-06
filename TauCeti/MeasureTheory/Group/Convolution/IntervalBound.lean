/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measures on the real line with uniformly bounded interval masses

A measure `ν` on `ℝ` whose translates of a fixed interval `[a, b]` all have mass at most `B`
integrates every translate of a function dominated by `C` times the indicator of `[a, b]` to at
most `C * B`. Consequently, convolving such a measure with a finite measure gives a locally
finite measure, even when neither factor is compactly supported.

## Main results

* `MeasureTheory.lintegral_comp_add_le_of_le_indicator`: the integral of a translate of a
  function dominated by `C` times the indicator of `[a, b]` is at most `C * B`.
* `MeasureTheory.Measure.isLocallyFiniteMeasure_conv_of_measure_Icc_le`: the convolution of a
  finite measure with a measure of uniformly bounded interval masses is locally finite.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A function dominated by `C` times the indicator of `[a, b]` has translates whose integrals are
at most `C * B`, when `B` bounds the masses of all translates of `[a, b]`. -/
theorem lintegral_comp_add_le_of_le_indicator {ν : Measure ℝ} {g : ℝ → ℝ≥0∞} {a b : ℝ}
    {C B : ℝ≥0∞} (hg : ∀ y, g y ≤ (Icc a b).indicator (fun _ ↦ C) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (x : ℝ) :
    ∫⁻ z, g (x + z) ∂ν ≤ C * B := by
  calc ∫⁻ z, g (x + z) ∂ν ≤ ∫⁻ z, (Icc (-x + a) (-x + b)).indicator (fun _ ↦ C) z ∂ν := by
        refine lintegral_mono fun z ↦ (hg _).trans_eq ?_
        by_cases hz : z ∈ Icc (-x + a) (-x + b)
        · rw [indicator_of_mem hz, indicator_of_mem (show x + z ∈ Icc a b from
            ⟨by linarith [hz.1], by linarith [hz.2]⟩)]
        · rw [indicator_of_notMem hz, indicator_of_notMem (show x + z ∉ Icc a b from fun h ↦
            hz ⟨by linarith [h.1], by linarith [h.2]⟩)]
    _ = C * ν (Icc (-x + a) (-x + b)) := lintegral_indicator_const measurableSet_Icc C
    _ ≤ C * B := by gcongr; exact hν _

namespace Measure

/-- Convolving a finite measure with a measure whose intervals of a fixed positive length have
uniformly bounded mass gives a locally finite measure. -/
theorem isLocallyFiniteMeasure_conv_of_measure_Icc_le {ρ η : Measure ℝ} [IsFiniteMeasure ρ]
    [SFinite η] {r : ℝ} (hr : 0 < r) {B : ℝ≥0∞} (hη : ∀ c, η (Icc c (c + r)) ≤ B)
    (hB : B ≠ ∞) : IsLocallyFiniteMeasure (ρ ∗ η) := by
  refine ⟨fun x ↦ ⟨Icc (x - r / 2) (x + r / 2), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  rw [← lintegral_indicator_one measurableSet_Icc,
    lintegral_conv (measurable_one.indicator measurableSet_Icc)]
  have hη' (c : ℝ) : η (Icc (c + (x - r / 2)) (c + (x + r / 2))) ≤ B := by
    have := hη (c + (x - r / 2))
    rwa [show c + (x - r / 2) + r = c + (x + r / 2) by ring] at this
  calc ∫⁻ y, ∫⁻ z, (Icc (x - r / 2) (x + r / 2)).indicator 1 (y + z) ∂η ∂ρ
      ≤ ∫⁻ y, 1 * B ∂ρ :=
        lintegral_mono fun y ↦ lintegral_comp_add_le_of_le_indicator (fun _ ↦ le_rfl) hη' y
    _ < ∞ := by
        rw [lintegral_const, one_mul]
        exact ENNReal.mul_lt_top hB.lt_top (measure_lt_top ρ _)

end Measure

end MeasureTheory
