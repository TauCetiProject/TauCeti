/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Probability bounds from sections

An upper bound on every section of a measurable product event bounds its probability for
a pair of independent random variables, after accounting for the total mass.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.IndepFun

/-- For independent random variables, a uniform bound on the probabilities of the sections
of a measurable set in the product space bounds the measure of that set by the bound times
the mass of the underlying measure. -/
theorem measure_preimage_prodMk_le_of_forall
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β}
    (hind : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {s : Set (α × β)} (hs : MeasurableSet s) {b : ℝ≥0∞}
    (h : ∀ a, P (Y ⁻¹' (Prod.mk a ⁻¹' s)) ≤ b) :
    P ((fun ω ↦ (X ω, Y ω)) ⁻¹' s) ≤ b * P univ := by
  rw [← Measure.map_apply_of_aemeasurable (hX.prodMk hY) hs,
    hind.map_prod_eq_prod_map_map hX hY, Measure.prod_apply hs]
  have hsection (a : α) : P.map Y (Prod.mk a ⁻¹' s) ≤ b := by
    rw [Measure.map_apply_of_aemeasurable hY (hs.preimage measurable_prodMk_left)]
    exact h a
  exact (lintegral_mono hsection).trans_eq (by
    simp [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ])

end ProbabilityTheory.IndepFun
