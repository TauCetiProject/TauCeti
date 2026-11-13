/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tonelli's theorem on the region between two functions

For `f g : α → ℝ` and `s : Set α`, Mathlib's `regionBetween f g s` is the set of pairs `(x, y)`
with `x ∈ s` and `f x < y < g x`, and `volume_regionBetween_eq_lintegral` computes its product
measure. This file integrates functions over it. For s-finite measures `μ` on `α` and `ν` on `ℝ`,
and a function `F : α × ℝ → ℝ≥0∞` that is almost everywhere measurable on the region, the lower
Lebesgue integral of `F` over the region is

* the integral over `x ∈ s` of the integrals of `F (x, ·)` over the vertical intervals
  `Ioo (f x) (g x)` (`MeasureTheory.setLIntegral_regionBetween`), and
* the integral over heights `y` of the integrals of `F (·, y)` over the horizontal slices
  `{x | x ∈ s ∧ y ∈ Ioo (f x) (g x)}` (`MeasureTheory.setLIntegral_regionBetween_symm`).

Only the region itself and, for the first formula, `s` need to be measurable: neither `f` nor
`g` is assumed measurable, and `F` is only constrained on the region.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ν : Measure ℝ} [SFinite ν]
  {f g : α → ℝ} {s : Set α} {F : α × ℝ → ℝ≥0∞}

/-- **Tonelli's theorem on the region between two functions**, integrating first along the
vertical intervals `Ioo (f x) (g x)`. -/
theorem setLIntegral_regionBetween (hs : MeasurableSet s)
    (hR : MeasurableSet (regionBetween f g s))
    (hF : AEMeasurable F ((μ.prod ν).restrict (regionBetween f g s))) :
    ∫⁻ z in regionBetween f g s, F z ∂μ.prod ν =
      ∫⁻ x in s, ∫⁻ y in Ioo (f x) (g x), F (x, y) ∂ν ∂μ := by
  rw [← lintegral_indicator hR, lintegral_prod _ ((aemeasurable_indicator_iff hR).2 hF),
    ← lintegral_indicator hs]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun y ↦ ?_
    simp only [indicator, regionBetween, mem_ofPred_eq, hx, true_and]
  · rw [indicator_of_notMem hx]
    simp [indicator, regionBetween, hx]

/-- **Tonelli's theorem on the region between two functions**, integrating first along the
horizontal slices `{x | x ∈ s ∧ y ∈ Ioo (f x) (g x)}`. -/
theorem setLIntegral_regionBetween_symm [SFinite μ] (hR : MeasurableSet (regionBetween f g s))
    (hF : AEMeasurable F ((μ.prod ν).restrict (regionBetween f g s))) :
    ∫⁻ z in regionBetween f g s, F z ∂μ.prod ν =
      ∫⁻ y, ∫⁻ x in {x | x ∈ s ∧ y ∈ Ioo (f x) (g x)}, F (x, y) ∂μ ∂ν := by
  rw [← lintegral_indicator hR, lintegral_prod_symm _ ((aemeasurable_indicator_iff hR).2 hF)]
  refine lintegral_congr fun y ↦ ?_
  have hslice : MeasurableSet {x | x ∈ s ∧ y ∈ Ioo (f x) (g x)} := measurable_prodMk_right hR
  rw [← lintegral_indicator hslice]
  rfl

end MeasureTheory
