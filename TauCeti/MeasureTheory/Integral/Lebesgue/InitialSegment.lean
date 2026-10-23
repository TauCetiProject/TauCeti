/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Weighted integral comparison on initial segments

Let `μ` be a measure on the real line and let `φ ≤ 1` on `(a, ∞)`. If the weighted integral
of `φ` over `(a, ∞)` is at most the weight of `(a, ρ]`, the same comparison holds after
intersecting both domains with any initial segment of `(a, ∞)`.

`TauCeti.setLIntegral_indicator_mul_le_setLIntegral_indicator_inter_Iic`
supplies this comparison without measurability assumptions on the weight, density, or initial
segment. Applied along each ray, it compares a radial density with the indicator of a ball on sets
star-shaped about the origin.

## References

The comparison argument comes from the proof of Bombieri–Gubler, *Heights in Diophantine
Geometry* (2006), Lemma C.3.7. It is adapted from the Apache-2.0 formalization of Vaaler's
theorem in `rwst/Subspace-Theorems` (files `ArithmeticHeights/GaussMeasure.lean` and
`ArithmeticHeights/SliceBound.lean`), by Ralf Stephan.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

/-- Let `R` be an initial segment of `(a, ∞)` and let `φ ≤ 1` there. If the integral of `φ`
against a weight `w` is at most the weight of `(a, ρ]`, then its integral over `R` is at most
the weight of `R ∩ (a, ρ]`. The measure is arbitrary, and no measurability assumptions on
`w`, `φ`, or `R` are needed. -/
theorem setLIntegral_indicator_mul_le_setLIntegral_indicator_inter_Iic
    {μ : Measure ℝ} {a ρ : ℝ} {w φ : ℝ → ℝ≥0∞}
    {R : Set ℝ} (hφ : ∀ r ∈ Ioi a, φ r ≤ 1)
    (hmass : ∫⁻ r in Ioi a, w r * φ r ∂μ ≤ ∫⁻ r in Ioi a, (Iic ρ).indicator w r ∂μ)
    (hR : ∀ ⦃r s⦄, a < s → s ≤ r → r ∈ R → s ∈ R) :
    ∫⁻ r in Ioi a, R.indicator (fun r ↦ w r * φ r) r ∂μ ≤
      ∫⁻ r in Ioi a, (R ∩ Iic ρ).indicator w r ∂μ := by
  by_cases hρR : ∀ r, a < r → r ≤ ρ → r ∈ R
  · -- `R` contains `(a, ρ]`: compare with the total mass of `φ`.
    calc ∫⁻ r in Ioi a, R.indicator (fun r ↦ w r * φ r) r ∂μ
        ≤ ∫⁻ r in Ioi a, w r * φ r ∂μ := lintegral_mono fun r ↦ indicator_le_self _ _ _
      _ ≤ ∫⁻ r in Ioi a, (Iic ρ).indicator w r ∂μ := hmass
      _ = ∫⁻ r in Ioi a, (R ∩ Iic ρ).indicator w r ∂μ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        by_cases hrρ : r ≤ ρ
        · rw [indicator_of_mem (mem_Iic.2 hrρ),
            indicator_of_mem (mem_inter (hρR r hr hrρ) (mem_Iic.2 hrρ))]
        · rw [indicator_of_notMem (mt mem_Iic.1 hrρ),
            indicator_of_notMem fun h ↦ hrρ (mem_Iic.1 (mem_of_mem_inter_right h))]
  · -- `R` misses a point `s ≤ ρ`, so it lies below `s`: use `φ ≤ 1` pointwise.
    simp only [not_forall] at hρR
    obtain ⟨s, hs, hsρ, hsR⟩ := hρR
    refine setLIntegral_mono' measurableSet_Ioi fun r hr ↦ ?_
    by_cases hrR : r ∈ R
    · have hrρ : r ≤ ρ := (not_le.mp fun hsr ↦ hsR (hR hs hsr hrR)).le.trans hsρ
      rw [indicator_of_mem hrR, indicator_of_mem (mem_inter hrR (mem_Iic.2 hrρ))]
      exact mul_le_of_le_one_right' (hφ r hr)
    · rw [indicator_of_notMem hrR]
      exact zero_le

end TauCeti
