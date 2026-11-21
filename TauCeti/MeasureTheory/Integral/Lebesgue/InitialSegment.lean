/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Integral comparison on initial segments

Let `μ` be a measure on a linear order, `S` a measurable set and `f ≤ w` on `S`. Let `R` and
`T` be initial segments of `S`, relative to `S`. If the integral of `f` over `S` is at most the
integral over `S` of `T.indicator w`, then the integral over `S` of `R.indicator f` is at most the
integral over `S` of `(R ∩ T).indicator w`.

`TauCeti.setLIntegral_indicator_le_setLIntegral_indicator_inter` supplies this comparison
without measurability assumptions on `f`, `w`, `R` or `T`. Applied along each ray, with `S` the
positive radii and `T` the radii inside a ball, it compares a radial density with the indicator
of the ball on sets star-shaped about the origin.

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

/-- Let `R` and `T` be initial segments of a measurable set `S` in a linear order, relative to
`S`: whenever `y ≤ x` are points of `S` and `x` lies in the segment, so does `y`. Let `f ≤ w` on
`S`. If the integral of `f` over `S` is at most the integral over `S` of `T.indicator w`, then
the integral over `S` of `R.indicator f` is at most the integral over `S` of
`(R ∩ T).indicator w`. The measure is arbitrary, and no measurability assumptions on `f`, `w`,
`R` or `T` are needed. -/
theorem setLIntegral_indicator_le_setLIntegral_indicator_inter
    {α : Type*} [LinearOrder α] [MeasurableSpace α] {μ : Measure α} {S R T : Set α}
    {f w : α → ℝ≥0∞} (hS : MeasurableSet S) (hf : ∀ x ∈ S, f x ≤ w x)
    (hmass : ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, T.indicator w x ∂μ)
    (hR : ∀ ⦃x y⦄, x ∈ S → y ∈ S → y ≤ x → x ∈ R → y ∈ R)
    (hT : ∀ ⦃x y⦄, x ∈ S → y ∈ S → y ≤ x → x ∈ T → y ∈ T) :
    ∫⁻ x in S, R.indicator f x ∂μ ≤ ∫⁻ x in S, (R ∩ T).indicator w x ∂μ := by
  by_cases hTR : ∀ x ∈ S, x ∈ T → x ∈ R
  · -- `R` contains the part of `S` in `T`: compare with the total mass of `f`.
    calc ∫⁻ x in S, R.indicator f x ∂μ
        ≤ ∫⁻ x in S, f x ∂μ := lintegral_mono fun x ↦ indicator_le_self _ _ _
      _ ≤ ∫⁻ x in S, T.indicator w x ∂μ := hmass
      _ = ∫⁻ x in S, (R ∩ T).indicator w x ∂μ := by
        refine setLIntegral_congr_fun hS fun x hx ↦ ?_
        by_cases hxT : x ∈ T
        · rw [indicator_of_mem hxT, indicator_of_mem (mem_inter (hTR x hx hxT) hxT)]
        · rw [indicator_of_notMem hxT, indicator_of_notMem fun h ↦ hxT (mem_of_mem_inter_right h)]
  · -- `R` misses a point `y ∈ S ∩ T`, so its part in `S` lies below `y`, hence in `T`:
    -- use `f ≤ w` pointwise.
    simp only [not_forall] at hTR
    obtain ⟨y, hy, hyT, hyR⟩ := hTR
    refine setLIntegral_mono' hS fun x hx ↦ ?_
    by_cases hxR : x ∈ R
    · have hxT : x ∈ T := hT hy hx (not_le.mp fun hyx ↦ hyR (hR hx hy hyx hxR)).le hyT
      rw [indicator_of_mem hxR, indicator_of_mem (mem_inter hxR hxT)]
      exact hf x hx
    · rw [indicator_of_notMem hxR]
      exact zero_le

end TauCeti
