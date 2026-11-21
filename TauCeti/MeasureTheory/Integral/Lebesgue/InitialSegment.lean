/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.UpperLower.Relative

/-!
# Integral comparison on initial segments

Let `μ` be a measure on a linear order, `S` a null-measurable set and `f ≤ w` almost everywhere on
`S`. Let `R` and `T` be initial segments of `S`, relative to `S`: `R ∩ S` and `T ∩ S` are lower
sets relative to `S` (`IsRelLowerSet`). If the integral of `f` over `S` is at most the integral
over `S` of `T.indicator w`, then the integral over `S` of `R.indicator f` is at most the integral
over `S` of `(R ∩ T).indicator w`.

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

/-- Let `R` and `T` be initial segments of a null-measurable set `S` in a linear order, relative
to `S`: `R ∩ S` and `T ∩ S` are lower sets relative to `S`, so whenever `y ≤ x` are points of `S`
and `x` lies in the segment, so does `y`. Let `f ≤ w` almost everywhere on `S`. If the integral
of `f` over `S` is at most the integral over `S` of `T.indicator w`, then the integral over `S` of
`R.indicator f` is at most the integral over `S` of `(R ∩ T).indicator w`. The measure is
arbitrary, and no measurability assumptions on `f`, `w`, `R` or `T` are needed. -/
theorem setLIntegral_indicator_le_setLIntegral_indicator_inter
    {α : Type*} [LinearOrder α] [MeasurableSpace α] {μ : Measure α} {S R T : Set α}
    {f w : α → ℝ≥0∞} (hS : NullMeasurableSet S μ) (hf : ∀ᵐ x ∂μ.restrict S, f x ≤ w x)
    (hmass : ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, T.indicator w x ∂μ)
    (hR : IsRelLowerSet (R ∩ S) (· ∈ S)) (hT : IsRelLowerSet (T ∩ S) (· ∈ S)) :
    ∫⁻ x in S, R.indicator f x ∂μ ≤ ∫⁻ x in S, (R ∩ T).indicator w x ∂μ := by
  -- Seen inside `S`, the segments `R` and `T` are lower sets, so one contains the other.
  have hlower {U : Set α} (hU : IsRelLowerSet (U ∩ S) (· ∈ S)) :
      IsLowerSet ((↑) ⁻¹' U : Set S) :=
    isLowerSet_subtype_iff_isRelLowerSet.mpr <| by
      simpa only [Subtype.image_preimage_val, inter_comm] using hU
  rcases (hlower hT).total (hlower hR) with hTR | hRT
  · -- `R` contains the part of `S` in `T`: compare with the total mass of `f`.
    calc ∫⁻ x in S, R.indicator f x ∂μ
        ≤ ∫⁻ x in S, f x ∂μ := lintegral_mono fun x ↦ indicator_le_self _ _ _
      _ ≤ ∫⁻ x in S, T.indicator w x ∂μ := hmass
      _ = ∫⁻ x in S, (R ∩ T).indicator w x ∂μ := setLIntegral_congr_fun₀ hS fun x hx ↦
        indicator_eq_indicator ⟨fun hxT ↦ ⟨hTR (a := ⟨x, hx⟩) hxT, hxT⟩, And.right⟩ rfl
  · -- The part of `S` in `R` lies in `T`: use `f ≤ w` almost everywhere on `S`.
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem₀ hS, hf] with x hx hfx
    rw [← indicator_indicator]
    exact indicator_le_indicator' fun hxR ↦ by
      rwa [indicator_of_mem (show x ∈ T from hRT (a := ⟨x, hx⟩) hxR)]

end TauCeti
