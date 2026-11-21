/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# First-order upper supports and Lipschitz estimates

Bounds on the differentials of touching upper supports give growth, integral
comparison and Lipschitz estimates without differentiability of the supported function.
This is the comparison step in Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*,
Proposition 7.5.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology NNReal

namespace TauCeti

/-- A touching upper support with derivative `d` gives right slopes below any `r > d`
arbitrarily close to `x` on the right. -/
theorem frequently_slope_lt_of_upper_support {f g : ℝ → ℝ} {x d r : ℝ}
    (hg : HasDerivWithinAt g d (Ici x) x) (heq : g x = f x)
    (hle : ∀ᶠ y in 𝓝[>] x, f y ≤ g y) (hdr : d < r) :
    ∃ᶠ y in 𝓝[>] x, slope f x y < r := by
  have hs := hg.liminf_right_slope_le hdr
  apply hs.mp
  filter_upwards [hle, self_mem_nhdsWithin] with y hy hxy hys
  apply lt_of_le_of_lt _ hys
  rw [slope_def_field, slope_def_field, heq]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hy _) (sub_pos.mpr hxy).le

/-- A differentiable comparison function bounds a function with touching upper supports. -/
theorem image_le_of_upper_supports {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (ha : f a ≤ B a)
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivWithinAt g d (Ici x) x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝[>] x, f y ≤ g y) ∧ d ≤ B' x) :
    ∀ x ∈ Icc a b, f x ≤ B x := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB
    hB'
  intro x hx r hr
  obtain ⟨g, d, hd, heq, hdom, hbound⟩ := hsupport x hx
  exact frequently_slope_lt_of_upper_support hd heq hdom (hbound.trans_lt hr)

/-- First-order upper supports with derivative at most `C` bound endpoint growth. -/
theorem sub_le_mul_of_upper_supports {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivWithinAt g d (Ici x) x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝[>] x, f y ≤ g y) ∧ d ≤ C) :
    f b - f a ≤ C * (b - a) := by
  have hcomparison := image_le_of_upper_supports hf
    (B := fun x ↦ f a + C * (x - a)) (B' := fun _ ↦ C) (by fun_prop)
    (fun x _ ↦ by
      simpa only [mul_one, id_eq] using
        ((((hasDerivAt_id x).sub_const a).const_mul C).const_add (f a)).hasDerivWithinAt)
    (by simp) hsupport
  exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hcomparison b ⟨hab, le_rfl⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded upper support at every point gives a one-sided segment estimate. -/
theorem sub_le_mul_norm_sub_of_upper_supports {S : Set E} (hS : Convex ℝ S)
    {f : E → ℝ} (hf : ContinuousOn f S) {C : ℝ}
    (hsupport : ∀ z ∈ S, ∃ g : E → ℝ, ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt g L z ∧ g z = f z ∧
        (∀ᶠ w in 𝓝[S] z, f w ≤ g w) ∧ ‖L‖ ≤ C)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y - f x ≤ C * ‖y - x‖ := by
  let c : ℝ → E := AffineMap.lineMap x y
  have hc : Continuous c := AffineMap.lineMap_continuous
  have hcS : MapsTo c (Icc 0 1) S := fun _ ht ↦ hS.lineMap_mem hx hy ht
  have hseg := sub_le_mul_of_upper_supports (f := f ∘ c) (C := C * ‖y - x‖)
    zero_le_one (hf.comp hc.continuousOn hcS) (fun t ht ↦ ?_)
  · simpa only [Function.comp_apply, c, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, sub_zero, mul_one] using hseg
  obtain ⟨g, L, hL, heq, hdom, hbound⟩ := hsupport (c t) (hcS (Ico_subset_Icc_self ht))
  refine ⟨g ∘ c, L (y - x),
    (hL.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap).hasDerivWithinAt, heq, ?_, ?_⟩
  · have hct : Tendsto c (𝓝[>] t) (𝓝[S] (c t)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds ht.2)] with u htu hu
      exact hcS ⟨ht.1.trans htu.le, hu.le⟩
    exact hct hdom
  · exact (le_abs_self _).trans ((L.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))

/-- Uniformly bounded upper support differentials imply Lipschitz continuity. -/
theorem lipschitzOnWith_of_upper_supports {S : Set E} (hS : Convex ℝ S)
    {f : E → ℝ} (hf : ContinuousOn f S) {C : ℝ≥0}
    (hsupport : ∀ z ∈ S, ∃ g : E → ℝ, ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt g L z ∧ g z = f z ∧
        (∀ᶠ w in 𝓝[S] z, f w ≤ g w) ∧ ‖L‖ ≤ C) :
    LipschitzOnWith C f S := by
  apply LipschitzOnWith.of_le_add_mul C
  intro x hx y hy
  have h := sub_le_mul_norm_sub_of_upper_supports hS hf hsupport hy hx
  rw [dist_eq_norm]
  linarith

end TauCeti

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti

/-- Continuous contact-derivative bounds can be integrated over an ordered interval. -/
theorem sub_le_integral_of_upper_supports {f h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivWithinAt g d (Ici x) x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝[>] x, f y ≤ g y) ∧ d ≤ h x) :
    f b - f a ≤ ∫ x in a..b, h x := by
  let B : ℝ → ℝ := fun t ↦ f a + ∫ x in a..t, h x
  have hint : IntervalIntegrable h volume a b := hh.intervalIntegrable_of_Icc hab
  have hBcont : ContinuousOn B (Icc a b) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
  have hB : ∀ t ∈ Ico a b, HasDerivWithinAt B (h t) (Ici t) t := by
    intro t ht
    have hnhds : Icc a b ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht
    have hright : ContinuousWithinAt h (Ioi t) t :=
      ((hh t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin hnhds).mono Ioi_subset_Ici_self
    have hmeas : StronglyMeasurableAtFilter h (𝓝[>] t) volume :=
      ⟨Icc a b, nhdsWithin_mono _ Ioi_subset_Ici_self hnhds,
        hh.aestronglyMeasurable measurableSet_Icc⟩
    have hintt : IntervalIntegrable h volume a t :=
      (hh.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1
    exact (intervalIntegral.integral_hasDerivWithinAt_right hintt hmeas hright).const_add _
  have hBa : f a ≤ B a := by simp [B]
  have hcomp := image_le_of_upper_supports hf
    hBcont hB hBa hsupport
      b ⟨hab, le_rfl⟩
  exact sub_le_iff_le_add.mpr (by simpa only [B, add_comm] using hcomp)

end TauCeti
