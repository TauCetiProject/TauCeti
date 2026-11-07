/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuity of parametric integrals with compactly supported integrand

Mathlib's `continuousOn_integral_of_compact_support` gives continuity of a parametric integral on
a set. This file records its global form: a jointly continuous integrand which vanishes unless the
integration variable lies in a fixed compact set has a continuous parametric integral, against any
measure which is finite on compact sets. It also records that the indicator function of a
bounded interval `[a, b)` is integrable against a locally finite measure, that the integral of
`|f|` over a set splits along the sign of `f`, and that a continuous
square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a measure positive
on nonempty open sets. It also bounds the integral over a measurable set `S` by integrals over
unions with disjoint sets.

## Main statements

* `TauCeti.continuous_integral_of_compact_support`: the parametric integral of a jointly
  continuous integrand which vanishes unless `r ∈ K`, for compact `K`, is continuous.
* `TauCeti.integrable_indicator_Ico_one`: the indicator function of `[a, b)` is integrable.
* `TauCeti.setIntegral_abs_eq_sub`: the integral of `|f|` over `s` is the integral of `f` over the
  part of `s` where `f ≥ 0` minus its integral over the rest of `s`.
* `Continuous.eq_zero_of_integral_conj_mul_self_eq_zero`: a continuous square-integrable function
  `h` with `∫ conj (h x) * h x = 0` vanishes.
* `MeasureTheory.norm_setIntegral_le_add_of_disjoint`: the integral over `S` is bounded by the
  integrals over `H ∪ (S ∪ T)`, `H` and `T`, for disjoint `H`, `S`, `T`.
-/

public section

open MeasureTheory Function Set

namespace TauCeti

/-- The parametric integral `s ↦ ∫ r, F s r` of a jointly continuous integrand which vanishes
unless `r ∈ K`, for compact `K`, is continuous. -/
theorem continuous_integral_of_compact_support {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : X → Y → E} {K : Set Y} (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (hK : IsCompact K) (hFc : Continuous (uncurry F)) (hF : ∀ s r, F s r ≠ 0 → r ∈ K) :
    Continuous fun s => ∫ r, F s r ∂μ :=
  continuousOn_univ.mp <| continuousOn_integral_of_compact_support hK hFc.continuousOn
    fun s r _ hr => by_contra fun h => hr (hF s r h)

/-- The indicator function of a bounded interval `[a, b)` is integrable against a locally finite
measure. -/
theorem integrable_indicator_Ico_one {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [LinearOrder α] [OrderClosedTopology α] [OpensMeasurableSpace α] [CompactIccSpace α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] (a b : α) :
    Integrable ((Ico a b).indicator (1 : α → ℝ)) μ :=
  (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

/-- The integral of `|f|` over a set `s` is the integral of `f` over the part of `s` where `f` is
nonnegative minus the integral of `f` over the part where it is negative. -/
theorem setIntegral_abs_eq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {s : Set α} (hf : IntegrableOn f s μ) :
    ∫ x in s, |f x| ∂μ = ∫ x in s ∩ {x | 0 ≤ f x}, f x ∂μ - ∫ x in s \ {x | 0 ≤ f x}, f x ∂μ := by
  have hneg : {x | f x < 0} ∩ s = s \ {x | 0 ≤ f x} := by
    ext x
    simp [and_comm]
  simp_rw [← Real.norm_eq_abs]
  rw [integral_norm_eq_pos_sub_neg hf, ← setIntegral_neg_eq_setIntegral_nonpos hf.1,
    Measure.restrict_restrict₀ (aestronglyMeasurable_const.nullMeasurableSet_le hf.1),
    Measure.restrict_restrict₀ (hf.1.nullMeasurableSet_lt aestronglyMeasurable_const),
    inter_comm _ s, hneg]

end TauCeti

/-- A continuous square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a
measure positive on nonempty open sets. -/
theorem Continuous.eq_zero_of_integral_conj_mul_self_eq_zero {X 𝕜 : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X}
    [μ.IsOpenPosMeasure] {h : X → 𝕜} (hc : Continuous h) (hL : MemLp h 2 μ)
    (h0 : ∫ x, starRingEnd 𝕜 (h x) * h x ∂μ = 0) : h = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hpos := MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (μ := μ) (f :=
    fun x => ‖h x‖ ^ 2)
    (x := x) (by fun_prop) (hL.integrable_norm_pow two_ne_zero) (fun _ => by positivity)
    (by simpa using hx)
  simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_eq_zero] at h0
  exact hpos.ne' h0

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If `H`, `S` and `T` are disjoint, with `S` and `T` measurable, then the integral of `f` over `S`
is bounded by its integrals over `H ∪ (S ∪ T)`, `H` and `T`. -/
theorem norm_setIntegral_le_add_of_disjoint {f : α → E} {H S T : Set α}
    (hf : IntegrableOn f (H ∪ (S ∪ T)) μ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hHST : Disjoint H (S ∪ T))
    (hST : Disjoint S T) :
    ‖∫ x in S, f x ∂μ‖ ≤
      ‖∫ x in H ∪ (S ∪ T), f x ∂μ‖ + ‖∫ x in H, f x ∂μ‖ + ‖∫ x in T, f x ∂μ‖ := by
  have hfH : IntegrableOn f H μ := hf.mono_set subset_union_left
  have hfS : IntegrableOn f S μ := hf.mono_set (subset_union_left.trans subset_union_right)
  have hfT : IntegrableOn f T μ := hf.mono_set (subset_union_right.trans subset_union_right)
  rw [setIntegral_union hHST (hS.union hT) hfH (hfS.union hfT), setIntegral_union hST hT hfS hfT]
  set a := ∫ x in H, f x ∂μ
  set b := ∫ x in S, f x ∂μ
  set c := ∫ x in T, f x ∂μ
  calc ‖b‖ = ‖a + (b + c) - a - c‖ := by congr 1; abel
    _ ≤ ‖a + (b + c) - a‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a + (b + c)‖ + ‖a‖ + ‖c‖ := by gcongr; exact norm_sub_le _ _

end MeasureTheory
