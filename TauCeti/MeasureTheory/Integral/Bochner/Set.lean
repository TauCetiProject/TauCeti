/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
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
on nonempty open sets.

## Main statements

* `TauCeti.continuous_integral_of_compact_support`: the parametric integral of a jointly
  continuous integrand which vanishes unless `r ∈ K`, for compact `K`, is continuous.
* `TauCeti.integrable_indicator_Ico_one`: the indicator function of `[a, b)` is integrable.
* `TauCeti.setIntegral_abs_eq_sub`: the integral of `|f|` over `s` is the integral of `f` over the
  part of `s` where `f ≥ 0` minus its integral over the rest of `s`.
* `MeasureTheory.setIntegral_mul_le_mul_setIntegral_abs`: the pairing of an integrable `f` on `Ω`
  with a function `g` bounded by `S` on `V ⊆ Ω` is at most `S ∫_Ω |f|`.
* `MeasureTheory.setLIntegral_enorm_sq_eq_ofReal_setIntegral`: the Lebesgue integral of `‖f‖ₑ ^ 2`
  over `A` is `ofReal` of the Bochner integral of `‖f‖ ^ 2`, and
  `MeasureTheory.setLIntegral_enorm_sq_le_ofReal` the corresponding bound.
* `Continuous.eq_zero_of_integral_conj_mul_self_eq_zero`: a continuous square-integrable function
  `h` with `∫ conj (h x) * h x = 0` vanishes.
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

/-- If disjoint parametrizations `Q i` of a domain `D` cover the complement of a finite set `Z`, and
`g` is injective on `s`, the integral over `g '' s` is the sum of the integrals over the images
`(g ∘ Q i) '' (D ∩ Q i ⁻¹' s)` of the pieces cut out by each parametrization, up to the transport
identity `hpiece` for each piece. The integrand need only be integrable on `g '' s`, and the
measure needs null singletons only to discard the seams. -/
theorem mul_integral_image_eq_sum_pieces {E M ι : Type*} [MeasurableSpace E] [Fintype ι]
    {Q : ι → E → M} {D : Set E} {Z : Set M} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D))) {g : M → E} {s : Set M}
    (hg : InjOn g s) (μ : Measure E) [NullSingletonClass μ] {C : E → ℝ}
    (hC : IntegrableOn C (g '' s) μ)
    (c : ℝ) (V : ι → E → ℝ)
    (hT : ∀ i, MeasurableSet ((g ∘ Q i) '' (D ∩ Q i ⁻¹' s)))
    (hpiece : ∀ i, c * ∫ y in (g ∘ Q i) '' (D ∩ Q i ⁻¹' s), C y ∂μ =
      ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ) :
    c * ∫ y in g '' s, C y ∂μ = ∑ i, ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ := by
  have hpair : Pairwise (fun i k ↦ Disjoint ((g ∘ Q i) '' (D ∩ Q i ⁻¹' s))
      ((g ∘ Q k) '' (D ∩ Q k ⁻¹' s))) := fun i k hik ↦ by
    simp only [image_comp, image_inter_preimage]
    exact ((hdisj hik).mono inter_subset_left inter_subset_left).image hg inter_subset_right
      inter_subset_right
  have hcover : (⋃ i, (g ∘ Q i) '' (D ∩ Q i ⁻¹' s)) = g '' (s \ Z) := by
    simp only [image_comp, image_inter_preimage]
    rw [← image_iUnion, ← iUnion_inter, himage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have hsub : ∀ i, (g ∘ Q i) '' (D ∩ Q i ⁻¹' s) ⊆ g '' s := fun i ↦ by
    rw [image_comp, image_inter_preimage]
    exact image_mono inter_subset_right
  rw [setIntegral_congr_set (hZ.image_sdiff_ae_eq g s μ), ← hcover,
    integral_iUnion_fintype hT hpair (fun i ↦ hC.mono_set (hsub i)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hpiece i

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

/-- The pairing of an integrable function `f` on `Ω` with a function `g` bounded by `S` on
`V ⊆ Ω` is at most `S ∫_Ω |f|`. -/
theorem setIntegral_mul_le_mul_setIntegral_abs {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {V Ω : Set α} {f g : α → ℝ} {S : ℝ} (hVΩ : V ⊆ Ω)
    (hf : IntegrableOn f Ω ν) (hS0 : 0 ≤ S) (hg : AEStronglyMeasurable g (ν.restrict V))
    (hgS : ∀ᵐ x ∂ν.restrict V, |g x| ≤ S) :
    ∫ x in V, f x * g x ∂ν ≤ S * ∫ x in Ω, |f x| ∂ν := by
  have hbound : ∀ᵐ x ∂ν.restrict V, ‖f x * g x‖ ≤ S * |f x| := by
    filter_upwards [hgS] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hfV : IntegrableOn f V ν := hf.mono_set hVΩ
  have hΔV : IntegrableOn (fun x => S * |f x|) V ν := hfV.abs.const_mul S
  calc _ ≤ ∫ x in V, S * |f x| ∂ν :=
        integral_mono_ae (hΔV.mono' (hfV.aestronglyMeasurable.mul hg) hbound) hΔV
          (hbound.mono fun x hx => (le_abs_self _).trans hx)
    _ = S * ∫ x in V, |f x| ∂ν := integral_const_mul S _
    _ ≤ S * ∫ x in Ω, |f x| ∂ν :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hf.abs
          (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ hVΩ)) hS0

/-- The Lebesgue integral of `‖f‖ₑ ^ 2` over `A` is the `ENNReal.ofReal` of the Bochner integral of
`‖f‖ ^ 2`, when `‖f‖ ^ 2` is integrable on `A`. -/
theorem setLIntegral_enorm_sq_eq_ofReal_setIntegral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {ν : Measure α} {A : Set α} {f : α → E}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) A ν) :
    ∫⁻ x in A, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x in A, ‖f x‖ ^ 2 ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A bound on the Bochner integral of `‖f‖ ^ 2` over `A` bounds the Lebesgue integral of
`‖f‖ₑ ^ 2`. -/
theorem setLIntegral_enorm_sq_le_ofReal {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {ν : Measure α} {A : Set α} {f : α → E} {c : ℝ}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) A ν) (h : ∫ x in A, ‖f x‖ ^ 2 ∂ν ≤ c) :
    ∫⁻ x in A, ‖f x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal c :=
  (setLIntegral_enorm_sq_eq_ofReal_setIntegral hf).trans_le (ENNReal.ofReal_le_ofReal h)

end MeasureTheory
