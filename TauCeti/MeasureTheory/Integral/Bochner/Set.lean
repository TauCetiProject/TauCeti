/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.UrysohnsLemma

/-!
# Continuity of parametric integrals with compactly supported integrand

Mathlib's `continuousOn_integral_of_compact_support` gives continuity of a parametric integral on
a set. This file records its global form: a jointly continuous integrand which vanishes unless the
integration variable lies in a fixed compact set has a continuous parametric integral, against any
measure which is finite on compact sets. It also records that the indicator function of a
bounded interval `[a, b)` is integrable against a locally finite measure, and that a continuous
square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a measure positive
on nonempty open sets. Continuous scalar functions are also determined by their integrals
against continuous compactly supported scalar tests.

## Main statements

* `TauCeti.continuous_integral_of_compact_support`: the parametric integral of a jointly
  continuous integrand which vanishes unless `r ∈ K`, for compact `K`, is continuous.
* `TauCeti.integrable_indicator_Ico_one`: the indicator function of `[a, b)` is integrable.
* `Continuous.eq_zero_of_integral_conj_mul_self_eq_zero`: a continuous square-integrable function
  `h` with `∫ conj (h x) * h x = 0` vanishes.
* `Continuous.eq_zero_of_forall_integral_mul_eq_zero`: a continuous scalar function whose
  integrals against all continuous compactly supported scalar tests vanish is zero.
-/

public section

open MeasureTheory Function Set
open scoped CompactlySupported

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

end TauCeti

/-- A continuous square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a
measure positive on nonempty open sets. -/
theorem Continuous.eq_zero_of_integral_conj_mul_self_eq_zero {X 𝕜 : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X}
    [μ.IsOpenPosMeasure] {h : X → 𝕜} (hc : Continuous h) (hL : MemLp h 2 μ)
    (h0 : ∫ x, starRingEnd 𝕜 (h x) * h x ∂μ = 0) : h = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := μ) (f := fun x => ‖h x‖ ^ 2)
    (x := x) (by fun_prop) (hL.integrable_norm_pow two_ne_zero) (fun _ => by positivity)
    (by simpa using hx)
  simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_eq_zero] at h0
  exact hpos.ne' h0

/-- A continuous scalar function vanishes if its integral against every continuous compactly
supported scalar test function vanishes. No global integrability or σ-finiteness is needed. -/
theorem Continuous.eq_zero_of_forall_integral_mul_eq_zero {X 𝕜 : Type*} [TopologicalSpace X]
    [R1Space X] [LocallyCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [RCLike 𝕜] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {h : X → 𝕜} (hc : Continuous h)
    (h0 : ∀ φ : C_c(X, 𝕜), ∫ x, φ x * h x ∂μ = 0) : h = 0 := by
  funext x
  obtain ⟨ψ, hψ1, hψs, -, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := x)) isOpen_univ (Set.subset_univ _)
  have hψc : HasCompactSupport (ψ : X → ℝ) := hψs
  let k : X → 𝕜 := fun y => (ψ y : 𝕜) * h y
  have hkc : Continuous k := by fun_prop
  have hks : HasCompactSupport k :=
    (hψc.comp_left (g := fun r : ℝ => (r : 𝕜)) (by simp)).mul_right
  let φ : C_c(X, 𝕜) :=
    ⟨⟨fun y => starRingEnd 𝕜 (k y) * (ψ y : 𝕜),
      hkc.star.mul (RCLike.continuous_ofReal.comp ψ.continuous)⟩,
      (hks.comp_left (map_zero (starRingEnd 𝕜))).mul_right⟩
  have hφ (y : X) : φ y * h y = starRingEnd 𝕜 (k y) * k y := by
    simp only [φ, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, k, mul_assoc]
  have hk0 := hkc.eq_zero_of_integral_conj_mul_self_eq_zero
    (hkc.memLp_of_hasCompactSupport hks) (by simpa only [hφ] using h0 φ)
  have hψx : ψ x = 1 := hψ1 (Set.mem_singleton x)
  simpa only [k, hψx, RCLike.ofReal_one, one_mul, Pi.zero_apply] using congrFun hk0 x
