/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Parametric integrals with a fixed compact support

Let `X` be a topological space with a Borel measure finite on compact sets, and let `D t x`
take values in a normed space over `𝕜 = ℝ` or `ℂ`. Suppose `D t` is continuous and vanishes
outside a fixed compact set for parameters near `t₀`. A jointly continuous parameter
derivative can then be integrated to compute the derivative of the integral.

On an open parameter domain, the integral is `C¹` when the first parameter derivative is
jointly continuous, and `C²` when both the first and second are jointly continuous. The
second derivative is also computed by integration. A general successor step reduces higher
regularity to the regularity of the integral of the first parameter derivative.
-/

public section

open MeasureTheory Set Function Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {K : Set X} {D D₁ D₂ : 𝕜 → X → E}

/-- **Differentiation under the integral sign with a fixed compact support.** Suppose `D t`
is continuous and vanishes outside a fixed compact set for parameters in a neighbourhood of
`t₀`. If its parameter derivative `D₁` is jointly continuous there, then the integral has
derivative equal to the integral of `D₁ t₀`. -/
theorem hasDerivAt_integral_of_compact_support {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  classical
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  have ht₀ := mem_of_mem_nhds hU
  have hzero (t : 𝕜) (ht : t ∈ ball t₀ ε) (x : X) (hx : x ∉ K) : D₁ t x = 0 := by
    refine (hderiv t (hεU (ball_subset_closedBall ht)) x).unique
      ((hasDerivAt_const t (0 : E)).congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_ball.mem_nhds ht] with s hs
    exact hsupp s (hεU (ball_subset_closedBall hs)) x hx
  have hmeas : ∀ t ∈ U, StronglyMeasurable (D t) := fun t ht ↦
    (hD t ht).stronglyMeasurable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hsupp t ht))
  have hD₁t : Continuous (D₁ t₀) := continuousOn_univ.1 (hD₁.uncurry_left t₀ ht₀)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ ε).prod hK).exists_bound_of_continuousOn
    (hD₁.mono (prod_mono hεU (subset_univ K)))
  have hbound : Integrable ((toMeasurable μ K).indicator fun _ ↦ max C 0) μ := by
    refine (integrableOn_const ?_).integrable_indicator (measurableSet_toMeasurable μ K)
    simpa only [measure_toMeasurable] using hK.measure_ne_top
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t₀ hε)
    ?_ ?_ (hD₁t.stronglyMeasurable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hzero t₀ (mem_ball_self hε)))).aestronglyMeasurable
    (ae_of_all _ fun x t ht ↦ ?_) hbound
    (ae_of_all _ fun x t ht ↦ hderiv t (hεU (ball_subset_closedBall ht)) x)).2
  · filter_upwards [hU] with t ht using (hmeas t ht).aestronglyMeasurable
  · exact ((hD t₀ ht₀).continuousOn.integrableOn_of_subset_isCompact hK
      (hmeas t₀ ht₀).measurableSet_support (support_subset_iff'.2 (hsupp t₀ ht₀))
      ((measure_mono (support_subset_iff'.2 (hsupp t₀ ht₀))).trans_lt
        hK.measure_lt_top).ne).integrable_of_forall_notMem_eq_zero
      (fun x hx ↦ notMem_support.mp hx)
  · by_cases hx : x ∈ K
    · rw [indicator_of_mem (subset_toMeasurable μ K hx)]
      exact (hC (t, x) ⟨ball_subset_closedBall ht, hx⟩).trans (le_max_left _ _)
    · rw [hzero t ht x hx, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ le_max_right _ _) _

/-- If the integral of the parameter derivative is `C^n`, then a family of continuous
functions with fixed compact support and jointly continuous parameter derivative has a
`C^(n+1)` integral. -/
theorem contDiffOn_succ_integral_of_compact_support {n : ℕ∞} (hU : IsOpen U)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0)
    (hI₁ : ContDiffOn 𝕜 n (fun t ↦ ∫ x, D₁ t x ∂μ) U) :
    ContDiffOn 𝕜 ((n : ℕ∞ω) + 1) (fun t ↦ ∫ x, D t x ∂μ) U := by
  have h₁ := fun (t : 𝕜) (ht : t ∈ U) ↦
    hasDerivAt_integral_of_compact_support (μ := μ) (hU.mem_nhds ht) hK hD hD₁ hderiv hsupp
  exact (contDiffOn_succ_iff_deriv_of_isOpen hU).2
    ⟨fun t ht ↦ (h₁ t ht).differentiableAt.differentiableWithinAt, by simp,
      hI₁.congr fun t ht ↦ (h₁ t ht).deriv⟩

/-- A family of continuous functions with fixed compact support and jointly continuous
parameter derivative has a `C¹` integral on its open parameter domain. -/
theorem contDiffOn_one_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 1 (fun t ↦ ∫ x, D t x ∂μ) U := by
  apply contDiffOn_succ_integral_of_compact_support (n := 0) hU hK hD hD₁ hderiv hsupp
  refine contDiffOn_zero.2 (continuousOn_integral_of_compact_support hK hD₁ ?_)
  intro t x ht hx
  refine (hderiv t ht x).unique ((hasDerivAt_const t (0 : E)).congr_of_eventuallyEq ?_)
  filter_upwards [hU.mem_nhds ht] with s hs using hsupp s hs x hx

/-- **Second differentiation under the integral sign with a fixed compact support.**
For continuous `D t` with fixed compact support on an open parameter domain, jointly
continuous first and second parameter derivatives can both be integrated to compute the
derivative of the derivative of the integral. -/
theorem hasDerivAt_deriv_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) {t₀ : 𝕜} (ht₀ : t₀ ∈ U) :
    HasDerivAt (deriv fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₂ t₀ x ∂μ) t₀ := by
  have hsupp₁ : ∀ t ∈ U, ∀ x ∉ K, D₁ t x = 0 := by
    intro t ht x hx
    refine (hderiv₁ t ht x).unique ((hasDerivAt_const t (0 : E)).congr_of_eventuallyEq ?_)
    filter_upwards [hU.mem_nhds ht] with s hs using hsupp s hs x hx
  have h₂ := hasDerivAt_integral_of_compact_support (μ := μ) (hU.mem_nhds ht₀) hK
    (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t ht)) hD₂ hderiv₂ hsupp₁
  refine h₂.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds ht₀] with t ht
  exact (hasDerivAt_integral_of_compact_support (hU.mem_nhds ht) hK hD hD₁ hderiv₁ hsupp).deriv

/-- **`C²` parametric integrals with a fixed compact support.** A family of continuous
functions with fixed compact support and jointly continuous first and second parameter
derivatives has a `C²` integral on its open parameter domain. -/
theorem contDiffOn_two_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  have hsupp₁ : ∀ t ∈ U, ∀ x ∉ K, D₁ t x = 0 := by
    intro t ht x hx
    refine (hderiv₁ t ht x).unique ((hasDerivAt_const t (0 : E)).congr_of_eventuallyEq ?_)
    filter_upwards [hU.mem_nhds ht] with s hs using hsupp s hs x hx
  exact contDiffOn_succ_integral_of_compact_support (n := 1) hU hK hD hD₁ hderiv₁ hsupp
    (contDiffOn_one_integral_of_compact_support hU hK
      (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t ht)) hD₂ hderiv₂ hsupp₁)

end TauCeti
