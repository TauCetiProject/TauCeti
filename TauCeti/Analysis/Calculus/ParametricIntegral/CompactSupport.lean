/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Parametric integrals with a fixed compact support

Let `X` be a topological space with a locally finite Borel measure `μ`, and let `D t x` be a real
function of a parameter `t` in an open set `U ⊆ ℝ` and of `x ∈ X`, vanishing for `x` outside a
fixed compact closed set `K`. If `D t` is continuous for every `t ∈ U` and the partial derivative
`∂ₜ D` exists and is jointly continuous on `U × X`, then `t ↦ ∫ D t x dμ` is differentiable on `U`
with derivative `∫ ∂ₜ D t x dμ`: on a compact neighbourhood of each parameter, `∂ₜ D` is bounded
on the compact set `K` and vanishes outside it, so it is dominated by an integrable function.
If moreover the second partial derivative exists and is jointly continuous, the integral is `C²`
on `U`.
-/

public section

open MeasureTheory Set Function Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] {U : Set ℝ} {K : Set X} {D D₁ D₂ : ℝ → X → ℝ}

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- If `D t x` vanishes for `x ∉ K` and every parameter in the open set `U`, so does its partial
derivative in `t`. -/
theorem hasDerivAt_eq_zero_of_forall_notMem (hU : IsOpen U)
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) {t : ℝ} (ht : t ∈ U) {x : X} (hx : x ∉ K) :
    D₁ t x = 0 := by
  refine (hderiv t ht x).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_)
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hsupp s hs x hx

/-- **Differentiation under the integral sign with a fixed compact support.** Let `D t x` vanish
for `x` outside a compact closed set `K` and `t` in an open set `U`, with `D t` continuous, and let
`D₁` be a jointly continuous partial derivative of `D` in `t` on `U × X`. Then the integral of
`D t` has derivative `∫ D₁ t x dμ` at every `t ∈ U`. -/
theorem hasDerivAt_integral_of_isCompact_support (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsClosed K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    HasDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds ht₀)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ ε).prod hK).exists_bound_of_continuousOn
    (hD₁.mono (prod_mono hεU (subset_univ K)))
  have hD₁t : Continuous (D₁ t₀) :=
    continuous_iff_continuousAt.2 fun x ↦ (hD₁.continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨ht₀, mem_univ x⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
  have hbound : Integrable (K.indicator fun _ ↦ C) μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t₀ hε)
    ?_ ?_ hD₁t.aestronglyMeasurable (ae_of_all _ fun x t ht ↦ ?_) hbound
    (ae_of_all _ fun x t ht ↦ hderiv t (hεU (ball_subset_closedBall ht)) x)).2
  · filter_upwards [hU.mem_nhds ht₀] with t ht
    exact (hD t ht).aestronglyMeasurable
  · exact (hD t₀ ht₀).integrable_of_hasCompactSupport
      (HasCompactSupport.intro' hK hKc (hsupp t₀ ht₀))
  · by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hC (t, x) ⟨ball_subset_closedBall ht, hx⟩
    · rw [indicator_of_notMem hx, hasDerivAt_eq_zero_of_forall_notMem hU hderiv hsupp
        (hεU (ball_subset_closedBall ht)) hx, norm_zero]

/-- The integral of a jointly continuous function with a fixed compact support is continuous in the
parameter. -/
theorem continuousOn_integral_of_isCompact_support (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsClosed K) (hD : ContinuousOn (uncurry D) (U ×ˢ univ))
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContinuousOn (fun t ↦ ∫ x, D t x ∂μ) U := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds ht₀)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ ε).prod hK).exists_bound_of_continuousOn
    (hD.mono (prod_mono hεU (subset_univ K)))
  have hDt : ∀ t ∈ U, Continuous (D t) := fun t ht ↦
    continuous_iff_continuousAt.2 fun x ↦ (hD.continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
  refine (continuousAt_of_dominated (bound := K.indicator fun _ ↦ C) ?_ ?_
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKc.measurableSet)
    (ae_of_all _ fun x ↦ ?_)).continuousWithinAt
  · filter_upwards [hU.mem_nhds ht₀] with t ht
    exact (hDt t ht).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds t₀ hε] with t ht
    refine ae_of_all _ fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hC (t, x) ⟨ht, hx⟩
    · rw [indicator_of_notMem hx, hsupp t (hεU ht) x hx, norm_zero]
  · exact (hD.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨ht₀, mem_univ x⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt

/-- **`C²` parametric integrals with a fixed compact support.** Let `D t x` vanish for `x` outside
a compact closed set `K` and `t` in an open set `U`, with `D t` continuous, and let `D₁` and `D₂`
be jointly continuous first and second partial derivatives of `D` in `t` on `U × X`. Then
`t ↦ ∫ D t x dμ` is `C²` on `U`. -/
theorem contDiffOn_two_integral_of_isCompact_support (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsClosed K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn ℝ 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  have hsupp₁ : ∀ t ∈ U, ∀ x ∉ K, D₁ t x = 0 := fun t ht x hx ↦
    hasDerivAt_eq_zero_of_forall_notMem hU hderiv₁ hsupp ht hx
  have hsupp₂ : ∀ t ∈ U, ∀ x ∉ K, D₂ t x = 0 := fun t ht x hx ↦
    hasDerivAt_eq_zero_of_forall_notMem hU hderiv₂ hsupp₁ ht hx
  have hD₁t : ∀ t ∈ U, Continuous (D₁ t) := fun t ht ↦
    continuous_iff_continuousAt.2 fun x ↦ (hD₁.continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
  have h₁ : ∀ t ∈ U, HasDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t x ∂μ) t := fun t ht ↦
    hasDerivAt_integral_of_isCompact_support hU hK hKc hD hD₁ hderiv₁ hsupp ht
  have h₂ : ∀ t ∈ U, HasDerivAt (fun t ↦ ∫ x, D₁ t x ∂μ) (∫ x, D₂ t x ∂μ) t := fun t ht ↦
    hasDerivAt_integral_of_isCompact_support hU hK hKc hD₁t hD₂ hderiv₂ hsupp₁ ht
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun t ht ↦ (h₁ t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  refine ContDiffOn.congr ?_ fun t ht ↦ (h₁ t ht).deriv
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun t ht ↦ (h₂ t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  refine ContDiffOn.congr ?_ fun t ht ↦ (h₂ t ht).deriv
  exact contDiffOn_zero.2 (continuousOn_integral_of_isCompact_support hU hK hKc hD₂ hsupp₂)

end TauCeti
