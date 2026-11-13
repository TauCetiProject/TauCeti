/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Calculus.Deriv.Const
public import TauCeti.Analysis.Calculus.FDeriv.Const
public import TauCeti.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Compactness.Normed

/-!
# Parametric integrals with a fixed compact support

Let `X` be a topological space with a Borel measure finite on compact sets, and let `D t x`
take values in a normed space over `𝕜 = ℝ` or `ℂ`. Suppose `D t` is continuous and vanishes
outside a fixed compact set for parameters in a normed space near `t₀`. A jointly continuous
parameter derivative can then be integrated to compute the derivative of the integral.

On an open parameter domain, the integral is `C¹` when the first parameter derivative is
jointly continuous, and `C²` when both the first and second are jointly continuous. The
second derivative is also computed by integration. A general successor step reduces higher
regularity to the regularity of the integral of the first parameter derivative.

The parameter-derivative integrability lemma also applies to the second derivative.
Directional evaluation of the first derivative integral uses `ContinuousLinearMap.integral_apply`;
the corresponding two-direction formula uses `ContinuousLinearMap.integral_apply_apply`.
-/

public section

open MeasureTheory Set Function Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace TauCeti

section Integrability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {U : Set H} {K : Set X} {D : H → X → E} {D₁ : X → H →L[𝕜] E}

-- Pin the standard extended norm for the iterated operator space used below.
/-- The standard extended norm on the space of curried continuous bilinear maps. -/
local instance instContinuousENormBilinear : ContinuousENorm (H →L[𝕜] H →L[𝕜] E) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid (H →L[𝕜] H →L[𝕜] E)
    inferInstance).toContinuousENorm

/-- A continuous parameter derivative of a family supported in a fixed compact set near the
parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasFDerivAt_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₁ : Continuous D₁)
    (hderiv : ∀ x, HasFDerivAt (D · x) (D₁ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  apply hD₁.integrable_of_support_subset_isCompact hK
  exact support_subset_iff'.2 fun x hx ↦ (hderiv x).eq_zero_of_eventually_const
    (Filter.Eventually.mono hU fun t ht ↦ hsupp t ht x hx)

/-- A continuous second parameter derivative of a family supported in a fixed compact set
near the parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasFDerivAt_of_hasFDerivAt_of_compact_support
    {D₁ : H → X → H →L[𝕜] E} {D₂ : X → H →L[𝕜] H →L[𝕜] E}
    {t₀ : H} (hU : U ∈ 𝓝 t₀) (hK : IsCompact K) (hD₂ : Continuous D₂)
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ x, HasFDerivAt (D₁ · x) (D₂ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₂ μ := by
  apply integrable_of_hasFDerivAt_of_compact_support
    (interior_mem_nhds.2 hU) hK hD₂ hderiv₂
  exact fun t ht x hx ↦
    (hderiv₁ t (interior_subset ht) x).eq_zero_of_eventually_const
      (Filter.Eventually.mono (isOpen_interior.mem_nhds ht)
        fun s hs ↦ hsupp s (interior_subset hs) x hx)

/-- A continuous scalar parameter derivative of a family supported in a fixed compact set
near the parameter is integrable, without a completeness assumption on the codomain. -/
theorem integrable_of_hasDerivAt_of_compact_support
    {U : Set 𝕜} {D : 𝕜 → X → E} {D₁ : X → E} {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₁ : Continuous D₁)
    (hderiv : ∀ x, HasDerivAt (D · x) (D₁ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) : Integrable D₁ μ := by
  apply hD₁.integrable_of_support_subset_isCompact hK
  exact support_subset_iff'.2 fun x hx ↦ (hderiv x).eq_zero_of_eventually_const
    (Filter.Eventually.mono hU fun t ht ↦ hsupp t ht x hx)

end Integrability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {U : Set H} {K : Set X} {D : H → X → E} {D₁ : H → X → H →L[𝕜] E}
  {D₂ : H → X → H →L[𝕜] H →L[𝕜] E}

/-- The integral of a continuous second parameter derivative can be evaluated in two
directions by integrating its pointwise evaluation, for a family with fixed compact support
near the parameter. -/
theorem integral_apply_apply_of_hasFDerivAt_of_compact_support
    {D₂ : X → H →L[𝕜] H →L[𝕜] E} {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD₂ : Continuous D₂)
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ x, HasFDerivAt (D₁ · x) (D₂ x) t₀)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) (v w : H) :
    (∫ x, D₂ x ∂μ) v w = ∫ x, D₂ x v w ∂μ :=
  ContinuousLinearMap.integral_apply_apply
    (integrable_of_hasFDerivAt_of_hasFDerivAt_of_compact_support
      hU hK hD₂ hderiv₁ hderiv₂ hsupp) v w

/-- **Differentiation under the integral sign with a fixed compact support.** Suppose `D t`
is continuous and vanishes outside a fixed compact set for parameters in a neighbourhood of
`t₀`. If its parameter derivative `D₁` is jointly continuous there, then the integral has
derivative equal to the integral of `D₁ t₀`. -/
theorem hasFDerivAt_integral_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasFDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  classical
  have ht₀ := mem_of_mem_nhds hU
  have ht₀i : t₀ ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  have hUi : IsOpen (interior U ×ˢ (univ : Set X)) := isOpen_interior.prod isOpen_univ
  have hD₁i := hD₁.mono (prod_mono interior_subset (Subset.refl univ))
  obtain ⟨C, hC⟩ := hK.exists_eventually_norm_le hUi
    (fun x _ ↦ hD₁i.continuousAt (hUi.mem_nhds ⟨ht₀i, mem_univ x⟩))
    (fun x _ ↦ ⟨ht₀i, mem_univ x⟩)
  have hS : {t | t ∈ interior U ∧ ∀ x ∈ K, ‖D₁ t x‖ ≤ C} ∈ 𝓝 t₀ := by
    filter_upwards [interior_mem_nhds.2 hU, hC] with t ht hCt
    exact ⟨ht, fun x hx ↦ (hCt x hx).2⟩
  have hzero (t : H) (ht : t ∈ interior U) (x : X) (hx : x ∉ K) : D₁ t x = 0 :=
    (hderiv t (interior_subset ht) x).eq_zero_of_eventually_const
      (Filter.Eventually.mono (isOpen_interior.mem_nhds ht)
        fun s hs ↦ hsupp s (interior_subset hs) x hx)
  have hmeas : ∀ t ∈ U, StronglyMeasurable (D t) := fun t ht ↦
    (hD t ht).stronglyMeasurable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hsupp t ht))
  have hD₁t : Continuous (D₁ t₀) := continuousOn_univ.1 (hD₁.uncurry_left t₀ ht₀)
  have hbound : Integrable ((toMeasurable μ K).indicator fun _ ↦ max C 0) μ := by
    refine (integrableOn_const ?_).integrable_indicator (measurableSet_toMeasurable μ K)
    simpa only [measure_toMeasurable] using hK.measure_ne_top
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le hS
    ?_ ?_ (integrable_of_hasFDerivAt_of_compact_support hU hK hD₁t
      (hderiv t₀ ht₀) hsupp).aestronglyMeasurable
    (ae_of_all _ fun x t ht ↦ ?_) hbound
    (ae_of_all _ fun x t ht ↦ hderiv t (interior_subset ht.1) x)
  · filter_upwards [hU] with t ht using (hmeas t ht).aestronglyMeasurable
  · exact (hD t₀ ht₀).integrable_of_support_subset_isCompact hK
      (support_subset_iff'.2 (hsupp t₀ ht₀))
  · by_cases hx : x ∈ K
    · rw [indicator_of_mem (subset_toMeasurable μ K hx)]
      exact (ht.2 x hx).trans (le_max_left _ _)
    · rw [hzero t ht.1 x hx, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ le_max_right _ _) _

/-- If the integral of the parameter derivative is `C^n`, then a family of continuous
functions with fixed compact support and jointly continuous parameter derivative has a
`C^(n+1)` integral. -/
theorem contDiffOn_succ_integral_of_compact_support {n : ℕ∞} (hU : IsOpen U)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0)
    (hI₁ : ContDiffOn 𝕜 n (fun t ↦ ∫ x, D₁ t x ∂μ) U) :
    ContDiffOn 𝕜 ((n : ℕ∞ω) + 1) (fun t ↦ ∫ x, D t x ∂μ) U := by
  have h₁ := fun (t : H) (ht : t ∈ U) ↦
    hasFDerivAt_integral_of_compact_support (μ := μ) (hU.mem_nhds ht) hK hD hD₁ hderiv hsupp
  exact (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
    ⟨fun t ht ↦ (h₁ t ht).differentiableAt.differentiableWithinAt, by simp,
      hI₁.congr fun t ht ↦ (h₁ t ht).fderiv⟩

/-- A family of continuous functions with fixed compact support and jointly continuous
parameter derivative has a `C¹` integral on its open parameter domain. -/
theorem contDiffOn_one_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 1 (fun t ↦ ∫ x, D t x ∂μ) U := by
  apply contDiffOn_succ_integral_of_compact_support (n := 0) hU hK hD hD₁ hderiv hsupp
  refine contDiffOn_zero.2 (continuousOn_integral_of_compact_support hK hD₁ ?_)
  exact fun t x ht hx ↦
    (hderiv t ht x).eq_zero_of_eventually_const
      (Filter.Eventually.mono (hU.mem_nhds ht) fun s hs ↦ hsupp s hs x hx)

/-- **Second differentiation under the integral sign with a fixed compact support.**
For continuous `D t` with fixed compact support near `t₀`, jointly continuous first and second
parameter derivatives can both be integrated to compute the derivative of the Fréchet
derivative of the integral. -/
theorem hasFDerivAt_fderiv_integral_of_compact_support {t₀ : H} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasFDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasFDerivAt (fderiv 𝕜 fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₂ t₀ x ∂μ) t₀ := by
  have hUi : interior U ∈ 𝓝 t₀ := interior_mem_nhds.2 hU
  have hsupp₁ : ∀ t ∈ interior U, ∀ x ∉ K, D₁ t x = 0 := fun t ht x hx ↦
    (hderiv₁ t (interior_subset ht) x).eq_zero_of_eventually_const
      (Filter.Eventually.mono (isOpen_interior.mem_nhds ht)
        fun s hs ↦ hsupp s (interior_subset hs) x hx)
  have h₂ := hasFDerivAt_integral_of_compact_support (μ := μ) hUi hK
    (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t (interior_subset ht)))
    (hD₂.mono (prod_mono interior_subset (Subset.refl univ)))
    (fun t ht ↦ hderiv₂ t (interior_subset ht)) hsupp₁
  refine h₂.congr_of_eventuallyEq ?_
  filter_upwards [hUi] with t ht
  exact (hasFDerivAt_integral_of_compact_support
    (mem_interior_iff_mem_nhds.1 ht) hK hD hD₁ hderiv₁ hsupp).fderiv

/-- **`C²` parametric integrals with a fixed compact support.** A family of continuous
functions with fixed compact support and jointly continuous first and second parameter
derivatives has a `C²` integral on its open parameter domain. -/
theorem contDiffOn_two_integral_of_compact_support (hU : IsOpen U) (hK : IsCompact K)
    (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasFDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasFDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  have hsupp₁ : ∀ t ∈ U, ∀ x ∉ K, D₁ t x = 0 := fun t ht x hx ↦
    (hderiv₁ t ht x).eq_zero_of_eventually_const
      (Filter.Eventually.mono (hU.mem_nhds ht) fun s hs ↦ hsupp s hs x hx)
  exact contDiffOn_succ_integral_of_compact_support (n := 1) hU hK hD hD₁ hderiv₁ hsupp
    (contDiffOn_one_integral_of_compact_support hU hK
      (fun t ht ↦ continuousOn_univ.1 (hD₁.uncurry_left t ht)) hD₂ hderiv₂ hsupp₁)

section Scalar

variable {U : Set 𝕜} {D D₁ D₂ : 𝕜 → X → E}

/-- A scalar parameter derivative of a continuous family with fixed compact support and a
jointly continuous parameter derivative can be integrated to differentiate the integral. -/
theorem hasDerivAt_integral_of_compact_support {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivAt (fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₁ t₀ x ∂μ) t₀ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  have h := hasFDerivAt_integral_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) hU hK hD
    (e.continuous.comp_continuousOn hD₁) (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp
  rw [e.integral_comp_comm (D₁ t₀)] at h
  exact hasDerivAt_iff_hasFDerivAt.2 h

/-- If the integral of the scalar parameter derivative is `C^n`, then a continuous family
with fixed compact support and jointly continuous derivative has a `C^(n+1)` integral. -/
theorem contDiffOn_succ_integral_of_hasDerivAt_of_compact_support {n : ℕ∞}
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0)
    (hI₁ : ContDiffOn 𝕜 n (fun t ↦ ∫ x, D₁ t x ∂μ) U) :
    ContDiffOn 𝕜 ((n : ℕ∞ω) + 1) (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  apply contDiffOn_succ_integral_of_compact_support (D₁ := fun t x ↦ e (D₁ t x))
    hU hK hD (e.continuous.comp_continuousOn hD₁)
    (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp
  simp_rw [e.integral_comp_comm]
  exact e.contDiff.comp_contDiffOn hI₁

/-- A continuous family with fixed compact support and jointly continuous scalar parameter
derivative has a `C¹` integral on its open parameter domain. -/
theorem contDiffOn_one_integral_of_hasDerivAt_of_compact_support
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ))
    (hderiv : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 1 (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  exact contDiffOn_one_integral_of_compact_support (D₁ := fun t x ↦ e (D₁ t x))
    hU hK hD (e.continuous.comp_continuousOn hD₁)
    (fun t ht x ↦ (hderiv t ht x).hasFDerivAt) hsupp

/-- A continuous family with fixed compact support and jointly continuous first and second
scalar parameter derivatives has a `C²` integral on its open parameter domain. -/
theorem contDiffOn_two_integral_of_hasDerivAt_of_compact_support
    (hU : IsOpen U) (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    ContDiffOn 𝕜 2 (fun t ↦ ∫ x, D t x ∂μ) U := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  let e₁ := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
  exact contDiffOn_two_integral_of_compact_support
    (D₁ := fun t x ↦ e (D₁ t x)) (D₂ := fun t x ↦ e₁ (e (D₂ t x))) hU hK hD
    (e.continuous.comp_continuousOn hD₁)
    (e₁.continuous.comp_continuousOn (e.continuous.comp_continuousOn hD₂))
    (fun t ht x ↦ (hderiv₁ t ht x).hasFDerivAt)
    (fun t ht x ↦ (e.hasFDerivAt.comp_hasDerivAt t (hderiv₂ t ht x)).hasFDerivAt) hsupp

/-- With a scalar parameter, jointly continuous first and second derivatives of a continuous
family with fixed compact support near `t₀` can both be integrated to compute the derivative
of the derivative of the integral. -/
theorem hasDerivAt_deriv_integral_of_compact_support {t₀ : 𝕜} (hU : U ∈ 𝓝 t₀)
    (hK : IsCompact K) (hD : ∀ t ∈ U, Continuous (D t))
    (hD₁ : ContinuousOn (uncurry D₁) (U ×ˢ univ)) (hD₂ : ContinuousOn (uncurry D₂) (U ×ˢ univ))
    (hderiv₁ : ∀ t ∈ U, ∀ x, HasDerivAt (D · x) (D₁ t x) t)
    (hderiv₂ : ∀ t ∈ U, ∀ x, HasDerivAt (D₁ · x) (D₂ t x) t)
    (hsupp : ∀ t ∈ U, ∀ x ∉ K, D t x = 0) :
    HasDerivAt (deriv fun t ↦ ∫ x, D t x ∂μ) (∫ x, D₂ t₀ x ∂μ) t₀ := by
  let e := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := E)
  let e₁ := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
  have h := hasFDerivAt_fderiv_integral_of_compact_support (μ := μ)
    (D₁ := fun t x ↦ e (D₁ t x)) (D₂ := fun t x ↦ e₁ (e (D₂ t x))) hU hK hD
    (e.continuous.comp_continuousOn hD₁)
    (e₁.continuous.comp_continuousOn (e.continuous.comp_continuousOn hD₂))
    (fun t ht x ↦ (hderiv₁ t ht x).hasFDerivAt)
    (fun t ht x ↦ (e.hasFDerivAt.comp_hasDerivAt t (hderiv₂ t ht x)).hasFDerivAt) hsupp
  rw [ContinuousLinearEquiv.integral_comp_comm (𝕜 := 𝕜) (E := 𝕜 →L[𝕜] E)
    (F := 𝕜 →L[𝕜] 𝕜 →L[𝕜] E) e₁, e.integral_comp_comm] at h
  have h' := (e.symm.hasFDerivAt.comp t₀ h).hasDerivAt
  simpa [e, e₁, comp_def, fderiv_apply_one_eq_deriv] using h'

end Scalar

end TauCeti
